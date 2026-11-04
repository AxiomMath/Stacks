module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.BaseChangeExactSequence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Surjectivity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaDiagram
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Henselization
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksFrontier.RingTheory.IntegralClosure.Pi
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctorComplete
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local exact sequence of a normal local domain

Let `A` be a normal local domain with fraction field `K`, let `A^sh` be a strict henselization of
`A` and `K^sh` its fraction field. The spectra of all four rings are connected, the inclusions
`A ⊆ K`, `K ⊆ K^sh` induce morphisms of spectra, and a geometric point `x` of `Spec K^sh` is a
base point for all of them. The sequence

```
π₁(Spec K^sh, x) → π₁(Spec K, x) → π₁(Spec A, x) → 1
```

is then exact: the fundamental group of the generic point surjects onto the fundamental group of
the spectrum, and its kernel is the smallest closed normal subgroup containing the image of the
fundamental group of the generic point of the strict henselization.

## Main definitions

* `AlgebraicGeometry.finiteEtaleOverSpec` — the finite étale cover of `Spec R` attached to a
  finite étale `R`-algebra; `AlgebraicGeometry.splitFiniteEtaleOverSpec` is the split one of a
  given degree.
* `AlgebraicGeometry.specIsoOfAlgEquiv` and `AlgebraicGeometry.algEquivOfSpecIso` — the two
  directions of the identification of isomorphisms of `R`-algebras with isomorphisms of their
  spectra over `Spec R`.
* `AlgebraicGeometry.integralClosurePiFractionEquiv` — the integral closure of a normal domain in
  a finite product of copies of its fraction field.

## Main results

* `AlgebraicGeometry.isAlgebraic_of_indEtale` — an ind-étale algebra over a domain is algebraic
  over it; `AlgebraicGeometry.isAlgebraic_of_isHenselization` is the case of a henselization.
* `AlgebraicGeometry.isDomain_and_isIntegrallyClosed_of_isHenselization` and
  `AlgebraicGeometry.isSepClosed_residueField_of_isHenselization` — a strict henselization of a
  normal local domain is a normal local domain with separably closed residue field.
* `AlgebraicGeometry.isFiniteCoproductOfTerminal_of_iso_split` and
  `AlgebraicGeometry.exists_algEquiv_pi_of_isFiniteCoproductOfTerminal` — over an affine base, a
  finite étale cover is a finite coproduct of copies of the base exactly when its algebra of
  global sections is a finite product of copies of the base ring.
* `AlgebraicGeometry.isFiniteCoproductOfTerminal_of_henselian_isSepClosed` — every finite étale
  cover of a strictly henselian local spectrum is such a coproduct.
* `AlgebraicGeometry.module_finite_and_etale_integralClosure_of_split_generic_of_isHenselization`
  — the integral closure of `A` in an algebra over `K` that splits over `K^sh` is finite étale
  over `A`.
* `AlgebraicGeometry.exists_section_of_section_fractionField` and
  `AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_fractionField` — a section over the
  generic point of a normal domain extends, so base change there is fully faithful.
* `AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_fractionField_of_isHenselization` —
  the exact sequence itself.

## Where the Galois-category property comes from

The exact sequence needs the finite étale covers of each of the four spectra to be a Galois
category at the relevant geometric point, which is Stacks Tag 0BNB. That is
`AlgebraicGeometry.finiteEtaleFiberFunctor_isGaloisCategory`, proved for every connected scheme
in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GaloisCategories/FiberFunctorComplete.lean`;
the four spectra are spectra of local rings, hence connected
(`AlgebraicGeometry.connectedSpace_spec_of_isLocalRing`), so the instance applies to each of
them and the exact sequence carries no hypothesis beyond its own. The auxiliary results below
still take the Galois-category property as an instance hypothesis
`Stacks.FundamentalGroup.IsGaloisCategory (finiteEtaleFiberFunctor y)` at the point in question,
as in `StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleEquivalence.lean`; those
hypotheses are now discharged by instance search wherever the base is known to be connected.

## Implementation notes

The strict henselization is `IsLocalRing.IsHenselization A κsep Ash` for `κsep` a separable
algebraic closure of the residue field of `A`, which is the repository's predicate for `A^sh`
(Definition 04GQ). Its three ring-theoretic inputs are already on main: it is normal by Tag 06DI
(`isNormalDomain_tfae_henselization_strictHenselization`), faithfully flat by
`IsLocalRing.IsHenselization.faithfullyFlat`, and base change along it commutes with integral
closure by Tag 0CBF (`AlgebraicGeometry.toIntegralClosure_bijective_of_isHenselization`). Only
algebraicity of `A ⊆ A^sh` is proved here, by factoring an element through an étale stage of the
ind-étale presentation.

The two directions of the essential-image criterion of Stacks 0BS9 are the two halves of the
proof. For the forward direction a cover pulled back from `Spec A` becomes split over the
strictly henselian `Spec A^sh`, and splitness is preserved by the exact base change to
`Spec K^sh`. For the converse a cover `V` of `Spec K` whose pullback to `Spec K^sh` is split has
a finite étale algebra of global sections `L`, the integral closure of `A` in `L` is finite étale
over `A` because it is so after the faithfully flat base change to `A^sh`, and `V` is the
generic fibre of its spectrum because `L` is a localization of that integral closure.

## References

* [Stacks Project, Tag 0BSM](https://stacks.math.columbia.edu/tag/0BSM)
* [Stacks Project, Tag 0BS9](https://stacks.math.columbia.edu/tag/0BS9)
* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI)
* [Stacks Project, Tag 0CBF](https://stacks.math.columbia.edu/tag/0CBF)
* [Stacks Project, Tag 0BNB](https://stacks.math.columbia.edu/tag/0BNB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.FundamentalGroup
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Algebraicity of an ind-étale algebra over a domain -/

/-- An étale algebra over a domain is algebraic over it: after base change to the fraction field
it is quasi-finite, hence finite, and the algebra injects into that base change. -/
theorem isAlgebraic_of_etale (R K B : Type u) [CommRing R] [IsDomain R] [Field K] [CommRing B]
    [Algebra R K] [IsFractionRing R K] [Algebra R B] [Algebra.Etale R B] :
    Algebra.IsAlgebraic R B := by
  have : Module.Finite K (K ⊗[R] B) := Module.Finite.of_quasiFinite
  have : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  have : Algebra.IsAlgebraic R (K ⊗[R] B) := Algebra.IsAlgebraic.trans R K _
  exact Algebra.IsAlgebraic.of_injective
    (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

/-- **An ind-étale algebra over a domain is algebraic over it.** An element of the algebra is the
image of a polynomial under a map out of `R[X]`, which is finitely presented, so that map factors
through an étale stage of the ind-étale presentation; étale algebras over a domain are
algebraic. -/
theorem isAlgebraic_of_indEtale (R K B : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [CommRing B] [Algebra R B]
    (h : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R B)) :
    Algebra.IsAlgebraic R B := by
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨J, _, _, pres, hstage⟩ := h
  let P : CommAlgCat R := CommAlgCat.of R (Polynomial R)
  let a : P ⟶ CommAlgCat.of R B := CommAlgCat.ofHom (Polynomial.aeval b)
  let _reg : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  have : IsFinitelyPresentable.{u} P := by
    refine (isCardinalPresentable_iff_of_isEquivalence P Cardinal.aleph0
      (commAlgCatEquivUnder (CommRingCat.of R)).functor).mp ?_
    apply CommRingCat.isFinitelyPresentable_under
    show (algebraMap R (Polynomial R)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  obtain ⟨j, ψ, hψ⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit a
  have hb : (pres.ι.app j).hom (ψ.hom Polynomial.X) = b := by
    show (CommAlgCat.Hom.hom (ψ ≫ pres.ι.app j)) Polynomial.X = b
    rw [hψ]
    exact Polynomial.aeval_X b
  have : Algebra.Etale R (pres.diag.obj j) := hstage j
  have : Algebra.IsAlgebraic R (pres.diag.obj j) := isAlgebraic_of_etale R K _
  exact hb ▸ (Algebra.IsAlgebraic.isAlgebraic (ψ.hom Polynomial.X)).algHom (pres.ι.app j).hom

/-! ### The ring-theoretic properties of a strict henselization -/

variable (A Ash : Type u) [CommRing A] [IsLocalRing A] [CommRing Ash] [IsLocalRing Ash]
  [Algebra A Ash] (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]

/-- **A henselization of a local domain is algebraic over it**: it is ind-étale, and an ind-étale
algebra over a domain is algebraic. -/
theorem isAlgebraic_of_isHenselization (K : Type u) [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [IsHenselization A κsep Ash] :
    Algebra.IsAlgebraic A Ash :=
  isAlgebraic_of_indEtale A K Ash
    (StacksDraft.indEtale_iff.mp (StacksDraft.indEtale_of_isHenselization κsep (Rh := Ash)))

/-- **A strict henselization of a normal local domain is a normal local domain.** This is the
equivalence of Stacks Tag 06DI between normality of a local ring and of its strict
henselization, applied to the henselization that Tag 04GN provides. -/
@[ega "IV 18.8.12" "(i)", ega "IV 7.5.3" "(vi), special case"]
theorem isDomain_and_isIntegrallyClosed_of_isHenselization
    [IsDomain A] [IsIntegrallyClosed A] [IsSepClosure (ResidueField A) κsep]
    [IsHenselization A κsep Ash] :
    IsDomain Ash ∧ IsIntegrallyClosed Ash := by
  obtain ⟨Ah, _, _, _, _⟩ := IsLocalRing.exists_isHenselization_residueField A
  refine ((isNormalDomain_tfae_henselization_strictHenselization A Ah Ash κsep).out 1 3).mp ?_
  exact ⟨‹IsDomain A›, ‹IsIntegrallyClosed A›⟩

/-- **The residue field of a strict henselization is separably closed**: it is the prescribed
separable algebraic closure of the residue field of the base. -/
theorem isSepClosed_residueField_of_isHenselization
    [IsSepClosure (ResidueField A) κsep] [IsHenselization A κsep Ash] :
    IsSepClosed (ResidueField Ash) := by
  obtain ⟨alg, -, hsep, -⟩ :=
    IsHenselization.exists_residueFieldAlgebra (R := A) (L := κsep) (Rh := Ash)
  let := alg
  exact (hsep inferInstance).sep_closed

/-! ### Split finite étale covers of an affine scheme -/

section Split

variable (R : Type u) [CommRing R]

/-- The finite étale cover of `Spec R` attached to a finite étale `R`-algebra, namely its
spectrum with the morphism induced by the structure map. -/
def finiteEtaleOverSpec (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S]
    [Algebra.Etale R S] : FiniteEtaleOver (Spec (.of R)) :=
  MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    ⟨by
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr inferInstance,
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)⟩

/-- The split finite étale cover of `Spec R` of degree `n`: the spectrum of the ring of functions
from an `n`-element type to `R`. -/
def splitFiniteEtaleOverSpec (n : ℕ) : FiniteEtaleOver (Spec (.of R)) :=
  finiteEtaleOverSpec R (ULift.{u} (Fin n) → R)

/-- The `i`-th projection of the split finite étale cover of degree `n`, as a morphism from the
terminal cover. -/
def splitFiniteEtaleOverSpecLeg (n : ℕ) (i : ULift.{u} (Fin n)) :
    finiteEtaleOverTerminal (Spec (.of R)) ⟶ splitFiniteEtaleOverSpec R n :=
  MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ULift.{u} (Fin n) ↦ R) i))) (by
      change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ULift.{u} (Fin n) ↦ R) i)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ULift.{u} (Fin n) → R))) = 𝟙 _
      rw [← Spec.map_comp, ← Spec.map_id]
      apply Spec.map_inj.mpr
      apply CommRingCat.hom_ext
      ext x
      simp)

/-- **The split finite étale cover of degree `n` is the coproduct of `n` copies of the terminal
cover.** The projections induce the canonical morphism from the disjoint union of `n` copies of
`Spec R`, which is an isomorphism; so they are a colimit cofan of schemes, hence a colimit cofan
of finite étale covers, those colimits being computed in schemes. -/
def isColimit_cofanMk_splitFiniteEtaleOverSpec (n : ℕ) :
    IsColimit (Cofan.mk (splitFiniteEtaleOverSpec R n) (splitFiniteEtaleOverSpecLeg R n)) := by
  let D := splitFiniteEtaleOverSpec R n
  let p : ∀ i : ULift.{u} (Fin n), (finiteEtaleOverTerminal (Spec (.of R))).left ⟶ D.left :=
    fun i ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ULift.{u} (Fin n) ↦ R) i))
  have hdesc : Sigma.desc p = sigmaSpec (fun _ : ULift.{u} (Fin n) ↦ CommRingCat.of R) := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ULift.{u} (Fin n) ↦ R) i)) =
      Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of R)) i ≫
        sigmaSpec (fun _ : ULift.{u} (Fin n) ↦ CommRingCat.of R)
    rw [ι_sigmaSpec]
  have hdescIso : IsIso (Sigma.desc p) := by
    rw [hdesc]
    change IsIso (sigmaSpec (fun _ : ULift.{u} (Fin n) ↦ CommRingCat.of R))
    infer_instance
  have hScheme : IsColimit (Cofan.mk D.left p) := by
    letI : IsIso (Sigma.desc (Cofan.mk D.left p).inj) := hdescIso
    exact Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk D.left p)
  exact isColimitOfReflects (MorphismProperty.Over.forget finiteEtale ⊤ (Spec (.of R)))
    (isColimitOfReflects (CategoryTheory.Over.forget (Spec (.of R))) hScheme)

/-- **A finite étale cover of `Spec R` isomorphic over the base to a split one is a finite
coproduct of copies of the base.** -/
theorem isFiniteCoproductOfTerminal_of_iso_split (Y : FiniteEtaleOver (Spec (.of R))) (n : ℕ)
    (e : Y.left ≅ Spec (.of (ULift.{u} (Fin n) → R)))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (ULift.{u} (Fin n) → R))) = Y.hom) :
    IsFiniteCoproductOfTerminal Y :=
  isFiniteCoproductOfTerminal_of_iso (MorphismProperty.Over.isoMk e he).symm
    ⟨n, fun _ ↦ finiteEtaleOverTerminal (Spec (.of R)),
      fun i ↦ splitFiniteEtaleOverSpecLeg R n (ULift.up i),
      fun _ ↦ ⟨MorphismProperty.Over.mkIdTerminal finiteEtale (Spec (.of R))⟩,
      ⟨(Cofan.isColimitEquivOfEquiv Equiv.ulift.symm _)
        (isColimit_cofanMk_splitFiniteEtaleOverSpec R n)⟩⟩

/-- The isomorphism of spectra attached to an isomorphism of algebras. -/
def specIsoOfAlgEquiv {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) : Spec (.of S) ≅ Spec (.of T) :=
  Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op

/-- The isomorphism of spectra attached to an isomorphism of algebras is one over the base. -/
theorem specIsoOfAlgEquiv_hom_comp {S T : Type u} [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] (e : S ≃ₐ[R] T) :
    (specIsoOfAlgEquiv R e).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  show Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  apply Spec.map_inj.mpr
  apply CommRingCat.hom_ext
  ext r
  exact e.symm.commutes r

/-- An isomorphism of spectra over `Spec R` comes from an isomorphism of `R`-algebras, because
`Spec` is fully faithful. -/
def algEquivOfSpecIso (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (e : Spec (.of S) ≅ Spec (.of T))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S))) : T ≃ₐ[R] S := by
  let eR : CommRingCat.of T ≅ CommRingCat.of S := (Spec.fullyFaithful.preimageIso e).unop
  have h : CommRingCat.ofHom (algebraMap R T) ≫ eR.hom = CommRingCat.ofHom (algebraMap R S) :=
    Spec.map_injective (by simpa [Spec.map_comp, eR] using he)
  exact AlgEquiv.ofRingEquiv (f := eR.commRingCatIsoToRingEquiv)
    fun r ↦ congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of S ↦ f r) h

/-- **A finite étale cover of `Spec R` which is a finite coproduct of copies of the base has a
split algebra of global sections.** The cover is the coproduct of `n` copies of the terminal
cover, hence isomorphic over `Spec R` to the split cover of degree `n`; `Spec` is fully faithful,
so that isomorphism comes from an isomorphism of `R`-algebras. -/
theorem exists_algEquiv_pi_sections_of_isFiniteCoproductOfTerminal
    (Y : FiniteEtaleOver (Spec (.of R))) [IsAffine Y.left]
    (hY : IsFiniteCoproductOfTerminal Y) :
    ∃ n : ℕ, Nonempty (letI : Algebra R Γ(Y.left, ⊤) :=
      (Spec.preimage (Y.left.isoSpec.inv ≫ Y.hom)).hom.toAlgebra
      Γ(Y.left, ⊤) ≃ₐ[R] (Fin n → R)) := by
  classical
  obtain ⟨n, A₀, f₀, hterm, ⟨hc₀⟩⟩ := hY
  let T := finiteEtaleOverTerminal (Spec (.of R))
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal finiteEtale (Spec (.of R))
  let e : ∀ i : Fin n, A₀ i ≅ T := fun i ↦ (Classical.choice (hterm i)).uniqueUpToIso hT
  let f : ∀ _ : Fin n, T ⟶ Y := fun i ↦ (e i).inv ≫ f₀ i
  have hfac (s : Cofan fun _ : Fin n ↦ T) (i : Fin n) :
      f₀ i ≫ hc₀.desc (Cofan.mk s.pt fun j ↦ (e j).hom ≫ s.inj j) = (e i).hom ≫ s.inj i :=
    Cofan.IsColimit.fac hc₀ _ i
  have hc : IsColimit (Cofan.mk Y f) := by
    refine Cofan.IsColimit.mk _ (fun s ↦ hc₀.desc
      (Cofan.mk s.pt (fun i ↦ (e i).hom ≫ s.inj i))) ?_ ?_
    · intro s i
      show (e i).inv ≫ f₀ i ≫ hc₀.desc (Cofan.mk s.pt (fun j ↦ (e j).hom ≫ s.inj j)) = s.inj i
      rw [hfac s i, Iso.inv_hom_id_assoc]
    · intro s m hm
      apply Cofan.IsColimit.hom_ext hc₀
      intro i
      calc f₀ i ≫ m = (e i).hom ≫ ((e i).inv ≫ f₀ i) ≫ m := by simp
        _ = (e i).hom ≫ s.inj i := congrArg ((e i).hom ≫ ·) (hm i)
        _ = f₀ i ≫ hc₀.desc (Cofan.mk s.pt (fun j ↦ (e j).hom ≫ s.inj j)) := (hfac s i).symm
  have hYlift : IsColimit (Cofan.mk Y (fun i : ULift.{u} (Fin n) ↦ f i.down)) :=
    (Cofan.isColimitEquivOfEquiv Equiv.ulift _) hc
  let eY : Y ≅ splitFiniteEtaleOverSpec R n :=
    hYlift.coconePointUniqueUpToIso (isColimit_cofanMk_splitFiniteEtaleOverSpec R n)
  let eScheme : Y.left ≅ Spec (.of (ULift.{u} (Fin n) → R)) :=
    (CategoryTheory.Over.forget (Spec (.of R))).mapIso
      ((MorphismProperty.Over.forget finiteEtale ⊤ (Spec (.of R))).mapIso eY)
  let eSpec : Spec (.of Γ(Y.left, ⊤)) ≅ Spec (.of (ULift.{u} (Fin n) → R)) :=
    Y.left.isoSpec.symm ≪≫ eScheme
  let : Algebra R Γ(Y.left, ⊤) := (Spec.preimage (Y.left.isoSpec.inv ≫ Y.hom)).hom.toAlgebra
  have hSpecBase : eSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (ULift.{u} (Fin n) → R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y.left, ⊤))) := by
    have hbase : eScheme.hom ≫ (splitFiniteEtaleOverSpec R n).hom = Y.hom := eY.hom.w
    have h1 : eSpec.hom ≫ (splitFiniteEtaleOverSpec R n).hom =
        Y.left.isoSpec.inv ≫ Y.hom := by
      show (Y.left.isoSpec.inv ≫ eScheme.hom) ≫ (splitFiniteEtaleOverSpec R n).hom = _
      rw [← hbase]
      exact Category.assoc _ _ _
    show eSpec.hom ≫ (splitFiniteEtaleOverSpec R n).hom = _
    rw [h1, ← Spec.map_preimage (Y.left.isoSpec.inv ≫ Y.hom)]
    apply Spec.map_inj.mpr
    apply CommRingCat.hom_ext
    ext x
    simp [RingHom.algebraMap_toAlgebra]
  let a : (ULift.{u} (Fin n) → R) ≃ₐ[R] Γ(Y.left, ⊤) :=
    algEquivOfSpecIso R Γ(Y.left, ⊤) (ULift.{u} (Fin n) → R) eSpec hSpecBase
  exact ⟨n, ⟨a.symm.trans (AlgEquiv.piCongrLeft' R (fun _ : Fin n ↦ R) Equiv.ulift.symm).symm⟩⟩

/-- **A finite étale algebra whose cover is a finite coproduct of copies of the base is a finite
product of copies of the base ring.** -/
theorem exists_algEquiv_pi_of_isFiniteCoproductOfTerminal (S : Type u) [CommRing S] [Algebra R S]
    (Y : FiniteEtaleOver (Spec (.of R))) (e : Y.left ≅ Spec (.of S))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) = Y.hom)
    (hY : IsFiniteCoproductOfTerminal Y) :
    ∃ n : ℕ, Nonempty (S ≃ₐ[R] (Fin n → R)) := by
  let : IsAffine Y.left := isAffine_left_of_finiteEtaleOver_spec R Y
  let : Algebra R Γ(Y.left, ⊤) := (Spec.preimage (Y.left.isoSpec.inv ≫ Y.hom)).hom.toAlgebra
  obtain ⟨n, ⟨e'⟩⟩ := exists_algEquiv_pi_sections_of_isFiniteCoproductOfTerminal R Y hY
  let eΓ := Y.left.isoSpec.symm ≪≫ e
  have hΓ : eΓ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y.left, ⊤))) := by
    show (Y.left.isoSpec.inv ≫ e.hom) ≫ _ = _
    rw [Category.assoc, he]
    exact (Spec.map_preimage _).symm
  exact ⟨n, ⟨(algEquivOfSpecIso R Γ(Y.left, ⊤) S eΓ hΓ).trans e'⟩⟩

/-- **A finite étale cover of the spectrum of a strictly henselian local ring is a finite
coproduct of copies of the base**: it is isomorphic over the base to a split cover. -/
theorem isFiniteCoproductOfTerminal_of_henselian_isSepClosed [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] (Y : FiniteEtaleOver (Spec (.of R))) :
    IsFiniteCoproductOfTerminal Y := by
  obtain ⟨n, e, he⟩ := finiteEtaleOver_spec_iso_pi_of_henselian_isSepClosed R Y
  exact isFiniteCoproductOfTerminal_of_iso_split R Y n e he

/-- Base change of the finite étale cover attached to an algebra is the cover attached to the base
changed algebra. -/
def finiteEtaleOverSpec_baseChangeIso (S T : Type u) [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Module.Finite R S] [Algebra.Etale R S] :
    (finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom (algebraMap R T)))).obj
        (finiteEtaleOverSpec R S) ≅ finiteEtaleOverSpec T (T ⊗[R] S) := by
  refine MorphismProperty.Over.isoMk (pullbackSymmetry _ _ ≪≫ pullbackSpecIso R T S) ?_
  change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R T S).hom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[R] S))) = _
  rw [Category.assoc, pullbackSpecIso_hom_fst']
  exact pullbackSymmetry_hom_comp_fst _ _

end Split

/-! ### Integral closures and the strict henselization -/

/-- **The integral closure of a normal domain in a finite product of copies of its fraction field
is the corresponding product of copies of the domain.** -/
@[ega "II 6.3.6" "special case"]
def integralClosurePiFractionEquiv (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsDomain R] [IsIntegrallyClosed R] (n : ℕ) :
    integralClosure R (Fin n → K) ≃ₐ[R] (Fin n → R) :=
  (integralClosurePiEquiv R (fun _ : Fin n ↦ K)).trans
    (AlgEquiv.piCongrRight fun _ ↦ IsIntegralClosure.equiv R (integralClosure R K) K R)

/-- If the base change of `L` to a normal domain `Ash` with fraction field `Ksh` is a finite
product of copies of `Ksh`, then the integral closure of `Ash` in it is the corresponding finite
product of copies of `Ash`. -/
theorem nonempty_integralClosure_algEquiv_pi_of_algEquiv_pi_fractionField
    (A Ash Ksh : Type u) [CommRing A] [IsDomain A] [CommRing Ash] [IsDomain Ash]
    [IsIntegrallyClosed Ash] [Field Ksh] [Algebra A Ash] [Algebra Ash Ksh]
    [IsFractionRing Ash Ksh] (L : Type u) [CommRing L] [Algebra A L]
    (n : ℕ) (e : Ash ⊗[A] L ≃ₐ[Ash] (Fin n → Ksh)) :
    Nonempty (integralClosure Ash (Ash ⊗[A] L) ≃ₐ[Ash] (Fin n → Ash)) :=
  ⟨(((integralClosure Ash (Ash ⊗[A] L)).equivMapOfInjective e.toAlgHom e.injective).trans
      (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e))).trans
    (integralClosurePiFractionEquiv Ash Ksh n)⟩

variable (K Ksh : Type u) [Field K] [Field Ksh] [IsDomain A] [Algebra A K] [IsFractionRing A K]
  [Algebra Ash Ksh] [IsFractionRing Ash Ksh] [Algebra A Ksh] [Algebra K Ksh]
  [IsScalarTower A K Ksh] [IsScalarTower A Ash Ksh]

omit [IsDomain A] in
/-- **The integral closure of `A` in `L` is finite étale over `A` once it is split after base
change to a strict henselization.** Base change to the strict henselization commutes with
integral closure (Stacks 0CBF), and the strict henselization is faithfully flat, so both
finiteness and étaleness descend. -/
@[sga "7 II 2.3.1" "partial"]
theorem module_finite_and_etale_integralClosure_of_split_of_isHenselization
    [IsHenselization A κsep Ash] (L : Type u) [CommRing L] [Algebra A L]
    (hsplit : ∃ n : ℕ, Nonempty (integralClosure Ash (Ash ⊗[A] L) ≃ₐ[Ash] (Fin n → Ash))) :
    Module.Finite A (integralClosure A L) ∧ Algebra.Etale A (integralClosure A L) := by
  obtain ⟨n, ⟨eSplit⟩⟩ := hsplit
  let eBase : Ash ⊗[A] (integralClosure A L) ≃ₐ[Ash] integralClosure Ash (Ash ⊗[A] L) :=
    AlgEquiv.ofBijective (TensorProduct.toIntegralClosure A Ash L)
      (toIntegralClosure_bijective_of_isHenselization (L := κsep))
  have : Module.FaithfullyFlat A Ash := IsHenselization.faithfullyFlat (L := κsep)
  refine ⟨?_, ?_⟩
  · have hfin : Module.Finite Ash (Ash ⊗[A] (integralClosure A L)) := by
      rw [Module.Finite.equiv_iff (eBase.trans eSplit).toLinearEquiv]
      infer_instance
    exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat Ash
  · have : Algebra.Etale Ash (Ash ⊗[A] (integralClosure A L)) :=
      Algebra.Etale.of_equiv (eBase.trans eSplit).symm
    exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Ash

/-- **The integral closure of a normal local domain `A` in an algebra `L` over its fraction field
is finite étale over `A` once `L` splits over the fraction field of a strict henselization.** The
fraction field of the strict henselization is the base change of the fraction field of `A`, so
splitness over it turns into splitness of the base change of `L` to the strict henselization. -/
theorem module_finite_and_etale_integralClosure_of_split_generic_of_isHenselization
    [IsIntegrallyClosed A] [IsSepClosure (ResidueField A) κsep] [IsHenselization A κsep Ash]
    (L : Type u) [CommRing L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    (hsplit : ∃ n : ℕ, Nonempty (Ksh ⊗[K] L ≃ₐ[Ksh] (Fin n → Ksh))) :
    Module.Finite A (integralClosure A L) ∧ Algebra.Etale A (integralClosure A L) := by
  have : Module.FaithfullyFlat A Ash := IsHenselization.faithfullyFlat (L := κsep)
  have : Algebra.IsAlgebraic A Ash := isAlgebraic_of_isHenselization A Ash κsep K
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_of_isHenselization A Ash κsep
  have : Algebra.IsPushout A Ash K Ksh := inferInstance
  obtain ⟨n, ⟨e⟩⟩ := hsplit
  let e' : Ash ⊗[A] L ≃ₐ[Ash] (Fin n → Ksh) :=
    (Algebra.IsPushout.cancelBaseChangeAlg A Ash K Ksh L).symm.trans (e.restrictScalars Ash)
  exact module_finite_and_etale_integralClosure_of_split_of_isHenselization A Ash κsep L
    ⟨n, nonempty_integralClosure_algEquiv_pi_of_algEquiv_pi_fractionField A Ash Ksh L n e'⟩

omit [IsDomain A] [IsFractionRing A K] [IsFractionRing Ash Ksh] in
/-- **A finite étale cover of `Spec A` becomes a finite coproduct of copies of the base over the
generic point of a strict henselization.** It is already split over `Spec A^sh`, which is
strictly henselian, and base change from `Spec A^sh` to `Spec K^sh` is exact, so it carries
finite coproducts of terminal objects to finite coproducts of terminal objects. -/
theorem isFiniteCoproductOfTerminal_finiteEtaleBaseChange_fractionField_of_isHenselization
    [IsIntegrallyClosed A] [IsSepClosure (ResidueField A) κsep] [IsHenselization A κsep Ash]
    (x : GeometricPoint (Spec (.of Ksh)))
    [IsGaloisCategory (finiteEtaleFiberFunctor x)]
    [IsGaloisCategory (finiteEtaleFiberFunctor
      (x.map (Spec.map (CommRingCat.ofHom (algebraMap Ash Ksh)))))]
    (Y : FiniteEtaleOver (Spec (.of A))) :
    IsFiniteCoproductOfTerminal
      ((finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom (algebraMap K Ksh)))).obj
        ((finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom (algebraMap A K)))).obj Y)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K Ksh))
  let g := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let i := Spec.map (CommRingCat.ofHom (algebraMap Ash Ksh))
  let j := Spec.map (CommRingCat.ofHom (algebraMap A Ash))
  have heq : f ≫ g = i ≫ j := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply Spec.map_inj.mpr
    apply CommRingCat.hom_ext
    ext a
    exact (IsScalarTower.algebraMap_apply A K Ksh a).symm.trans
      (IsScalarTower.algebraMap_apply A Ash Ksh a)
  let e₁ : finiteEtaleBaseChange (f ≫ g) ≅
      finiteEtaleBaseChange g ⋙ finiteEtaleBaseChange f :=
    MorphismProperty.Over.pullbackComp f g
  let e₂ : finiteEtaleBaseChange (f ≫ g) ≅
      finiteEtaleBaseChange j ⋙ finiteEtaleBaseChange i :=
    MorphismProperty.Over.pullbackComp i j (f ≫ g) heq
  have : HenselianLocalRing Ash := IsHenselization.henselian (R := A) (L := κsep)
  have : IsSepClosed (ResidueField Ash) :=
    isSepClosed_residueField_of_isHenselization A Ash κsep
  have : PreservesFiniteLimits (finiteEtaleBaseChange i) :=
    (exactFunctor_finiteEtaleBaseChange i x).1
  have : PreservesFiniteColimits (finiteEtaleBaseChange i) :=
    (exactFunctor_finiteEtaleBaseChange i x).2
  exact isFiniteCoproductOfTerminal_of_iso ((e₂.symm ≪≫ e₁).app Y)
    (isFiniteCoproductOfTerminal_map (finiteEtaleBaseChange i)
      (isFiniteCoproductOfTerminal_of_henselian_isSepClosed Ash ((finiteEtaleBaseChange j).obj Y)))

/-! ### Extending a section over the generic point -/

/-- **A map from a finite algebra over a normal domain to its fraction field lands in the
domain.** Each value is integral over the domain, hence in its image, and the resulting map is a
homomorphism because the structure map to the fraction field is injective. -/
theorem exists_algHom_of_algHom_fractionField (R S F : Type u) [CommRing R] [CommRing S]
    [Field F] [IsDomain R] [IsIntegrallyClosed R] [Algebra R S] [Module.Finite R S]
    [Algebra R F] [IsFractionRing R F] (φ : S →ₐ[R] F) :
    ∃ ψ : S →ₐ[R] R, ∀ s, algebraMap R F (ψ s) = φ s := by
  classical
  let a : S → R := fun s ↦ Classical.choose <|
    IsIntegrallyClosed.algebraMap_eq_of_integral
      (IsIntegral.map φ (IsIntegral.of_finite R s))
  have ha (s : S) : algebraMap R F (a s) = φ s :=
    Classical.choose_spec <| IsIntegrallyClosed.algebraMap_eq_of_integral
      (IsIntegral.map φ (IsIntegral.of_finite R s))
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  refine ⟨{ toFun := a
            map_one' := hinj (by simp [ha])
            map_mul' := fun x y ↦ hinj (by simp only [map_mul, ha])
            map_zero' := hinj (by simp [ha])
            map_add' := fun x y ↦ hinj (by simp only [map_add, ha])
            commutes' := fun r ↦ hinj ((ha (algebraMap R S r)).trans (φ.commutes r)) }, ha⟩

/-- A finite étale affine cover of `Spec R` has a finite étale `R`-algebra of global sections. -/
private theorem module_finite_and_etale_sections_of_finiteEtaleOver (R : Type u) [CommRing R]
    (Y : FiniteEtaleOver (Spec (.of R))) [IsAffine Y.left] :
    letI : Algebra R Γ(Y.left, ⊤) := (Spec.preimage (Y.left.isoSpec.inv ≫ Y.hom)).hom.toAlgebra
    Module.Finite R Γ(Y.left, ⊤) ∧ Algebra.Etale R Γ(Y.left, ⊤) := by
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  let : Algebra R Γ(Y.left, ⊤) := (Spec.preimage (Y.left.isoSpec.inv ≫ Y.hom)).hom.toAlgebra
  constructor
  · rw [← RingHom.finite_algebraMap]
    apply (IsFinite.SpecMap_iff _).mp
    rw [Spec.map_preimage]
    infer_instance
  · rw [← RingHom.etale_algebraMap]
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    infer_instance

/-- **A section of a finite étale cover of `Spec R` over the generic point extends to a section
over `Spec R`**, for `R` a normal domain: the cover is affine, so the section is an `R`-algebra
map from its finite algebra of global sections to the fraction field, and such a map lands in
`R`. -/
theorem exists_section_of_section_fractionField (R F : Type u) [CommRing R] [Field F] [IsDomain R]
    [IsIntegrallyClosed R] [Algebra R F] [IsFractionRing R F]
    (Y : FiniteEtaleOver (Spec (.of R))) (s : Spec (.of F) ⟶ Y.left)
    (hs : s ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap R F))) :
    ∃ t : Spec (.of R) ⟶ Y.left, t ≫ Y.hom = 𝟙 _ := by
  have : IsAffine Y.left := isAffine_left_of_finiteEtaleOver_spec R Y
  let φ : CommRingCat.of R ⟶ CommRingCat.of Γ(Y.left, ⊤) :=
    Spec.preimage (Y.left.isoSpec.inv ≫ Y.hom)
  let : Algebra R Γ(Y.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(Y.left, ⊤) := (module_finite_and_etale_sections_of_finiteEtaleOver R Y).1
  let ψ : CommRingCat.of Γ(Y.left, ⊤) ⟶ CommRingCat.of F :=
    Spec.preimage (s ≫ Y.left.isoSpec.hom)
  have hψ : φ ≫ ψ = CommRingCat.ofHom (algebraMap R F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hs
  obtain ⟨t, ht⟩ := exists_algHom_of_algHom_fractionField R Γ(Y.left, ⊤) F
    { toRingHom := ψ.hom
      commutes' := fun r ↦
        congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of F ↦ k r) hψ }
  refine ⟨Spec.map (CommRingCat.ofHom t.toRingHom) ≫ Y.left.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← Spec.map_preimage (Y.left.isoSpec.inv ≫ Y.hom), ← Spec.map_comp,
    ← Spec.map_id]
  apply Spec.map_inj.mpr
  apply CommRingCat.hom_ext
  ext r
  exact t.commutes r

/-- **Base change to the generic point of a normal domain is fully faithful on finite étale
covers.** By Stacks 0BN6 this is the statement that a connected finite étale cover of `Spec R`
with a section over the generic point has a section over `Spec R`, which is
`AlgebraicGeometry.exists_section_of_section_fractionField`. -/
theorem fullyFaithful_finiteEtaleBaseChange_fractionField (R F : Type u) [CommRing R] [Field F]
    [IsDomain R] [IsIntegrallyClosed R] [Algebra R F] [IsFractionRing R F]
    [ConnectedSpace (Spec (.of R))] [ConnectedSpace (Spec (.of F))]
    (x : GeometricPoint (Spec (.of F)))
    [IsGaloisCategory (finiteEtaleFiberFunctor x)]
    [IsGaloisCategory (finiteEtaleFiberFunctor
      (x.map (Spec.map (CommRingCat.ofHom (algebraMap R F)))))] :
    Nonempty (finiteEtaleBaseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R F)))).FullyFaithful := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R F))
  let H := finiteEtaleBaseChange g
  let F₀ := finiteEtaleFiberFintypeFunctor (Spec (.of R)) (x.map g)
  let F₁ := finiteEtaleFiberFintypeFunctor (Spec (.of F)) x
  let t := finiteEtaleFiberFintypeFunctorBaseChangeIso g x
  let d := galoisFunctorDataOfFiberIso F₀ F₁ H t
  let _g₀ : IsGaloisCategory (setValuedFiberFunctor F₀) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor _ _
  let _g₁ : IsGaloisCategory (setValuedFiberFunctor F₁) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor _ _
  let star := finiteEtaleOverTerminal (Spec (.of R))
  let star' := finiteEtaleOverTerminal (Spec (.of F))
  have hs : IsTerminal star := MorphismProperty.Over.mkIdTerminal _ _
  have hs' : IsTerminal star' := MorphismProperty.Over.mkIdTerminal _ _
  have hH := exactFunctor_finiteEtaleBaseChange g x
  have : PreservesFiniteLimits H := hH.1
  apply ((surjective_inducedHom_tfae F₀ F₁ H hH t d star star' hs hs'
    (hs.isTerminalObj H star)).out 4 2).mp
  rintro Y _ ⟨σ⟩
  let v : Spec (.of F) ⟶ Y.left := σ.left ≫ pullback.fst Y.hom g
  have hv : v ≫ Y.hom = g := by
    have hw : σ.left ≫ pullback.snd Y.hom g = 𝟙 _ := σ.w
    have h1 : pullback.fst Y.hom g ≫ Y.hom = pullback.snd Y.hom g ≫ g := pullback.condition
    have h2 : σ.left ≫ (pullback.fst Y.hom g ≫ Y.hom) =
      σ.left ≫ (pullback.snd Y.hom g ≫ g) := congrArg (σ.left ≫ ·) h1
    have h3 : (σ.left ≫ pullback.fst Y.hom g) ≫ Y.hom =
        (σ.left ≫ pullback.snd Y.hom g) ≫ g :=
      (Category.assoc _ _ _).trans (h2.trans (Category.assoc _ _ _).symm)
    exact h3.trans ((congrArg (· ≫ g) hw).trans (Category.id_comp g))
  obtain ⟨w, hw⟩ := exists_section_of_section_fractionField R F Y v hv
  exact ⟨MorphismProperty.Over.homMk w hw⟩

/-- **A finite algebra over the fraction field of a normal domain is the generic fibre of the
integral closure.** The integral closure is obtained from the algebra by inverting the nonzero
elements of the domain. -/
theorem isLocalization_integralClosure_fractionField (R F L : Type u) [CommRing R] [IsDomain R]
    [Field F] [CommRing L] [Algebra R F] [IsFractionRing R F] [Algebra R L] [Algebra F L]
    [IsScalarTower R F L] [Algebra.IsAlgebraic F L] :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R L)
      (nonZeroDivisors R)) L := by
  have : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F (nonZeroDivisors R)
  have : Algebra.IsAlgebraic R L := Algebra.IsAlgebraic.trans R F L
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, r, hr, rfl⟩
    show IsUnit (algebraMap R L r)
    rw [IsScalarTower.algebraMap_apply R F L]
    exact (IsLocalization.map_units F (⟨r, hr⟩ : nonZeroDivisors R)).map _
  · intro z
    obtain ⟨r, s, hr, hs⟩ :=
      (Algebra.IsAlgebraic.isAlgebraic (R := R) z).exists_smul_eq (integralClosure R L)
    refine ⟨(s, ⟨algebraMap R (integralClosure R L) r,
      ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, rfl⟩⟩), ?_⟩
    show z * algebraMap R L r = (s : L)
    simpa [Algebra.smul_def, mul_comm, Subalgebra.algebraMap_eq] using hs
  · intro x y hxy
    obtain rfl : x = y := Subtype.ext hxy
    exact ⟨1, rfl⟩

/-- **A finite étale cover of the generic point of a normal local domain which splits over the
generic point of a strict henselization comes from `Spec A`.** Its algebra of global sections `L`
splits over `K^sh`, so the integral closure of `A` in `L` is finite étale over `A`, and `L` is its
generic fibre. -/
private theorem essImage_finiteEtaleBaseChange_fractionField_of_isFiniteCoproductOfTerminal
    [IsIntegrallyClosed A] [IsSepClosure (ResidueField A) κsep] [IsHenselization A κsep Ash]
    (V : FiniteEtaleOver (Spec (.of K)))
    (hsplit : IsFiniteCoproductOfTerminal
      ((finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom (algebraMap K Ksh)))).obj V)) :
    (finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom (algebraMap A K)))).essImage V := by
  have : IsAffine V.left := isAffine_left_of_finiteEtaleOver_spec K V
  let L := Γ(V.left, ⊤)
  let φ : CommRingCat.of K ⟶ CommRingCat.of L :=
    Spec.preimage (V.left.isoSpec.inv ≫ V.hom)
  let : Algebra K L := φ.hom.toAlgebra
  obtain ⟨_, _⟩ : Module.Finite K L ∧ Algebra.Etale K L :=
    module_finite_and_etale_sections_of_finiteEtaleOver K V
  let V' := finiteEtaleOverSpec K L
  let eV : V ≅ V' := MorphismProperty.Over.isoMk V.left.isoSpec (by
    show V.left.isoSpec.hom ≫ Spec.map φ = V.hom
    rw [Spec.map_preimage]
    simp)
  have hS : IsFiniteCoproductOfTerminal (finiteEtaleOverSpec Ksh (Ksh ⊗[K] L)) :=
    isFiniteCoproductOfTerminal_of_iso
      ((finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom (algebraMap K Ksh)))).mapIso eV ≪≫
        finiteEtaleOverSpec_baseChangeIso K L Ksh) hsplit
  have hsplitalg : ∃ n : ℕ, Nonempty (Ksh ⊗[K] L ≃ₐ[Ksh] (Fin n → Ksh)) :=
    exists_algEquiv_pi_of_isFiniteCoproductOfTerminal Ksh (Ksh ⊗[K] L)
      (finiteEtaleOverSpec Ksh (Ksh ⊗[K] L)) (Iso.refl _) (Category.id_comp _) hS
  let : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨_, _⟩ := module_finite_and_etale_integralClosure_of_split_generic_of_isHenselization
    A Ash κsep K Ksh L hsplitalg
  let B := integralClosure A L
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    isLocalization_integralClosure_fractionField A K L
  have : Algebra.IsPushout A B K L :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors A) K B L
  have : Algebra.IsPushout A K B L := Algebra.IsPushout.symm inferInstance
  let eB : K ⊗[A] B ≃ₐ[K] L := Algebra.IsPushout.equiv A K B L
  let eY : (finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom (algebraMap A K)))).obj
      (finiteEtaleOverSpec A B) ≅ V' :=
    finiteEtaleOverSpec_baseChangeIso A B K ≪≫
      MorphismProperty.Over.isoMk (specIsoOfAlgEquiv K eB) (specIsoOfAlgEquiv_hom_comp K eB)
  exact ⟨finiteEtaleOverSpec A B, ⟨eY ≪≫ eV.symm⟩⟩

/-! ### The local exact sequence -/

/-- **The local exact sequence for a normal local ring.** Let
`A` be a normal local domain with fraction field `K`, let `A^sh` be a strict henselization of `A`
and `K^sh` its fraction field, and let `x` be a geometric point of `Spec K^sh`. Then

```
π₁(Spec K^sh, x) → π₁(Spec K, x) → π₁(Spec A, x) → 1
```

is exact.

The criterion of Stacks 0BS9 reduces this to two statements. Base change to the generic point is
fully faithful because a connected finite étale cover of `Spec A` with a section over `K` has a
section over `A`. A cover of `Spec K` comes from `Spec A` exactly when it becomes a finite
coproduct of copies of the base over `Spec K^sh`: one direction is that a cover pulled back from
`Spec A` is already split over the strictly henselian `Spec A^sh`, and the other is that the
integral closure of `A` in such a cover is finite étale over `A` — which it is because it is so
after the faithfully flat base change to `A^sh` — and has the cover as its generic fibre.

The four spectra are spectra of local rings, hence connected, so the Galois-category property
of Stacks Tag 0BNB applies at each of their geometric points. -/
@[stacks 0BSM]
theorem isExactSequence_etaleFundamentalGroupMap_fractionField_of_isHenselization
    [IsIntegrallyClosed A] [IsSepClosure (ResidueField A) κsep] [IsHenselization A κsep Ash]
    (x : GeometricPoint (Spec (.of Ksh))) :
    IsExactSequence
      (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K Ksh))) x)
      (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap A K)))
        (x.map (Spec.map (CommRingCat.ofHom (algebraMap K Ksh))))) := by
  have : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
  have : ConnectedSpace (Spec (.of Ash)) := connectedSpace_spec_of_isLocalRing Ash
  have : ConnectedSpace (Spec (.of K)) := connectedSpace_spec_of_isLocalRing K
  have : ConnectedSpace (Spec (.of Ksh)) := connectedSpace_spec_of_isLocalRing Ksh
  set f := Spec.map (CommRingCat.ofHom (algebraMap K Ksh))
  set g := Spec.map (CommRingCat.ofHom (algebraMap A K))
  have := finiteEtaleFiberFunctor_isGaloisCategory (Spec (.of Ksh)) x
  have := finiteEtaleFiberFunctor_isGaloisCategory (Spec (.of K)) (x.map f)
  have := finiteEtaleFiberFunctor_isGaloisCategory (Spec (.of A)) ((x.map f).map g)
  have := finiteEtaleFiberFunctor_isGaloisCategory (Spec (.of Ash))
    (x.map (Spec.map (CommRingCat.ofHom (algebraMap Ash Ksh))))
  refine isExactSequence_etaleFundamentalGroupMap f g x
    (fullyFaithful_finiteEtaleBaseChange_fractionField A K (x.map f)) (fun V ↦ ⟨?_, ?_⟩)
  · rintro ⟨Y, ⟨e⟩⟩
    exact isFiniteCoproductOfTerminal_of_iso ((finiteEtaleBaseChange f).mapIso e)
      (isFiniteCoproductOfTerminal_finiteEtaleBaseChange_fractionField_of_isHenselization
        A Ash κsep K Ksh x Y)
  · exact essImage_finiteEtaleBaseChange_fractionField_of_isFiniteCoproductOfTerminal
      A Ash κsep K Ksh V

end AlgebraicGeometry

end
