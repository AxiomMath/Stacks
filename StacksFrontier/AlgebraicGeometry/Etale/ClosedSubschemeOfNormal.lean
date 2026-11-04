module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.FieldTheory.IsSepClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.NormalSepClosedFunctionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.EtaleLocalRepresentability
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSpectrumVanishing
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.LocalTriviality
public import StacksFrontier.RingTheory.Etale.Lifting

/-!
# Étale morphisms over closed subschemes of normal affine schemes

Let `X` be an integral normal affine scheme whose function field is separably closed, and let
`Z` be a closed subscheme of `X`. Every affine scheme étale over `Z` is a finite disjoint
union of open subschemes of `Z`; a surjective finite étale morphism of this kind therefore has
a section. Consequently the first étale cohomology of `Z` with coefficients in a finite
constant abelian group vanishes, and so does its étale cohomology in every positive degree.

## Main results

* `AlgebraicGeometry.exists_finite_coproduct_open_immersions` presents an affine étale scheme
  over `Z` as a finite coproduct of open subschemes of `Z`.
* `AlgebraicGeometry.exists_section_of_surjective_finite_etale` gives a section of a
  surjective finite étale morphism over `Z`.
* `AlgebraicGeometry.subsingleton_smallEtaleH1_constantSheaf'` is the vanishing of the first
  cohomology of the small étale site of `Z` with finite constant abelian coefficients.
* `AlgebraicGeometry.stalk_strictlyHenselian_of_isClosedImmersion`: every local ring of `Z` is
  strictly henselian.
* `AlgebraicGeometry.subsingleton_smallEtaleH_constantSheaf'` is the vanishing of the étale
  cohomology of `Z` with finite constant abelian coefficients in every positive degree.

The unprimed `AlgebraicGeometry.subsingleton_smallEtaleH1_constantSheaf` and
`AlgebraicGeometry.subsingleton_smallEtaleH_constantSheaf` are the same two statements over the
effective-descent hypothesis `h0245`,
`Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability`; the primed forms discharge
it, and the tags sit there.

## Implementation notes

A closed subscheme is represented by a closed immersion into `X`. The finite disjoint union is
represented by a coproduct indexed by `Fin n`, and the displayed equation records
compatibility of the coproduct presentation with the given morphism to `Z`. A section is
expressed by a right inverse in the category of schemes.

The reduction to `X` goes through a pushout of affine schemes: an étale algebra over the
quotient cutting out `Z` lifts to an étale algebra over `X`, and the square so produced is a
pushout. The algebraic half of that argument is collected in the opening section.

The cohomological statement reads a class in first cohomology as a torsor (Stacks 03AJ), the
torsor as a finite locally constant sheaf of sets, and that sheaf as a scheme finite étale over
`Z` (Stacks 03RV); the section furnished above trivializes the torsor. Vanishing of an abelian
group is expressed by `Subsingleton`. The small étale site is formed inside an arbitrary big
étale site containing `Z`, a size choice absent from the mathematical assertion, and the
coefficient group is taken in the universe `u + 1` where the sheaves of sets on that site live;
every finite abelian group has a model there.

The implication from finite local constancy to representability by a finite étale scheme is
effective descent for schemes affine over the base along an étale covering (Stacks 0245), which
this library proves as
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex`; the primed
statements use it through the unconditional
`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable`, so they carry no
descent hypothesis.  The unprimed statements still take it as the explicit hypothesis `h0245`,
in the packaged form
`Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability`, through
`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable_of_descent`.

The passage from degree one to all positive degrees is the vanishing criterion of Stacks 0GY0,
`Stacks.EtaleCohomology.StrictlyHenselian.subsingleton_H_of_degreeOne_kernel_eq_zero`: on the
spectrum of a ring whose local rings are all strictly henselian, an abelian sheaf with no first
cohomology on the basic opens has no higher cohomology at all. That criterion is stated on the
small étale site of a spectrum placed in a single universe, where cohomology over an object is
available, so it is reached in three steps, all of them in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ConstantSheafVanishingTransport.lean`: `Z` is
affine, hence isomorphic to the spectrum of its ring of global sections; the small étale site
cut out of `B` and Mathlib's small étale site have the same abelian sheaves, as do Mathlib's and
its one-universe model; and the cohomology over a basic open, read as an object of that model,
is the global cohomology of the basic open itself.

The first-cohomology input of the criterion is supplied unconditionally: a basic open of `Z` is
a closed subscheme of the corresponding basic open of `X`, which is again integral, normal and
affine with separably closed function field, so
`AlgebraicGeometry.subsingleton_smallEtaleH1_constantSheaf'` applies to it; the degenerate case
of an empty basic open is handled by the closed immersion into `X` itself.

That all local rings of `Z` are strictly henselian — the other input of the criterion — is
proved here: the local rings of `X` are strictly henselian (Stacks 09Z9), the stalk maps of a
closed immersion are surjective local homomorphisms, and strict henselianness passes along
such a homomorphism, Hensel's lemma being transported by lifting monic polynomials and the
residue field being unchanged (Stacks 05WS).

## References

* [Stacks Project, Tag 09ZA](https://stacks.math.columbia.edu/tag/09ZA)
* [Stacks Project, Tag 09ZB](https://stacks.math.columbia.edu/tag/09ZB)
* [Stacks Project, Tag 09ZC](https://stacks.math.columbia.edu/tag/09ZC)
* [Stacks Project, Tag 09Z9](https://stacks.math.columbia.edu/tag/09Z9)
* [Stacks Project, Tag 05WS](https://stacks.math.columbia.edu/tag/05WS)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 0GY0](https://stacks.math.columbia.edu/tag/0GY0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section PushoutHelpers

open TensorProduct

/-- Surjectivity of the structure map of an algebra is surjectivity of the canonical algebra
map. -/
private theorem surjective_of_algebraMap_surjective
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (h : Function.Surjective (algebraMap R A)) :
    Function.Surjective (Algebra.ofId R A) := by
  intro a
  obtain ⟨r, hr⟩ := h a
  exact ⟨r, by simpa only [Algebra.ofId_apply] using hr⟩

/-- For a surjective map `R → A` with kernel generated by an idempotent-free presentation and
an étale `R`-algebra `C`, the pushout `A ⊗[R] C` is computed by lifting a map out of the
quotient. -/
private noncomputable def affine_pushout_equiv_of_quotient_etale_lift
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra R C]
    (hA : Function.Surjective (algebraMap R A))
    (ψ : C →ₐ[R] B) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker (ψ : C →+* B) =
      (RingHom.ker (algebraMap R A)).map (algebraMap R C)) :
    (A ⊗[R] C) ≃ₐ[R] B := by
  let I := RingHom.ker (Algebra.ofId R A)
  have hI : I = RingHom.ker (algebraMap R A) := by
    ext r
    simp only [RingHom.mem_ker]
    change (Algebra.ofId R A) r = 0 ↔ algebraMap R A r = 0
    rfl
  have hker' : RingHom.ker ψ = I.map (algebraMap R C) := by
    change RingHom.ker (ψ : C →+* B) = I.map (algebraMap R C)
    rw [hker, ← hI]
  let eA : (R ⧸ I) ≃ₐ[R] A :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R A)
      (surjective_of_algebraMap_surjective R A hA)
  let eTensor : ((R ⧸ I) ⊗[R] C) ≃ₐ[R] (A ⊗[R] C) :=
    AlgEquiv.ofBijective
      (Algebra.TensorProduct.map eA.toAlgHom (AlgHom.id R C))
      (Algebra.TensorProduct.map_bijective eA.bijective (Equiv.refl C).bijective)
  let eReduce := (tensorQuotientAlgEquiv R I C).restrictScalars R
  let eKer : (C ⧸ RingHom.ker ψ) ≃ₐ[R]
      (C ⧸ I.map (algebraMap R C)) :=
    Ideal.quotientEquivAlgOfEq R hker'
  let eψ : (C ⧸ RingHom.ker ψ) ≃ₐ[R] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := ψ) hψ
  exact eTensor.symm.trans (eReduce.trans (eKer.symm.trans eψ))

/-- The right inclusion into a tensor product with a quotient, read through the canonical
equivalence. -/
private theorem tensorQuotientAlgEquiv_includeRight_local
    (R : Type u) [CommRing R] (I : Ideal R) (C : Type u) [CommRing C] [Algebra R C]
    (c : C) :
    tensorQuotientAlgEquiv R I C (1 ⊗ₜ[R] c) =
      Ideal.Quotient.mk (I.map (algebraMap R C)) c := by
  change (Algebra.TensorProduct.lift (Algebra.ofId (R ⧸ I)
      (C ⧸ I.map (algebraMap R C))) (Ideal.Quotient.mkₐ R _) (fun _ _ => Commute.all _ _))
      (1 ⊗ₜ[R] c) = _
  rw [Algebra.TensorProduct.lift_tmul]
  simp

/-- The inverse of the tensor comparison equivalence on the right inclusion. -/
private theorem tensorMapEquiv_symm_includeRight
    (R S A C : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing C]
    [Algebra R S] [Algebra R A] [Algebra R C] (e : S ≃ₐ[R] A) (c : C) :
    (AlgEquiv.ofBijective
      (Algebra.TensorProduct.map e.toAlgHom (AlgHom.id R C))
      (Algebra.TensorProduct.map_bijective e.bijective (Equiv.refl C).bijective)).symm
      (1 ⊗ₜ[R] c) = 1 ⊗ₜ[R] c := by
  let E := AlgEquiv.ofBijective
      (Algebra.TensorProduct.map e.toAlgHom (AlgHom.id R C))
      (Algebra.TensorProduct.map_bijective e.bijective (Equiv.refl C).bijective)
  apply E.injective
  simp [E]

/-- The pushout equivalence composed with the right inclusion is the given lift. -/
private theorem affine_pushout_equiv_includeRight
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra R C]
    (hA : Function.Surjective (algebraMap R A))
    (ψ : C →ₐ[R] B) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker (ψ : C →+* B) =
      (RingHom.ker (algebraMap R A)).map (algebraMap R C)) :
    (affine_pushout_equiv_of_quotient_etale_lift R A B C hA ψ hψ hker).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom = ψ.toRingHom := by
  classical
  ext c
  change (affine_pushout_equiv_of_quotient_etale_lift R A B C hA ψ hψ hker)
      (1 ⊗ₜ[R] c) = ψ c
  unfold affine_pushout_equiv_of_quotient_etale_lift
  simp only [AlgEquiv.trans_apply]
  rw [tensorMapEquiv_symm_includeRight]
  simp only [AlgEquiv.restrictScalars_apply]
  rw [tensorQuotientAlgEquiv_includeRight_local]
  rw [Ideal.quotientEquivAlgOfEq_symm, Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk hψ c

/-- The pushout equivalence composed with the left inclusion is the canonical map. -/
private theorem affine_pushout_equiv_includeLeft
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra R C]
    (hA : Function.Surjective (algebraMap R A))
    (ψ : C →ₐ[R] B) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker (ψ : C →+* B) =
      (RingHom.ker (algebraMap R A)).map (algebraMap R C)) :
    (affine_pushout_equiv_of_quotient_etale_lift R A B C hA ψ hψ hker).toRingHom.comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] C).toRingHom =
        algebraMap A B := by
  classical
  ext a
  obtain ⟨r, hr⟩ := hA a
  rw [← hr]
  change (affine_pushout_equiv_of_quotient_etale_lift R A B C hA ψ hψ hker)
      (algebraMap R (A ⊗[R] C) r) = algebraMap A B (algebraMap R A r)
  rw [AlgEquiv.commutes]
  exact IsScalarTower.algebraMap_apply R A B r

/-- The square exhibiting `A ⊗[R] C` as the pushout of a surjection and an étale map is a
pushout of affine schemes. -/
private theorem affine_lift_isPushout
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra R C] [Algebra C B] [IsScalarTower R C B]
    (hA : Function.Surjective (algebraMap R A))
    (ψ : C →ₐ[R] B) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker (ψ : C →+* B) =
      (RingHom.ker (algebraMap R A)).map (algebraMap R C))
    (hAlg : algebraMap C B = ψ.toRingHom) :
    Algebra.IsPushout R A C B := by
  classical
  let e := affine_pushout_equiv_of_quotient_etale_lift R A B C hA ψ hψ hker
  let eA : (A ⊗[R] C) ≃ₐ[A] B :=
    { toRingEquiv := e.toRingEquiv
      commutes' := by
        intro a
        change (e.toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] C).toRingHom) a =
            algebraMap A B a
        simpa only [e] using
          DFunLike.congr_fun (affine_pushout_equiv_includeLeft R A B C hA ψ hψ hker) a }
  let : Algebra C (A ⊗[R] C) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R C (A ⊗[R] C) := Algebra.TensorProduct.right_isScalarTower
  let : Algebra.IsPushout R A C (A ⊗[R] C) := TensorProduct.isPushout
  exact Algebra.IsPushout.of_equiv eA (by
    ext c
    rw [Algebra.TensorProduct.algebraMap_eq_includeRight, hAlg]
    change (e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom) c = ψ c
    exact DFunLike.congr_fun
      (affine_pushout_equiv_includeRight R A B C hA ψ hψ hker) c)

end PushoutHelpers

/-- **Stacks Project, Tag 09ZA, first assertion.** An affine etale scheme over a closed
subscheme of an integral normal affine scheme with separably closed function field is a finite
disjoint union of open subschemes of the closed subscheme. -/
@[stacks 09ZA "finite disjoint union"]
theorem exists_finite_coproduct_open_immersions
    (X : Scheme.{u}) [IsAffine X] [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
    (V : Scheme.{u}) [IsAffine V] (f : V ⟶ Z) [Etale f] :
    ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (j : ∀ a, U a ⟶ Z)
      (_ : ∀ a, IsOpenImmersion (j a)) (e : V ≅ ∐ U),
      e.hom ≫ Sigma.desc j = f :=
  by
  classical
  have : IsAffine Z := isAffine_of_isAffineHom i
  let R : Type u := Γ(X, ⊤)
  let A : Type u := Γ(Z, ⊤)
  let B : Type u := Γ(V, ⊤)
  let : Algebra R A := RingHom.toAlgebra i.appTop.hom
  let : Algebra A B := RingHom.toAlgebra f.appTop.hom
  let : Algebra R B := RingHom.toAlgebra (f.appTop.hom.comp i.appTop.hom)
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsurj : Function.Surjective (algebraMap R A) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have : Algebra.Etale A B := by
    change RingHom.Etale (f.app ⊤).hom
    rw [← f.appLE_eq_app]
    exact f.etale_appLE (isAffineOpen_top Z) ((isAffineOpen_top Z).preimage f) le_rfl
  obtain ⟨C, hCCommRing, hCAlgebra, hCEtale, ψ, hψsurj, hψker⟩ :=
    etale_lift_along_surjection R A B hsurj
  let : CommRing C := hCCommRing
  let : Algebra R C := hCAlgebra
  let : Algebra.Etale R C := hCEtale
  let : Algebra C B := ψ.toRingHom.toAlgebra
  let : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq fun _ => (ψ.commutes _).symm
  have hpush : Algebra.IsPushout R A C B :=
    affine_lift_isPushout R A B C hsurj ψ hψsurj hψker (RingHom.algebraMap_toAlgebra _)
  let U : Scheme.{u} := Spec (.of C)
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R C))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hCEtale)
  let g : U ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ X.isoSpec.inv
  have : Etale g := by
    dsimp [g]
    infer_instance
  have : IsSeparated g := by
    dsimp [g]
    infer_instance
  let l : V ⟶ U := V.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom ψ.toRingHom)
  obtain ⟨I, W, k, hk, e, he⟩ :=
    exists_coproduct_open_immersions X U g
  have hRingPushout :
      IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R C))
        (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom ψ.toRingHom) :=
    CommRingCat.isPushout_iff_isPushout.mpr hpush
  have hSpecPullback : IsPullback
      (Spec.map (CommRingCat.ofHom ψ.toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R C)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ hRingPushout).flip
  have hPullback : IsPullback l f g i := by
    apply hSpecPullback.of_iso (V.isoSpec.symm) (Iso.refl U)
      (Z.isoSpec.symm) (X.isoSpec.symm)
    · simp only [l]
      rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc]
    · change Spec.map (f.appTop) ≫ Z.isoSpec.inv = V.isoSpec.inv ≫ f
      exact Scheme.isoSpec_inv_naturality f
    · change Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ X.isoSpec.inv =
        𝟙 U ≫ (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ X.isoSpec.inv)
      simp
    · change Spec.map (i.appTop) ≫ X.isoSpec.inv = Z.isoSpec.inv ≫ i
      exact Scheme.isoSpec_inv_naturality i
  let a : ∀ t : I, W t ⟶ U := fun t => Sigma.ι W t ≫ e.inv
  have ha (t : I) : a t ≫ g = k t := by
    dsimp [a]
    rw [Category.assoc, ← he]
    simp
  have haOpen (t : I) : IsOpenImmersion (a t) := by
    dsimp [a]
    infer_instance
  let T : I → Scheme := fun t => pullback (a t) l
  let s : ∀ t, T t ⟶ V := fun t => pullback.snd (a t) l
  let q : ∀ t, T t ⟶ Z := fun t => s t ≫ f
  have hsOpen (t : I) : IsOpenImmersion (s t) := by
    dsimp [s]
    exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (a t) l) (haOpen t)
  have hLocal (t : I) :
      IsPullback (pullback.fst (a t) l) (q t) (k t) i := by
    dsimp [q, s]
    simpa [ha t, Category.assoc] using
      (IsPullback.of_hasPullback (a t) l).paste_vert hPullback
  have hqOpen (t : I) : IsOpenImmersion (q t) :=
    MorphismProperty.of_isPullback (hLocal t) (hk t)
  have haDisj : Pairwise (fun t t' => Disjoint (a t).opensRange (a t').opensRange) := by
    intro t t' htt'
    rw [disjoint_iff, TopologicalSpace.Opens.ext_iff]
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      change z ∈ Set.range (a t) at hz
      change z ∈ Set.range (a t') at hz'
      obtain ⟨x, rfl⟩ := hz
      obtain ⟨y, hy⟩ := hz'
      have hEq := congrArg (fun w : U => e.hom w) hy.symm
      have hSigma : Sigma.ι W t x = Sigma.ι W t' y := by
        simpa [a, Scheme.Hom.comp_apply] using hEq
      exact False.elim (htt' (congrArg Sigma.fst ((sigmaι_eq_iff W t t' x y).mp hSigma)))
    · intro hz
      exact False.elim hz
  have haCover : ∀ x : U, ∃ t, x ∈ (a t).opensRange := by
    intro x
    let σ : (Σ t : I, W t) ≃ₜ (∐ W : Scheme.{u}) := AlgebraicGeometry.sigmaMk W
    obtain ⟨⟨t, w⟩, hw⟩ := σ.surjective (e.hom x)
    have hw' : Sigma.ι W t w = e.hom x := by
      simpa only [σ, AlgebraicGeometry.sigmaMk_mk] using hw
    refine ⟨t, ?_⟩
    apply Set.mem_range.mpr
    refine ⟨w, ?_⟩
    have h := congrArg (fun z : (∐ W : Scheme.{u}) => e.inv z) hw'
    simpa [a, Scheme.Hom.comp_apply] using h
  have hsRange (t : I) :
      (s t).opensRange = l ⁻¹ᵁ (a t).opensRange := by
    simpa [s] using Scheme.Hom.opensRange_pullbackSnd (a t) l
  have hsCover : ∀ x : V, ∃ t, x ∈ (s t).opensRange := by
    intro x
    obtain ⟨t, ht⟩ := haCover (l x)
    exact ⟨t, by rw [hsRange]; exact ht⟩
  have : CompactSpace V := Scheme.compactSpace_of_isAffine V
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun t => ((s t).opensRange : Set V)) (fun t => (s t).opensRange.2)
    (fun x _ => Set.mem_iUnion.mpr (hsCover x))
  let J := {t : I // t ∈ F}
  let T' : J → Scheme := fun j => T j.1
  let s' : ∀ j, T' j ⟶ V := fun j => s j.1
  let q' : ∀ j, T' j ⟶ Z := fun j => q j.1
  have hSOpen (j : J) : IsOpenImmersion (s' j) := hsOpen j.1
  have hQOpen (j : J) : IsOpenImmersion (q' j) := hqOpen j.1
  have hSDisj : Pairwise (fun j j' => Disjoint (s' j).opensRange (s' j').opensRange) := by
    intro j j' hj
    change Disjoint (s j.1).opensRange (s j'.1).opensRange
    rw [hsRange, hsRange, disjoint_iff]
    change l ⁻¹ᵁ ((a j.1).opensRange ⊓ (a j'.1).opensRange) = ⊥
    rw [(haDisj (fun h => hj (Subtype.ext h))).eq_bot]
    rfl
  have hSCover : ⨆ j : J, (s' j).opensRange = ⊤ := by
    refine top_unique fun x _ => ?_
    obtain ⟨t, htF, htx⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x))
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨⟨t, htF⟩, htx⟩
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of s' hSCover hSDisj
  have hSigmaIso : IsIso (Sigma.desc s') :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk V s')).mp ⟨hc⟩
  let eJ : V ≅ ∐ T' := asIso (Sigma.desc s') |>.symm
  have heJ : eJ.hom ≫ Sigma.desc s' = 𝟙 V := eJ.hom_inv_id
  let n := F.card
  let ρ : Fin n ≃ J := F.equivFin.symm
  let U' : Fin n → Scheme := fun b => T' (ρ b)
  let j' : ∀ b, U' b ⟶ Z := fun b => q' (ρ b)
  let e' : V ≅ ∐ U' := eJ ≪≫ (Sigma.reindex ρ T').symm
  refine ⟨n, U', j', (fun b => hQOpen (ρ b)), e', ?_⟩
  change eJ.hom ≫ (Sigma.reindex ρ T').inv ≫ Sigma.desc j' = f
  have hReindex : (Sigma.reindex ρ T').inv ≫ Sigma.desc j' = Sigma.desc q' := by
    refine Sigma.hom_ext _ _ fun j => ?_
    have hidx : ρ (ρ.symm j) = j := Equiv.apply_symm_apply ρ j
    rw [← hidx, ← Category.assoc,
      CategoryTheory.Limits.Sigma.ι_reindex_inv ρ T' (ρ.symm j)]
    simp [j', q']
  have hqf : Sigma.desc q' = Sigma.desc s' ≫ f :=
    Sigma.hom_ext _ _ fun j => by simp [q', s', q]
  rw [hReindex, hqf, ← Category.assoc, heJ, Category.id_comp]

/-- **Stacks Project, Tag 09ZA, final assertion.** A surjective finite etale morphism over a
closed subscheme of an integral normal affine scheme with separably closed function field has a
section. -/
@[stacks 09ZA "section"]
theorem exists_section_of_surjective_finite_etale
    (X : Scheme.{u}) [IsAffine X] [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
    (V : Scheme.{u}) [IsAffine V] (f : V ⟶ Z)
    [Surjective f] [IsFinite f] [Etale f] :
    ∃ s : Z ⟶ V, s ≫ f = 𝟙 Z :=
  by
  classical
  obtain ⟨n, U, j, hj, e, he⟩ :=
    exists_finite_coproduct_open_immersions X Z i V f
  let m (a : Fin n) : U a ⟶ V := Sigma.ι U a ≫ e.inv
  have hmRange (a : Fin n) : IsClosed (Set.range (m a)) := by
    have hSigma : IsClosed (Set.range (Sigma.ι U a)) := by
      let cover := AlgebraicGeometry.sigmaOpenCover U
      have hrange (b : Fin n) : IsOpen (Set.range (Sigma.ι U b)) := by
        simpa [Scheme.Hom.opensRange] using (Sigma.ι U b).opensRange.2
      have hcomp : (Set.range (Sigma.ι U a))ᶜ =
          ⋃ b : Fin n, if b ≠ a then Set.range (Sigma.ι U b) else ∅ := by
        ext x
        constructor
        · intro hxa
          have hcov := cover.covers x
          let b : Fin n := cover.idx x
          change x ∈ Set.range (Sigma.ι U b) at hcov
          have hba : b ≠ a := by
            intro h
            have hxa' : x ∈ Set.range (Sigma.ι U a) := by
              rw [h] at hcov
              exact hcov
            exact hxa hxa'
          obtain ⟨y, hy⟩ := hcov
          exact Set.mem_iUnion.mpr ⟨b, by
            rw [ite_eq_left hba]
            exact ⟨y, hy⟩⟩
        · intro hx hxa
          obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
          by_cases hba : b = a
          · simp [hba] at hb
          · have hb' : x ∈ Set.range (Sigma.ι U b) := by simpa [hba] using hb
            obtain ⟨y, hy⟩ := hb'
            obtain ⟨z, hz⟩ := hxa
            have hEq : Sigma.ι U a z = Sigma.ι U b y := hz.trans hy.symm
            have hidx := congrArg Sigma.fst ((sigmaι_eq_iff U a b z y).mp hEq)
            exact hba hidx.symm
      have hopen : IsOpen ((Set.range (Sigma.ι U a))ᶜ) := by
        rw [hcomp]
        exact isOpen_iUnion fun b => by
          by_cases hba : b ≠ a
          · simpa [hba] using hrange b
          · simp [hba]
      simpa using hopen.isClosed_compl
    have hEq : Set.range (m a) =
        Scheme.homeoOfIso e.symm '' Set.range (Sigma.ι U a) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨Sigma.ι U a y, ⟨y, rfl⟩, by simp [m]⟩
      · rintro ⟨y, ⟨z, rfl⟩, hx⟩
        exact ⟨z, by simpa [m] using hx⟩
    rw [hEq]
    exact (Scheme.homeoOfIso e.symm).isClosedMap _ hSigma
  have : UniversallyClosed f := inferInstance
  have hjfactor (a : Fin n) : m a ≫ f = j a := by
    have he' : e.inv ≫ f = Sigma.desc j := by
      rw [← he]
      simp
    dsimp [m]
    rw [Category.assoc, he', Sigma.ι_desc]
  have hjClosed (a : Fin n) : IsClosed ((j a).opensRange : Set Z) := by
    have hEq : Set.range (j a) = f '' Set.range (m a) := by
      rw [← Set.range_comp]
      change Set.range (j a).base = Set.range (m a ≫ f).base
      exact congrArg (fun g : U a ⟶ Z => Set.range g.base) (hjfactor a).symm
    have hclosed : IsClosed (Set.range (j a)) := by
      rw [hEq]
      exact f.isClosedMap _ (hmRange a)
    simpa [Scheme.Hom.opensRange] using hclosed
  let P (a : Fin n) : Z.Opens :=
    ⟨⋃ b : Fin n, if b < a then (j b).opensRange else ∅,
      isOpen_iUnion fun b => by
        by_cases hba : b < a
        · simpa [hba] using (j b).opensRange.2
        · simp [hba]⟩
  have hPClosed (a : Fin n) : IsClosed (P a : Set Z) := by
    change IsClosed (⋃ b : Fin n, if b < a then ((j b).opensRange : Set Z) else ∅)
    apply isClosed_iUnion_of_finite
    intro b
    by_cases hba : b < a
    · simpa [hba] using hjClosed b
    · simp [hba]
  let O (a : Fin n) : Z.Opens :=
    ⟨(j a).opensRange \ P a, (j a).opensRange.2.sdiff (hPClosed a)⟩
  have hOsub (a : Fin n) : O a ≤ (j a).opensRange := by
    intro x hx
    exact hx.1
  have hOdisj : Pairwise (fun a b => Disjoint (O a) (O b)) := by
    intro a b hab
    rw [disjoint_iff, TopologicalSpace.Opens.ext_iff]
    ext x
    constructor
    · rintro ⟨hxa, hxb⟩
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · have hxprev : x ∈ P b := by
          change x ∈ ⋃ c : Fin n, if c < b then ((j c).opensRange : Set Z) else ∅
          have hmem : x ∈ ((j a).opensRange : Set Z) := hOsub a hxa
          exact Set.mem_iUnion.mpr ⟨a, by simpa [hlt] using hmem⟩
        exact hxb.2 hxprev
      · have hxprev : x ∈ P a := by
          change x ∈ ⋃ c : Fin n, if c < a then ((j c).opensRange : Set Z) else ∅
          have hmem : x ∈ ((j b).opensRange : Set Z) := hOsub b hxb
          exact Set.mem_iUnion.mpr ⟨b, by simpa [hgt] using hmem⟩
        exact hxa.2 hxprev
    · intro hx
      exact False.elim hx
  have hJcover : ⨆ a, (j a).opensRange = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨v, hv⟩ :=
      (show Function.Surjective f.base from (show Surjective f from inferInstance).surj) x
    let cover := AlgebraicGeometry.sigmaOpenCover U
    let a := cover.idx (e.hom v)
    have hcov : e.hom v ∈ Set.range (Sigma.ι U a) := cover.covers (e.hom v)
    obtain ⟨y, hy'⟩ := hcov
    have hval : (j a) y = x := by
      calc
        (j a) y = (Sigma.desc j) (Sigma.ι U a y) :=
          (congrArg (fun g : U a ⟶ Z => g y) (Sigma.ι_desc j a)).symm
        _ = (e.hom ≫ Sigma.desc j) v := by rw [hy']; rfl
        _ = f v := congrArg (fun g : V ⟶ Z => g v) he
        _ = x := hv
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨a, Set.mem_range.mpr ⟨y, hval⟩⟩
  have hOcover : ⨆ a, O a = ⊤ := by
    apply top_unique
    intro x hx
    have hxJ : x ∈ ⨆ a, (j a).opensRange := by simp [hJcover]
    obtain ⟨a, ha⟩ := (TopologicalSpace.Opens.mem_iSup).1 hxJ
    let F : Finset (Fin n) := Finset.univ.filter fun b => x ∈ (j b).opensRange
    have hF : F.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    let b := F.min' hF
    have hbF : b ∈ F := Finset.min'_mem F hF
    refine (TopologicalSpace.Opens.mem_iSup).2 ⟨b, ?_⟩
    constructor
    · exact (Finset.mem_filter.mp hbF).2
    · intro hprev
      change x ∈ ⋃ c : Fin n, if c < b then ((j c).opensRange : Set Z) else ∅ at hprev
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hprev
      have hclt : c < b := by
        by_contra hnot
        simp [hnot] at hc
      have hcmem : x ∈ (j c).opensRange := by simpa [hclt] using hc
      have hc' : c ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcmem⟩
      have hle : b ≤ c := Finset.min'_le F c hc'
      exact (not_lt_of_ge hle) hclt
  let t (a : Fin n) : (O a).toScheme ⟶ V :=
    Z.homOfLE (hOsub a) ≫ (j a).isoOpensRange.inv ≫ m a
  have ht (a : Fin n) : t a ≫ f = (O a).ι := by
    dsimp [t]
    calc
      _ = Z.homOfLE (hOsub a) ≫ ((j a).isoOpensRange.inv ≫ (m a ≫ f)) := by simp [Category.assoc]
      _ = Z.homOfLE (hOsub a) ≫ ((j a).isoOpensRange.inv ≫ j a) := by rw [hjfactor]
      _ = Z.homOfLE (hOsub a) ≫ (j a).opensRange.ι := by
        rw [Scheme.Hom.isoOpensRange_inv_comp]
      _ = (O a).ι := Scheme.homOfLE_ι _ _
  have hcol : Nonempty (IsColimit (Cofan.mk Z (fun a : Fin n => (O a).ι))) :=
    nonempty_isColimit_cofanMk_of (fun a : Fin n => (O a).ι)
      (by simpa only [Scheme.Opens.opensRange_ι] using hOcover)
      (by simpa only [Scheme.Opens.opensRange_ι] using hOdisj)
  have : IsIso (Sigma.desc (fun a : Fin n => (O a).ι)) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk Z (fun a : Fin n => (O a).ι))).mp hcol
  let eO : Z ≅ ∐ fun a : Fin n => (O a).toScheme :=
    (asIso (Sigma.desc (fun a : Fin n => (O a).ι))).symm
  have heO : eO.hom ≫ Sigma.desc (fun a : Fin n => (O a).ι) = 𝟙 Z := eO.hom_inv_id
  refine ⟨eO.hom ≫ Sigma.desc t, ?_⟩
  have hdesc : Sigma.desc t ≫ f = Sigma.desc (fun a : Fin n => (O a).ι) := by
    apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc]
    exact ht a
  rw [Category.assoc, hdesc, heO]

section FirstCohomology

open Opposite Stacks.Cohomology.Torsors

universe v w t

/-- First cohomology of an abelian sheaf vanishes as soon as every torsor under it has a global
section, because the isomorphism classes of torsors are exactly the first cohomology classes. -/
private theorem subsingleton_sheafH1_of_torsors_globalSections
    {C : Type v} [Category.{t} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{u} (Sheaf J AddCommGrpCat.{w})]
    (H : Sheaf J AddCommGrpCat.{w})
    (h : ∀ F : AbelianTorsor H, Nonempty (GlobalSections F.1.presheaf)) :
    Subsingleton (Sheaf.H H 1) := by
  have hz : ∀ x : torsorIsoClasses H, torsorIsoClassesEquivH1 H x = 0 := by
    intro x
    induction x using Quotient.inductionOn with
    | h F =>
      rw [← (torsor_class_eq_trivial_iff H F).2 (h F)]
      exact torsorIsoClassesEquivH1_trivial H
  refine ⟨fun x y => ?_⟩
  rw [← (torsorIsoClassesEquivH1 H).apply_symm_apply x,
    ← (torsorIsoClassesEquivH1 H).apply_symm_apply y, hz, hz]

/-- Every covering sieve of the small étale site is jointly surjective on points: some member
of the sieve has the given point of its target in its image. -/
private alias exists_mem_arrows_mem_range_smallEtale := SmallEtale.exists_mem_arrows_mem_range

section ConstantCoefficients

variable {C : Type v} [Category.{t} C] (J : GrothendieckTopology C)

/-- The unit of the constant sheaf on an abelian group `M`, read as a map of presheaves of sets
into the sheaf of multiplicatively written groups underlying that constant sheaf. -/
private noncomputable def constantGroupUnit (M : AddCommGrpCat.{max v t})
    [HasSheafify J AddCommGrpCat.{max v t}] :
    (Functor.const Cᵒᵖ).obj (Multiplicative M) ⟶
      (abelianSheafAsGroupSheaf ((constantSheaf J AddCommGrpCat.{max v t}).obj M)).presheaf where
  app U := ↾fun a => Multiplicative.ofAdd
    ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U (Multiplicative.toAdd a))
  naturality := by
    intro U V f
    ext a
    change Multiplicative.ofAdd
        ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app V (Multiplicative.toAdd a)) =
      Multiplicative.ofAdd ((sheafify J ((Functor.const Cᵒᵖ).obj M)).map f
        ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U (Multiplicative.toAdd a)))
    congr 1
    exact congrArg (fun q => q (Multiplicative.toAdd a))
      ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).naturality f)

/-- The unit of a constant sheaf of abelian groups is locally injective. -/
private theorem isLocallyInjective_constantGroupUnit (M : AddCommGrpCat.{max v t})
    [HasSheafify J AddCommGrpCat.{max v t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}] :
    Presheaf.IsLocallyInjective J (constantGroupUnit J M) := by
  refine ⟨fun {U} x y h => ?_⟩
  have h' : (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U (Multiplicative.toAdd x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U (Multiplicative.toAdd y) :=
    congrArg Multiplicative.toAdd h
  refine J.superset_covering (fun V f hf => ?_)
    ((inferInstance :
      Presheaf.IsLocallyInjective J (toSheafify J ((Functor.const Cᵒᵖ).obj M))).equalizerSieve_mem
        (Multiplicative.toAdd x) (Multiplicative.toAdd y) h')
  exact congrArg Multiplicative.ofAdd hf

/-- The unit of a constant sheaf of abelian groups is locally surjective. -/
private theorem isLocallySurjective_constantGroupUnit (M : AddCommGrpCat.{max v t})
    [HasSheafify J AddCommGrpCat.{max v t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}] :
    Presheaf.IsLocallySurjective J (constantGroupUnit J M) := by
  refine ⟨fun {U} x => ?_⟩
  refine J.superset_covering (fun V f hf => ?_)
    ((inferInstance :
      Presheaf.IsLocallySurjective J
        (toSheafify J ((Functor.const Cᵒᵖ).obj M))).imageSieve_mem (Multiplicative.toAdd x))
  obtain ⟨a, ha⟩ := hf
  exact ⟨Multiplicative.ofAdd a, congrArg Multiplicative.ofAdd ha⟩

/-- A section of a torsor under a constant sheaf of abelian groups over an object `V`
identifies the restriction of the torsor to the localized site at `V` with the constant sheaf
of sets on the group. -/
private theorem nonempty_constantSheafIso_overPullback_of_section
    [HasSheafify J AddCommGrpCat.{max v t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]
    (M : AddCommGrpCat.{max v t})
    (F : AbelianTorsor ((constantSheaf J AddCommGrpCat.{max v t}).obj M))
    (V : C) (s : F.1.presheaf.obj (op V)) :
    Nonempty ((constantSheaf (J.over V) (Type (max v t))).obj (Multiplicative M) ≅
      (J.overPullback (Type (max v t)) V).obj ⟨F.1.presheaf, F.1.isSheaf⟩) := by
  obtain ⟨φ, hφ⟩ := (PseudoTorsor.isTrivial_over_iff F.1 V).2 ⟨s⟩
  have hiso : IsIso φ.hom := hφ
  have h1 : Presheaf.IsLocallyInjective (J.over V)
      ((Over.forget V).op.whiskerLeft (constantGroupUnit J M)) := by
    have := isLocallyInjective_constantGroupUnit J M
    exact Presheaf.isLocallyInjective_whisker (J.over V) J (Over.forget V) _
  have h2 : Presheaf.IsLocallySurjective (J.over V)
      ((Over.forget V).op.whiskerLeft (constantGroupUnit J M)) := by
    have := isLocallySurjective_constantGroupUnit J M
    exact Presheaf.isLocallySurjective_whisker (J.over V) J (Over.forget V) _
  let χ : (Over.forget V).op ⋙
      (abelianSheafAsGroupSheaf ((constantSheaf J AddCommGrpCat.{max v t}).obj M)).presheaf ⟶
      (Over.forget V).op ⋙ F.1.presheaf := φ.hom
  have hχ : IsIso χ := hiso
  let ψ := (Over.forget V).op.whiskerLeft (constantGroupUnit J M) ≫ χ
  have h1' : Presheaf.IsLocallyInjective (J.over V) ψ := by
    have := h1
    have := hχ
    infer_instance
  have h2' : Presheaf.IsLocallySurjective (J.over V) ψ := by
    have := h2
    have := hχ
    infer_instance
  have hsheaf : IsIso (toSheafify J F.1.presheaf) := isIso_toSheafify J F.1.isSheaf
  let ε : (presheafToSheaf J (Type (max v t))).obj F.1.presheaf ≅
      (⟨F.1.presheaf, F.1.isSheaf⟩ : Sheaf J (Type (max v t))) :=
    (sheafToPresheaf J (Type (max v t))).preimageIso
      (asIso (toSheafify J F.1.presheaf)).symm
  exact ⟨Stacks.ConstantSheaf.constantSheafObjIsoOverPullback J V ψ h1' h2' ≪≫
    (J.overPullback (Type (max v t)) V).mapIso ε⟩

/-- The sheaf of sets underlying a torsor under a finite constant sheaf of abelian groups is
finite locally constant: a torsor has sections on a covering, and a section trivializes it. -/
private theorem isFiniteLocallyConstant_torsor
    [HasSheafify J AddCommGrpCat.{max v t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]
    (M : AddCommGrpCat.{max v t}) [Finite M]
    (F : AbelianTorsor ((constantSheaf J AddCommGrpCat.{max v t}).obj M)) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant J
      (⟨F.1.presheaf, F.1.isSheaf⟩ : Sheaf J (Type (max v t))) := by
  classical
  refine ⟨fun U => ?_⟩
  obtain ⟨S, hS, hne⟩ := F.2 U
  refine ⟨Σ V : C, {f : V ⟶ U // S f}, fun a => a.1, fun a => a.2.1, ?_, fun a => ?_⟩
  · refine J.superset_covering (fun V f hf => ?_) hS
    exact Sieve.ofArrows_mk (fun a : Σ V : C, {f : V ⟶ U // S f} => a.1)
      (fun a => a.2.1) ⟨V, f, hf⟩
  · obtain ⟨s⟩ := hne a.2.2
    exact ⟨Multiplicative M, inferInstance,
      nonempty_constantSheafIso_overPullback_of_section J M F a.1 s⟩

end ConstantCoefficients

section SmallEtaleSite

variable (B : BigEtaleSite.{u}) (Z : Scheme.{u}) (hZ : B.Contains Z)

/-- Weak equivalences of abelian sheaves on the small étale site are the locally bijective
morphisms, the site being essentially small. -/
private theorem wEqualsLocallyBijective_smallEtale
    [HasSheafify (SmallEtale.topology B Z hZ) AddCommGrpCat.{u + 1}] :
    (SmallEtale.topology B Z hZ).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  have : EssentiallySmall.{u + 1} (SmallEtale B Z hZ) :=
    essentiallySmallSelf.{u, u, u + 1} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- A morphism of the small étale site to the final object is, on underlying schemes, the
structure morphism of its source. -/
private theorem toScheme_map_eq_of_hom_final {W : SmallEtale B Z hZ}
    (g : W ⟶ SmallEtale.final B Z hZ) :
    (SmallEtale.toScheme B Z hZ).map g = B.inclusion.map W.obj.hom := by
  have h := Stacks.EtaleCohomology.toScheme_map_comp_hom B hZ g
  have h0 : B.inclusion.map (SmallEtale.final B Z hZ).obj.hom = 𝟙 _ :=
    B.inclusion.map_id _
  rw [h0] at h
  exact (Category.comp_id _).symm.trans h

/-- An object of the small étale site representing a sheaf which has sections locally over
every object has surjective structure morphism. -/
private theorem surjective_hom_of_sheafifiedYonedaIso
    (U : SmallEtale B Z hZ) (P : Sheaf (SmallEtale.topology B Z hZ) (Type (u + 1)))
    (hP : ∀ V : SmallEtale B Z hZ, ∃ S ∈ SmallEtale.topology B Z hZ V,
      ∀ ⦃W : SmallEtale B Z hZ⦄ ⦃g : W ⟶ V⦄, S g → Nonempty (P.obj.obj (op W)))
    (e : P ≅ (Sheaf.sheafifiedYoneda (SmallEtale.topology B Z hZ)).obj U) :
    Surjective (B.inclusion.map U.obj.hom) := by
  classical
  obtain ⟨S, hS, hne⟩ := hP (SmallEtale.final B Z hZ)
  refine ⟨fun z => ?_⟩
  obtain ⟨W, g, hgS, w, hw⟩ := exists_mem_arrows_mem_range_smallEtale B Z hZ hS z
  obtain ⟨s⟩ := hne hgS
  have hx := Presheaf.imageSieve_mem (SmallEtale.topology B Z hZ)
    (toSheafify (SmallEtale.topology B Z hZ)
      (uliftYoneda.{u + 1}.obj U)) (e.hom.hom.app (op W) s)
  obtain ⟨W', g', hg', w', hw'⟩ := exists_mem_arrows_mem_range_smallEtale B Z hZ hx w
  obtain ⟨a, -⟩ := hg'
  refine ⟨(SmallEtale.toScheme B Z hZ).map a.down w', ?_⟩
  have h1 := Stacks.EtaleCohomology.toScheme_map_comp_hom B hZ a.down
  have h2 := toScheme_map_eq_of_hom_final B Z hZ (g' ≫ g)
  have h3 := (congrArg (fun p => (SmallEtale.toScheme B Z hZ).map g p) hw').trans hw
  have h4 : ((SmallEtale.toScheme B Z hZ).map a.down ≫ B.inclusion.map U.obj.hom) w' = z := by
    rw [h1, ← h2, (SmallEtale.toScheme B Z hZ).map_comp]
    exact (Scheme.Hom.comp_apply _ _ w').trans h3
  exact (Scheme.Hom.comp_apply _ _ w').symm.trans h4

/-- A section of the structure morphism of an object of the small étale site is a morphism from
the final object of that site. -/
private noncomputable def homFinalOfSection (U : SmallEtale B Z hZ)
    (s : Z ⟶ (SmallEtale.toScheme B Z hZ).obj U)
    (hs : s ≫ B.inclusion.map U.obj.hom = 𝟙 Z) :
    SmallEtale.final B Z hZ ⟶ U :=
  Stacks.EtaleCohomology.mkHom B hZ (V := SmallEtale.final B Z hZ) (W := U) s (by
    have h0 : B.inclusion.map (SmallEtale.final B Z hZ).obj.hom = 𝟙 _ :=
      B.inclusion.map_id _
    rw [h0]
    exact hs)

end SmallEtaleSite

/-- Stacks 09ZB over the effective-descent hypothesis `h0245`.  The unconditional statement is
`AlgebraicGeometry.subsingleton_smallEtaleH1_constantSheaf'`, which is where the tag sits: the
hypothesis is now a theorem of this library, reached through
`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable`. -/
theorem subsingleton_smallEtaleH1_constantSheaf
    (B : BigEtaleSite.{u})
    (X : Scheme.{u}) [IsAffine X] [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] (hZ : B.Contains Z)
    (M : AddCommGrpCat.{u + 1}) [Finite M]
    (h0245 : Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability B)
    [HasSheafify (SmallEtale.topology B Z hZ) AddCommGrpCat.{u + 1}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B Z hZ) AddCommGrpCat.{u + 1})] :
    Subsingleton (Sheaf.H ((constantSheaf (SmallEtale.topology B Z hZ)
      AddCommGrpCat.{u + 1}).obj M) 1) := by
  classical
  have hJ := wEqualsLocallyBijective_smallEtale B Z hZ
  have hZaff : IsAffine Z := isAffine_of_isAffineHom i
  apply subsingleton_sheafH1_of_torsors_globalSections
  intro F
  have hflc := isFiniteLocallyConstant_torsor (SmallEtale.topology B Z hZ) M F
  obtain ⟨U, hUfin, ⟨e⟩⟩ :=
    (Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable_of_descent
      B (B.obj Z hZ) ⟨F.1.presheaf, F.1.isSheaf⟩ h0245).mp hflc
  have hfin : IsFinite (B.inclusion.map U.obj.hom) := hUfin
  have htgt : IsAffine (B.inclusion.obj (B.obj Z hZ)) := inferInstanceAs (IsAffine Z)
  have hUaff : IsAffine ((SmallEtale.toScheme B Z hZ).obj U) :=
    isAffine_of_isAffineHom (B.inclusion.map U.obj.hom)
  have hsurj : Surjective (B.inclusion.map U.obj.hom) :=
    surjective_hom_of_sheafifiedYonedaIso B Z hZ U ⟨F.1.presheaf, F.1.isSheaf⟩
      (fun V => by
        obtain ⟨S, hS, hne⟩ := F.2 V
        exact ⟨S, hS, hne⟩) e
  obtain ⟨s, hs⟩ := exists_section_of_surjective_finite_etale X Z i
    ((SmallEtale.toScheme B Z hZ).obj U) (B.inclusion.map U.obj.hom)
  exact nonempty_globalSections_of_isTrivial F.1
    (PseudoTorsor.isTrivial_of_terminal_section (SmallEtale.finalIsTerminal B Z hZ) F.1
      (Sheaf.sectionEquiv (SmallEtale.topology B Z hZ)
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B Z hZ)).map
          (homFinalOfSection B Z hZ U s hs) ≫ e.inv)))

/-- **Stacks Project, Tag 09ZB.** The first cohomology of the small étale site of a closed
subscheme of an integral normal affine scheme with separably closed function field, with
coefficients in a finite constant abelian group, vanishes.

This is `AlgebraicGeometry.subsingleton_smallEtaleH1_constantSheaf` with its descent hypothesis
discharged: a torsor under the constant sheaf is finite locally constant, hence representable by
a scheme finite étale over `Z` by the unconditional
`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable`, and that scheme
has a section because `Z` is a closed subscheme of a normal integral affine scheme with
separably closed function field. -/
@[stacks 09ZB]
theorem subsingleton_smallEtaleH1_constantSheaf'
    (B : BigEtaleSite.{u})
    (X : Scheme.{u}) [IsAffine X] [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] (hZ : B.Contains Z)
    (M : AddCommGrpCat.{u + 1}) [Finite M]
    [HasSheafify (SmallEtale.topology B Z hZ) AddCommGrpCat.{u + 1}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B Z hZ) AddCommGrpCat.{u + 1})] :
    Subsingleton (Sheaf.H ((constantSheaf (SmallEtale.topology B Z hZ)
      AddCommGrpCat.{u + 1}).obj M) 1) := by
  exact subsingleton_smallEtaleH1_constantSheaf B X Z i hZ M
    (Stacks.EtaleCohomology.etaleDescentForFiniteEtaleRepresentability B)

end FirstCohomology

section HigherCohomology

open IsLocalRing

universe w

/-! ### Strictly henselian local rings on a closed subscheme -/

/-- A henselian local ring stays henselian along a surjective local homomorphism: a monic
polynomial over the target lifts to a monic polynomial over the source, Hensel's lemma produces
a root there, and its image is the root asked for. -/
private theorem henselianLocalRing_of_surjective
    {A D : Type*} [CommRing A] [CommRing D] [HenselianLocalRing A] [IsLocalRing D]
    (f : A →+* D) [hlh : IsLocalHom f] (hf : Function.Surjective f) :
    HenselianLocalRing D := by
  have hmap : ∀ (p : Polynomial A) (x : A), f (p.eval x) = (p.map f).eval (f x) :=
    fun p x => by rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  refine ⟨fun g hg a₀ ha₀ hunit => ?_⟩
  obtain ⟨G, hGmap, -, hGmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts g).mpr fun n => ⟨_, (hf (g.coeff n)).choose_spec⟩) hg
  obtain ⟨r, hr⟩ := hf a₀
  have hmem : G.eval r ∈ maximalIdeal A := by
    rw [← maximalIdeal_comap f, Ideal.mem_comap, hmap, hGmap, hr]
    exact ha₀
  have hunit' : IsUnit ((Polynomial.derivative G).eval r) := by
    refine hlh.map_nonunit _ ?_
    rw [hmap, ← Polynomial.derivative_map, hGmap, hr]
    exact hunit
  obtain ⟨a, haroot, hasub⟩ := HenselianLocalRing.is_henselian G hGmonic r hmem hunit'
  refine ⟨f a, ?_, ?_⟩
  · rw [Polynomial.IsRoot, ← hGmap, ← hmap, haroot, map_zero]
  · rw [← hr, ← map_sub, ← Ideal.mem_comap, maximalIdeal_comap]
    exact hasub

/-- **A strictly henselian local ring stays strictly henselian along a surjective local
homomorphism**, Stacks 05WS: the target is henselian, and the induced map of residue fields is
bijective, so the residue field of the target is again separably closed. -/
private theorem strictlyHenselianLocalRing_of_surjective
    {A D : Type*} [CommRing A] [CommRing D] [StrictlyHenselianLocalRing A]
    [IsLocalRing D] (f : A →+* D) [IsLocalHom f]
    (hf : Function.Surjective f) : StrictlyHenselianLocalRing D := by
  have : HenselianLocalRing D := henselianLocalRing_of_surjective f hf
  have hres : Function.Bijective (ResidueField.map f) := by
    refine ⟨(ResidueField.map f).injective, fun y => ?_⟩
    obtain ⟨d, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hf d
    exact ⟨residue A a, ResidueField.map_residue f a⟩
  have : IsSepClosed (ResidueField D) :=
    IsSepClosed.of_ringEquiv (RingEquiv.ofBijective _ hres).symm
  exact ⟨⟩

/-- **Every local ring of a closed subscheme of an integral normal scheme with separably closed
function field is strictly henselian.** The local rings of the ambient scheme are strictly
henselian, and the stalk maps of a closed immersion are surjective local homomorphisms. -/
theorem stalk_strictlyHenselian_of_isClosedImmersion {X Z : Scheme.{u}} [IsIntegral X]
    [IsNormal X] [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    StrictlyHenselianLocalRing (Z.presheaf.stalk z) := by
  have : StrictlyHenselianLocalRing (X.presheaf.stalk (i z)) := stalk_strictlyHenselian X (i z)
  exact strictlyHenselianLocalRing_of_surjective (i.stalkMap z).hom (i.stalkMap_surjective z)

/-! ### Basic opens of a closed subscheme -/

/-- An integral scheme open in an integral scheme with separably closed function field has
separably closed function field: an open immersion carries the generic point to the generic
point and is an isomorphism on stalks, and the function field is the stalk at the generic
point. -/
private theorem isSepClosed_functionField_of_isOpenImmersion {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsSepClosed Y.functionField] (j : X ⟶ Y) [IsOpenImmersion j] :
    IsSepClosed X.functionField := by
  have hη : j (genericPoint X) = genericPoint Y := genericPoint_eq_of_isOpenImmersion j
  have e : X.functionField ≅ Y.functionField :=
    (asIso (j.stalkMap (genericPoint X))).symm.trans (eqToIso (congrArg Y.presheaf.stalk hη))
  exact IsSepClosed.of_ringEquiv e.commRingCatIsoToRingEquiv

/-- **A basic open of a closed subscheme of an affine scheme is a closed subscheme of a basic
open of the ambient scheme.** The defining function lifts along the surjection on global
sections, and the restricted morphism is a base change of the given closed immersion along the
inclusion of the ambient basic open. -/
private theorem exists_isClosedImmersion_resLE_basicOpen {X Z : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : Γ(Z, ⊤)) :
    ∃ (g : Γ(X, ⊤)) (hle : Z.basicOpen f ≤ i ⁻¹ᵁ X.basicOpen g),
      IsClosedImmersion (i.resLE (X.basicOpen g) (Z.basicOpen f) hle) := by
  have : IsAffine Z := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  obtain ⟨g, hg⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine i).2 f
  have hpre : i ⁻¹ᵁ X.basicOpen g = Z.basicOpen f := by
    rw [Scheme.Hom.preimage_basicOpen]
    exact congrArg Z.basicOpen hg
  refine ⟨g, le_of_eq hpre.symm, ?_⟩
  have hpb : IsPullback (i.resLE (X.basicOpen g) (Z.basicOpen f) (le_of_eq hpre.symm))
      (Z.basicOpen f).ι (X.basicOpen g).ι i := by
    refine IsOpenImmersion.isPullback _ (Z.basicOpen f).ι (X.basicOpen g).ι i
      (Scheme.Hom.resLE_comp_ι i (le_of_eq hpre.symm)).symm ?_
    simpa only [Scheme.Opens.opensRange_ι] using hpre
  exact IsClosedImmersion.isStableUnderBaseChange.of_isPullback hpb.flip inferInstance

/-! ### Vanishing in all positive degrees -/

/-- Stacks 09ZC over the effective-descent hypothesis `h0245`.  The unconditional statement is
`AlgebraicGeometry.subsingleton_smallEtaleH_constantSheaf'`, which is where the tag sits: the
hypothesis is now a theorem of this library, reached through
`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable`. -/
theorem subsingleton_smallEtaleH_constantSheaf
    (B : BigEtaleSite.{u})
    (X : Scheme.{u}) [IsAffine X] [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] (hZ : B.Contains Z)
    (M : AddCommGrpCat.{u + 1}) [Finite M]
    (h0245 : Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability B)
    [HasSheafify (SmallEtale.topology B Z hZ) AddCommGrpCat.{u + 1}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B Z hZ) AddCommGrpCat.{u + 1})]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H ((constantSheaf (SmallEtale.topology B Z hZ)
      AddCommGrpCat.{u + 1}).obj M) q) := by
  have hZaff : IsAffine Z := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  have hbo : ∀ f : Γ(Z, ⊤), B.Contains (Z.basicOpen f).toScheme := fun f =>
    (Scheme.size_coe_opens_le Z (Z.basicOpen f)).trans_lt hZ
  set S : Scheme.{u} := Spec (CommRingCat.of ↥Γ(Z, ⊤)) with hSdef
  let F := (constantSheaf (Stacks.EtaleCohomology.MayerVietoris.topology S)
    AddCommGrpCat.{u + 1}).obj M
  have h1 : ∀ b : ↥Γ(Z, ⊤), Subsingleton
      ((Stacks.EtaleCohomology.StrictlyHenselian.opensCohomology F 1).obj
        (Opposite.op (PrimeSpectrum.basicOpen b))) := by
    intro b
    have : HasExt.{u + 1} (Sheaf (SmallEtale.topology B (Z.basicOpen b).toScheme (hbo b))
        AddCommGrpCat.{u + 1}) := smallEtaleSheaf_hasExt B _ (hbo b)
    refine Stacks.EtaleCohomology.ConstantTransport.subsingleton_H'_opensToSite S
      (PrimeSpectrum.basicOpen b) M 1 ?_
    refine Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_mayerVietoris_of_smallEtale
      _ M 1 ?_
    refine Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_smallEtale_of_iso
      (Z.isoOfEq (Scheme.map_PrimeSpectrum_basicOpen_of_affine Z b).symm ≪≫
        Stacks.EtaleCohomology.ConstantTransport.preimageOpensIsoOfIsIso Z.isoSpec.hom
          (PrimeSpectrum.basicOpen b)) M 1 ?_
    refine
      Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_smallEtale_of_boundedSmallEtale
        B (Z.basicOpen b).toScheme (hbo b) M 1 ?_
    by_cases hne : Nonempty (Z.basicOpen b).toScheme
    · obtain ⟨g, hle, hclosed⟩ := exists_isClosedImmersion_resLE_basicOpen i b
      have hXne : Nonempty (X.basicOpen g).toScheme :=
        ⟨i.resLE (X.basicOpen g) (Z.basicOpen b) hle hne.some⟩
      have : IsAffine (X.basicOpen g).toScheme := (isAffineOpen_top X).basicOpen g
      have : IsIntegral (X.basicOpen g).toScheme :=
        isIntegral_of_isOpenImmersion (X.basicOpen g).ι
      have : IsNormal (X.basicOpen g).toScheme := isNormal_open (X.basicOpen g)
      have : IsSepClosed (X.basicOpen g).toScheme.functionField :=
        isSepClosed_functionField_of_isOpenImmersion (X.basicOpen g).ι
      exact subsingleton_smallEtaleH1_constantSheaf B (X.basicOpen g).toScheme
        (Z.basicOpen b).toScheme (i.resLE (X.basicOpen g) (Z.basicOpen b) hle) (hbo b) M h0245
    · have : IsEmpty (Z.basicOpen b).toScheme := not_nonempty_iff.mp hne
      exact subsingleton_smallEtaleH1_constantSheaf B X
        (Z.basicOpen b).toScheme ((Z.basicOpen b).ι ≫ i) (hbo b) M h0245
  have hlocal : ∀ x : S, StrictlyHenselianLocalRing (S.presheaf.stalk x) :=
    stalk_strictlyHenselian_of_isClosedImmersion (Z.isoSpec.inv ≫ i)
  have h0GY0 :=
    Stacks.EtaleCohomology.StrictlyHenselian.subsingleton_H_of_degreeOne_kernel_eq_zero
      hlocal F (fun f g y _ _ => (h1 (f + g)).elim y 0) q hq
  exact Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_boundedSmallEtale_of_smallEtale
    B Z hZ M q
    (Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_smallEtale_of_iso
      Z.isoSpec.symm M q
      (Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_smallEtale_of_mayerVietoris
        S M q h0GY0))

/-- **Stacks Project, Tag 09ZC.** The étale cohomology of a closed subscheme of a normal
integral affine scheme with separably closed function field, with coefficients in a finite
constant abelian group, vanishes in every positive degree.

This is `AlgebraicGeometry.subsingleton_smallEtaleH_constantSheaf` with its descent hypothesis
discharged: the degree-one input is the unconditional
`AlgebraicGeometry.subsingleton_smallEtaleH1_constantSheaf'` on the basic opens of `Z`, and the
passage to all positive degrees is the vanishing criterion of Stacks 0GY0. -/
@[stacks 09ZC]
theorem subsingleton_smallEtaleH_constantSheaf'
    (B : BigEtaleSite.{u})
    (X : Scheme.{u}) [IsAffine X] [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] (hZ : B.Contains Z)
    (M : AddCommGrpCat.{u + 1}) [Finite M]
    [HasSheafify (SmallEtale.topology B Z hZ) AddCommGrpCat.{u + 1}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B Z hZ) AddCommGrpCat.{u + 1})]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H ((constantSheaf (SmallEtale.topology B Z hZ)
      AddCommGrpCat.{u + 1}).obj M) q) := by
  exact subsingleton_smallEtaleH_constantSheaf B X Z i hZ M
    (Stacks.EtaleCohomology.etaleDescentForFiniteEtaleRepresentability B) q hq

end HigherCohomology

end AlgebraicGeometry

end
