module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.FreeResolution
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryProducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceQuasiIso
public import StacksFrontier.Homology.KFlat.Closure

/-!
# The K-flat resolution of a differential graded algebra, as an input to Tag 09S6

Stacks Tag 0BZ7 produces, for every differential graded `R`-algebra `(B, d)`, a quasi-isomorphic
differential graded algebra `(B', d)` which is K-flat as a complex of `R`-modules, and Stacks
Tag 09S6 turns a quasi-isomorphism of differential graded algebras into an equivalence of derived
categories. The two are formalized against different encodings of the same data, and this file is
the bridge between them.

Tag 0BZ7 (`Stacks.DGA.exists_kFlat_freeGraded_resolution`) delivers the resolution in a raw form:
an `R`-algebra homomorphism `f : B' → B` together with the *proposition*
`Stacks.DGA.IsDGAMorphism B' B f`, a pair of cochain complexes `CB'` and `CB` identified with the
graded pieces of `B'` and of `B` by a `Stacks.DGA.ModelsComplex`, K-flatness of `CB'`, and a
quasi-isomorphism `CB' ⟶ CB` compatible with `f`. Tag 09S6
(`DifferentialGraded.Bimodule.derivedExtensionEquivalence`) consumes a bundled
`DifferentialGradedAlgebra.Hom` together with the bijectivity of
`DifferentialGradedAlgebra.Hom.cohomologyMap` in every degree. Three steps close the gap, and all
three are carried out below:

1. the proposition `IsDGAMorphism` is exactly the two fields of a bundled homomorphism, so it
   bundles with no work;
2. a `ModelsComplex` *is* an isomorphism onto the cochain complex underlying the regular module,
   so the complexes of the raw form can be dispensed with and K-flatness transported to the
   canonical complex `B'^•`;
3. the cohomology `H^k(B')` of `Algebra/DifferentialGraded/Cohomology.lean` — a quotient of the
   homogeneous cocycles, with no cochain complex in sight — is bijectively compared with
   `H^k(B'^•)` along a homomorphism, which is what makes "quasi-isomorphism of complexes" and
   "bijective on cohomology algebras" the same hypothesis.

Step 3 is the one with content, and the route taken avoids computing either cohomology group.
A homomorphism `φ : (A, d) → (B, d)` is the same thing as a homomorphism
`A ⟶ B_A` of differential graded `A`-modules from the regular module to the restriction of the
regular `B`-module (`DifferentialGradedAlgebra.Hom.toRegularRestriction`), restriction of scalars
changes no cochain complex, and the cycle-and-boundary criterion
`DifferentialGradedModule.IsQuasiIsomorphism` is already known to be *equivalent* to the
underlying cochain map being a quasi-isomorphism
(`DifferentialGradedModule.isQuasiIsomorphism_of_quasiIso`). That criterion is literally the
statement that `H^k(φ)` is surjective and injective on representatives, so the comparison of the
two cohomologies is never formed: both are read through the same element-level conditions.

## Main definitions

* `DifferentialGradedAlgebra.Hom.ofIsDGAMorphism`: the bundled homomorphism of differential
  graded algebras attached to an `R`-algebra map satisfying `Stacks.DGA.IsDGAMorphism`.
* `Stacks.DGA.ModelsComplex.isoRegularCochainComplex`: a `ModelsComplex` for `(A, d)`, read as an
  isomorphism of the modelling complex with the cochain complex `A^•` underlying the regular
  differential graded `A`-module.
* `DifferentialGradedAlgebra.Hom.toRegularRestriction` and
  `DifferentialGradedAlgebra.Hom.toRegularCochainMap`: a homomorphism of differential graded
  algebras `φ : A → B`, read as a homomorphism of differential graded `A`-modules `A ⟶ B_A` and
  as a cochain map `A^• ⟶ B^•`.

## Main results

* `Stacks.DGA.ModelsComplex.kFlat_regularModule`: K-flatness of a modelling complex is
  K-flatness of `A^•`.
* `DifferentialGradedAlgebra.Hom.bijective_cohomologyMap_of_quasiIso`: **the cohomology
  bridge.** If the cochain map `A^• ⟶ B^•` underlying `φ` is a quasi-isomorphism, then `H^k(φ)`
  is bijective for every `k`, which is the hypothesis of Tag 09S6.
* `DifferentialGradedAlgebra.Hom.quasiIso_toRegularCochainMap_of_models`: the quasi-isomorphism
  of the raw form of Tag 0BZ7 is the cochain map underlying the bundled homomorphism.
* `DifferentialGradedAlgebra.exists_kFlat_resolution_bijective_cohomologyMap`: **Tag 0BZ7 in the
  encoding Tag 09S6 consumes** — a K-flat `(B', d)` and a homomorphism `B' → B` bijective on
  cohomology in every degree.
* `DifferentialGradedAlgebra.exists_kFlat_resolution_derivedEquivalence`: the resulting
  equivalence `D(B', d) ≌ D(B, d)` of Tag 09S6, in the form "`- ⊗_{B'}^𝐋 B` is an equivalence".

## Implementation notes

*Why the bridge is not an isomorphism `H^k(A) ≅ H^k(A^•)`.* Such an isomorphism, natural in the
homomorphism, is what one would build to compare the two cohomologies; it is not needed to
compare the two *hypotheses*, and only the hypotheses are wanted here and at Tag 09S6. The
element-level cycle-and-boundary criterion is the common refinement of both, and it is already
available in both directions, so the bridge below is a short quotient argument rather than a
construction of homology isomorphisms.

*Universes.* Steps 1 and 2 are stated at the universes of
`StacksFrontier/Algebra/DGA/FreeResolution.lean`, where the algebra and the complexes live in
`max u v` over a base ring in `Type u`. Step 3 and everything after it is on the diagonal
`max u u = u`, which is where the differential graded derived category of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedCategory.lean` and hence Tag 09S6 live,
following Stacks Tag 09JJ.

## References

* [Stacks Project, Tag 0BZ7](https://stacks.math.columbia.edu/tag/0BZ7), the resolution.
* [Stacks Project, Tag 09S6](https://stacks.math.columbia.edu/tag/09S6), the derived equivalence
  attached to a quasi-isomorphism of differential graded algebras.
* [Stacks Project, Tag 0BZ8](https://stacks.math.columbia.edu/tag/0BZ8), whose first half is the
  reduction of a general middle algebra to a K-flat one along these two tags.
* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI) for the cohomology of a
  differential graded algebra.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule

universe u v

/-! ### Bundling the homomorphism -/

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- **A homomorphism of differential graded algebras from the raw encoding.** The proposition
`Stacks.DGA.IsDGAMorphism A B f` of `StacksFrontier/Algebra/DGA/FreeResolution.lean` is the
conjunction of compatibility with the gradings and compatibility with the differentials, which
are the two fields of `DifferentialGradedAlgebra.Hom` beyond the `R`-algebra map itself. -/
def Hom.ofIsDGAMorphism {A B : DifferentialGradedAlgebra.{u, max u v} R} {f : A.A →ₐ[R] B.A}
    (hf : Stacks.DGA.IsDGAMorphism.{u, v} A B f) : A.Hom B where
  toAlgebraHom := f
  map_grading := hf.1
  map_d := hf.2

/-- The `R`-algebra map underlying `DifferentialGradedAlgebra.Hom.ofIsDGAMorphism hf` is
`f`. -/
@[simp] theorem Hom.ofIsDGAMorphism_toAlgebraHom
    {A B : DifferentialGradedAlgebra.{u, max u v} R} {f : A.A →ₐ[R] B.A}
    (hf : Stacks.DGA.IsDGAMorphism.{u, v} A B f) :
    (Hom.ofIsDGAMorphism hf).toAlgebraHom = f :=
  rfl

end DifferentialGradedAlgebra

/-! ### A modelling complex is the complex underlying the regular module -/

namespace Stacks.DGA

variable {R : Type u} [CommRing R]

/-- **A modelling complex is `A^•`.** A `Stacks.DGA.ModelsComplex A C` identifies the degree-`n`
term of `C` with the homogeneous component `A^n` compatibly with the differentials, which is
exactly an isomorphism of `C` with the cochain complex underlying the regular differential graded
`A`-module. -/
def ModelsComplex.isoRegularCochainComplex {A : DifferentialGradedAlgebra.{u, max u v} R}
    {C : CochainComplex (ModuleCat.{max u v} R) ℤ} (e : ModelsComplex A C) :
    C ≅ (regularModule A).toCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (e.equiv n).toModuleIso) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    rw [DifferentialGradedModule.toCochainComplex_d]
    ext x
    exact Subtype.ext (e.d_compatible i x).symm)

/-- In degree `n`, the isomorphism `C ≅ A^•` sends `x` to `e.equiv n x`. -/
@[simp] theorem ModelsComplex.isoRegularCochainComplex_hom_f_apply
    {A : DifferentialGradedAlgebra.{u, max u v} R}
    {C : CochainComplex (ModuleCat.{max u v} R) ℤ} (e : ModelsComplex A C) (n : ℤ) (x : C.X n) :
    (e.isoRegularCochainComplex.hom.f n) x = e.equiv n x :=
  rfl

/-- In degree `n`, the inverse isomorphism `A^• ≅ C` sends `x` to `(e.equiv n).symm x`. -/
@[simp] theorem ModelsComplex.isoRegularCochainComplex_inv_f_apply
    {A : DifferentialGradedAlgebra.{u, max u v} R}
    {C : CochainComplex (ModuleCat.{max u v} R) ℤ} (e : ModelsComplex A C) (n : ℤ)
    (x : A.grading n) :
    (e.isoRegularCochainComplex.inv.f n) x = (e.equiv n).symm x :=
  rfl

/-- **K-flatness of a modelling complex is K-flatness of `A^•`.** The two complexes are
isomorphic by `Stacks.DGA.ModelsComplex.isoRegularCochainComplex`, and K-flatness transports
along an isomorphism. -/
theorem ModelsComplex.kFlat_regularModule {A : DifferentialGradedAlgebra.{u, max u v} R}
    {C : CochainComplex (ModuleCat.{max u v} R) ℤ} (e : ModelsComplex A C)
    (hC : CochainComplex.KFlat.{u, v} C) :
    CochainComplex.KFlat.{u, v} (regularModule A).toCochainComplex :=
  CochainComplex.kFlat_of_iso.{u, v} e.isoRegularCochainComplex hC

end Stacks.DGA

/-! ### A homomorphism of algebras as a homomorphism of modules -/

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- **A homomorphism of differential graded algebras, read as a homomorphism of differential
graded modules `A ⟶ B_A`.** Its underlying map is that of `φ`; it is right `A`-linear because
`φ` is multiplicative and the right `A`-action on the restriction `B_A` is right multiplication
by the image of the scalar. -/
def Hom.toRegularRestriction (φ : A.Hom B) :
    DifferentialGradedModule.Hom (regularModule A) (restrictScalars φ (regularModule B)) where
  toFun := φ.toAlgebraHom.toLinearMap
  map_smul x a := map_mul φ.toAlgebraHom x a
  map_grading := φ.map_grading
  map_d := LinearMap.ext φ.map_d

/-- The underlying map of `DifferentialGradedAlgebra.Hom.toRegularRestriction φ` sends `x` to
`φ x`. -/
@[simp] theorem Hom.toRegularRestriction_toFun (φ : A.Hom B) (x : A.A) :
    φ.toRegularRestriction.toFun x = φ.toAlgebraHom x :=
  rfl

/-- **The cochain map `A^• ⟶ B^•` underlying a homomorphism of differential graded algebras.**
Restriction of scalars changes no cochain complex
(`DifferentialGradedModule.restrictScalars_toCochainComplex`), so the cochain map underlying
`DifferentialGradedAlgebra.Hom.toRegularRestriction` is a map between the complexes underlying
the two regular modules. -/
def Hom.toRegularCochainMap (φ : A.Hom B) :
    (regularModule A).toCochainComplex ⟶ (regularModule B).toCochainComplex :=
  φ.toRegularRestriction.toCochainMap

/-- In degree `n`, the cochain map `A^• ⟶ B^•` underlying `φ` is the degree-`n` graded map of
`DifferentialGradedAlgebra.Hom.toRegularRestriction φ`. -/
@[simp] theorem Hom.toRegularCochainMap_f (φ : A.Hom B) (n : ℤ) :
    φ.toRegularCochainMap.f n = ModuleCat.ofHom (φ.toRegularRestriction.gradedMap n) :=
  rfl

/-- **The cohomology bridge.** If the cochain map `A^• ⟶ B^•` underlying a homomorphism `φ` of
differential graded algebras is a quasi-isomorphism, then the induced map `H^k(φ)` of
`DifferentialGradedAlgebra.Hom.cohomologyMap` is bijective for every `k` — which is the
hypothesis of [Stacks, Tag 09S6].

Neither cohomology group is computed. The cochain map underlying `φ` is the one underlying the
homomorphism of differential graded `A`-modules `A ⟶ B_A`
(`DifferentialGradedAlgebra.Hom.toRegularRestriction`), and
`DifferentialGradedModule.isQuasiIsomorphism_of_quasiIso` converts a quasi-isomorphism into the
cycle-and-boundary criterion `DifferentialGradedModule.IsQuasiIsomorphism`: in every degree,
every cocycle of `B` is the image of a cocycle of `A` up to a coboundary, and a cocycle of `A`
whose image is a coboundary is one. Those two conditions are surjectivity and injectivity of
`H^k(φ)` on representatives. -/
theorem Hom.bijective_cohomologyMap_of_quasiIso (φ : A.Hom B)
    (hφ : QuasiIso φ.toRegularCochainMap) (k : ℤ) :
    Function.Bijective (φ.cohomologyMap k) := by
  obtain ⟨hsurj, hinj⟩ :=
    DifferentialGradedModule.isQuasiIsomorphism_of_quasiIso φ.toRegularRestriction hφ k
  constructor
  · refine Quotient.ind₂ fun a b hab => ?_
    rw [Hom.cohomologyMap_mk, Hom.cohomologyMap_mk,
      Cohomology.mk_eq_mk_iff B k] at hab
    obtain ⟨c, hc⟩ := hab
    rw [Hom.cocycleMap_val, Hom.cocycleMap_val] at hc
    obtain ⟨z, hz, hdz⟩ := hinj ((a.1 : A.A) - b.1)
      (Submodule.sub_mem _ a.1.2 b.1.2)
      (by rw [map_sub, show A.d (a.1 : A.A) = 0 from a.2,
        show A.d (b.1 : A.A) = 0 from b.2, sub_zero])
      ⟨(c : B.A), c.2, by rw [map_sub]; exact hc.symm⟩
    exact (Cohomology.mk_eq_mk_iff A k a b).mpr ⟨⟨z, hz⟩, hdz.symm⟩
  · refine Quotient.ind fun b => ?_
    obtain ⟨x, hx, hdx, z, hz, hdz⟩ := hsurj (b.1 : B.A) b.1.2 b.2
    refine ⟨Quotient.mk _ ⟨⟨x, hx⟩, hdx⟩, ?_⟩
    rw [Hom.cohomologyMap_mk, Cohomology.mk_eq_mk_iff B k]
    replace hdz : B.d z = (b.1 : B.A) - φ.toAlgebraHom x := hdz
    refine ⟨⟨-z, Submodule.neg_mem _ hz⟩, ?_⟩
    rw [Hom.cocycleMap_val, map_neg, hdz, neg_sub]

/-- **The quasi-isomorphism of the raw encoding of Tag 0BZ7 is the cochain map underlying the
bundled homomorphism.** Let `CA` and `CB` model `A` and `B` and let `g : CA ⟶ CB` be compatible
with the underlying `R`-algebra map of `φ`, as in
`Stacks.DGA.exists_kFlat_freeGraded_resolution`. Then `g` and `φ.toRegularCochainMap` differ by
the two isomorphisms of `Stacks.DGA.ModelsComplex.isoRegularCochainComplex`, so one is a
quasi-isomorphism as soon as the other is. -/
theorem Hom.quasiIso_toRegularCochainMap_of_models (φ : A.Hom B)
    {CA CB : CochainComplex (ModuleCat.{u} R) ℤ}
    (eA : Stacks.DGA.ModelsComplex.{u, u} A CA) (eB : Stacks.DGA.ModelsComplex.{u, u} B CB)
    (g : CA ⟶ CB)
    (hg : ∀ (n : ℤ) (x : CA.X n),
      ((eB.equiv n (g.f n x)) : B.A) = φ.toAlgebraHom ((eA.equiv n x) : A.A))
    (hq : QuasiIso g) :
    QuasiIso φ.toRegularCochainMap := by
  have heq : eA.isoRegularCochainComplex.hom ≫ φ.toRegularCochainMap =
      g ≫ eB.isoRegularCochainComplex.hom := by
    ext n y
    exact Subtype.ext (hg n y).symm
  refine (quasiIso_iff_comp_left eA.isoRegularCochainComplex.hom φ.toRegularCochainMap).1 ?_
  rw [heq]
  infer_instance

/-! ### Tag 0BZ7 in the form Tag 09S6 consumes -/

/-- **Stacks Tag 0BZ7, in the encoding Tag 09S6 consumes.** Every differential graded
`R`-algebra `(B, d)` admits a homomorphism `φ : (B', d) → (B, d)` of differential graded algebras
with `(B', d)` K-flat as a complex of `R`-modules and with `H^k(φ)` bijective for every `k`, i.e.
`φ` an isomorphism on cohomology algebras.

This is `Stacks.DGA.exists_kFlat_freeGraded_resolution` with its raw encoding converted: the
`Stacks.DGA.IsDGAMorphism` bundled by `DifferentialGradedAlgebra.Hom.ofIsDGAMorphism`, the
modelling complexes removed and their K-flatness transported to the canonical complex `B'^•` by
`Stacks.DGA.ModelsComplex.kFlat_regularModule`, and the quasi-isomorphism of complexes turned
into bijectivity on cohomology by
`DifferentialGradedAlgebra.Hom.bijective_cohomologyMap_of_quasiIso`. Freeness of `B'` as a graded
algebra, which Tag 0BZ7 also provides, is dropped: the reduction of Tag 0BZ8 to a K-flat middle
algebra uses only K-flatness. -/
@[stacks 0BZ7 "the resolution read as a homomorphism of differential graded algebras which is \
K-flat over the base and bijective on cohomology in every degree, which is the hypothesis of \
Tag 09S6"]
theorem exists_kFlat_resolution_bijective_cohomologyMap (B : DifferentialGradedAlgebra.{u, u} R) :
    ∃ (B' : DifferentialGradedAlgebra.{u, u} R) (φ : B'.Hom B),
      CochainComplex.KFlat.{u, u} (regularModule B').toCochainComplex ∧
        ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k) := by
  obtain ⟨B', f, CB', CB, eB', eB, g, -, hflat, hf, hcomp, hq⟩ :=
    Stacks.DGA.exists_kFlat_freeGraded_resolution.{u, u} B
  exact ⟨B', Hom.ofIsDGAMorphism hf, eB'.kFlat_regularModule hflat,
    Hom.bijective_cohomologyMap_of_quasiIso _
      (Hom.quasiIso_toRegularCochainMap_of_models _ eB' eB g hcomp hq)⟩

/-- **The derived equivalence attached to the K-flat resolution of a differential graded
algebra.** Every differential graded `R`-algebra `(B, d)` is the target of a homomorphism
`φ : (B', d) → (B, d)` with `(B', d)` K-flat as a complex of `R`-modules along which extension of
scalars `- ⊗_{B'}^𝐋 B : D(B', d) → D(B, d)` is an equivalence of categories, with derived
restriction of scalars as quasi-inverse
(`DifferentialGraded.Bimodule.derivedExtensionEquivalence`).

This is Tag 0BZ7 followed by Tag 09S6, and it is the first ingredient of the reduction of
Tag 0BZ8 to a K-flat middle algebra; the second is the transport of the conclusion of Tag 0BZ8
through the three composites `D(A) → D(B) → D(B')`, `D(B') → D(B) → D(C)` and
`D(A) → D(B') → D(C)`. -/
@[stacks 0BZ7 "the resolution together with the derived equivalence of Tag 09S6 it gives"]
theorem exists_kFlat_resolution_derivedEquivalence (B : DifferentialGradedAlgebra.{u, u} R) :
    ∃ (B' : DifferentialGradedAlgebra.{u, u} R) (φ : B'.Hom B),
      CochainComplex.KFlat.{u, u} (regularModule B').toCochainComplex ∧
        (DifferentialGraded.Bimodule.derivedTensorFunctor
          (DifferentialGraded.Bimodule.regular φ)).IsEquivalence := by
  obtain ⟨B', φ, hflat, hφ⟩ := exists_kFlat_resolution_bijective_cohomologyMap B
  exact ⟨B', φ, hflat,
    DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor_regular φ hφ⟩

end DifferentialGradedAlgebra

end
