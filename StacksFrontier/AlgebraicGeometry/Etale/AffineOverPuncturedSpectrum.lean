module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrum
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# Affineness of a scheme which is affine over a punctured spectrum

Let `A` be a commutative ring and let `W ⊆ Spec A` be an open subscheme. Suppose a scheme `V`
over `Spec A` factors through `W` by an affine morphism `g`. Then the inverse image in `V` of a
standard open `D(x)` contained in `W` is an affine open of `V`. Consequently, as soon as a family
of elements of `A` whose standard opens all lie in `W` has image generating the unit ideal of
`Γ(V, 𝒪_V)`, those inverse images cover `V` by affine standard opens and `V` is affine.

For `A` local and `W = Spec A \ {𝔪}` the punctured spectrum this is the last paragraph of the
proof of [Stacks, Tag 0ECC]: there `A` is a regular local ring containing a field and `V` is
quasi-compact and étale over `Spec A`, the cohomological hypothesis of the source is used to show
that `H⁰(V, 𝒪_V) ⊗_A A/𝔪 = 0`, and this is exactly the statement that the image of `𝔪` generates
the unit ideal of `Γ(V, 𝒪_V)`. Writing `𝔪 = (x_1, …, x_d)`, the opens `V_{x_i}` are affine
because `V` is affine over the punctured spectrum, and they cover `V`.

## Main definitions

* `Stacks.PuncturedSpectrum.baseHom` is the ring map `A → Γ(V, 𝒪_V)` determined by a morphism
  `V ⟶ Spec A`.
* `Stacks.PuncturedSpectrum.baseAlgebra` is the `A`-algebra structure it gives `Γ(V, 𝒪_V)`.

## Main results

* `Stacks.PuncturedSpectrum.isAffineOpen_basicOpen_baseHom`: for `x : A` whose standard open is
  contained in `W`, the standard open of the image of `x` in `Γ(V, 𝒪_V)` is an affine open of
  `V`.
* `Stacks.PuncturedSpectrum.isAffine_of_span_baseHom_eq_top`: `V` is affine as soon as such a
  family of elements has image generating the unit ideal.
* `Stacks.PuncturedSpectrum.isAffine_of_map_eq_top`: the same, for the complement of the zero
  locus of an ideal `I` and the family `I` itself.
* `Stacks.PuncturedSpectrum.map_eq_top_iff_subsingleton_quotTensor`: an ideal maps onto the unit
  ideal of an algebra exactly when the quotient tensor product vanishes. With `B = Γ(V, 𝒪_V)`
  and `I = 𝔪` this is the source's hypothesis `H⁰(V, 𝒪_V) ⊗_A A/𝔪 = 0`.
* `Stacks.PuncturedSpectrum.isAffine_of_subsingleton_quotTensor_globalSections`: Tag 0ECC's final
  step in the situation of Tag 0ECB, with the vanishing of `H⁰(V, 𝒪_V) ⊗_A A/𝔪` as hypothesis.
* `Stacks.PuncturedSpectrum.algebraMap_baseAlgebra`: the structure map of `baseAlgebra` is
  `baseHom`, which is what the previous result requires of the ambient algebra structure.
* `Stacks.PuncturedSpectrum.isAffine_of_subsingleton_quotTensor_baseAlgebra`: the same final step
  with `baseAlgebra` supplied, so that no algebra structure has to be provided by the caller.

## Implementation notes

The punctured spectrum is `Stacks.LocalCohomology.puncturedSpectrum`, the open complement of the
closed point. Factoring the structure morphism through this open subscheme records both that the
closed point is outside the image of `V` and the morphism called `g` in the source; this is the
"situation of Lemma 0ECB" in which Tag 0ECC is phrased, and
`Stacks.PuncturedSpectrum.closedPoint_notMem_range_base` reads the first half of it back off the
factorization.

Standard opens of `Spec A` are written `(Spec A).basicOpen ((Scheme.ΓSpecIso A).inv x)` rather
than `PrimeSpectrum.basicOpen x`, so that every open in sight is an `(Spec A).Opens` and the
scheme-level `basicOpen` API applies without transporting along the definitional equality of the
two ambient types. `Stacks.PuncturedSpectrum.specBasicOpen` abbreviates it.

The affineness criterion at the end is Mathlib's
`AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`, which is Tag 01QF, the lemma the source
cites as Properties of Schemes, Lemma 28.28.3.

The declaration carrying the tag repeats all the hypotheses of Tag 0ECB, including the ones this
step does not use: regularity of `A`, the field it contains, and étaleness and quasi-compactness
of the structure morphism. Those are needed only for the cohomological half of the proof of Tag
0ECC. The unconditional results above it are stated without them.

### What Tag 0ECC still needs

The attribute here is qualified, and covers only the final step. The cohomological half of the
proof of Tag 0ECC — deriving `H⁰(V, 𝒪_V) ⊗_A A/𝔪 = 0` from the vanishing of `H^i(V, 𝒪_V)` for
`i ≥ dim(A) - 1` — splits further. Its spectral-sequence argument, which is the one place the
degree bound `dim(A) - 1` is used, is
`Stacks.SpectralSequence.isZero_derivedTensorHomology_zero_singleHomology_zero` in
`StacksFrontier.Algebra.Homology.SpectralSequence.OriginVanishing`, built on Tag 0662. Its three
hypotheses in this application are what the library does not yet carry:

* `H⁰(RΓ(V, 𝒪_V) ⊗^L_A A/𝔪) = 0`, from cohomology and base change applied to the empty fibre of
  `V` over the closed point — Tag 08IB;
* `Tor_r^A(A/𝔪, H^{r-1}(V, 𝒪_V)) = 0` for `2 ≤ r < dim(A)`, from Tag 0ECB (the cohomology is a
  direct sum of copies of the injective hull of the residue field) together with Tag 0EBT
  (`Tor_i^A(A/𝔪, E) = 0` for `i ≠ dim(A)`);
* the identification of `H^i(V, 𝒪_V)` with the cohomology of `RΓ(V, 𝒪_V)` as an `A`-module. The
  `A`-module model of `H^i(V, 𝒪_V)` to use is `Stacks.LocalCohomology.cohomologyOverBase` in
  `StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBase`.

## References

* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
* [Stacks Project, Tag 0ECB](https://stacks.math.columbia.edu/tag/0ECB)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

namespace Stacks.PuncturedSpectrum

/-! ### Standard opens of an affine scheme -/

variable {A : Type u} [CommRing A]

/-- The standard open of `x : A` in `Spec A`, as an open of the scheme `Spec A`. -/
noncomputable abbrev specBasicOpen (A : Type u) [CommRing A] (x : A) :
    (Spec (CommRingCat.of A)).Opens :=
  (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv x)

/-- A standard open of `Spec A` is an affine open. -/
theorem isAffineOpen_specBasicOpen (x : A) : IsAffineOpen (specBasicOpen A x) :=
  (isAffineOpen_top (Spec (CommRingCat.of A))).basicOpen _

/-- The scheme-level standard open of `x` is the standard open of `x` in `PrimeSpectrum A`. -/
theorem specBasicOpen_eq (x : A) :
    specBasicOpen A x = PrimeSpectrum.basicOpen x :=
  basicOpen_eq_of_affine (R := CommRingCat.of A) x

/-- A point of `Spec A` lies in the standard open of `x` exactly when `x` is outside it. -/
theorem mem_specBasicOpen_iff (x : A) (p : Spec (CommRingCat.of A)) :
    p ∈ specBasicOpen A x ↔ x ∉ p.asIdeal := by
  rw [specBasicOpen_eq]
  exact Iff.rfl

/-- The standard open of an element of `I` avoids the zero locus of `I`. -/
theorem specBasicOpen_le_complementZeroLocus (I : Ideal A) {x : A} (hx : x ∈ I) :
    specBasicOpen A x ≤ LocalCohomology.complementZeroLocus A I := by
  intro p hp
  exact fun (hz : (I : Set A) ⊆ p.asIdeal) ↦ (mem_specBasicOpen_iff x p).mp hp (hz hx)

/-- The standard open of an element of the maximal ideal of a local ring is contained in the
punctured spectrum. -/
theorem specBasicOpen_le_puncturedSpectrum [IsLocalRing A] {x : A}
    (hx : x ∈ IsLocalRing.maximalIdeal A) :
    specBasicOpen A x ≤ LocalCohomology.puncturedSpectrum (CommRingCat.of A) := by
  intro p hp
  refine fun (hcp : p ∈ ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))) ↦
    (mem_specBasicOpen_iff x p).mp hp ?_
  obtain rfl : p = IsLocalRing.closedPoint A := hcp
  exact hx

/-! ### Affineness from a cover by standard opens -/

variable {V : Scheme.{u}}

/-- The ring map `A → Γ(V, 𝒪_V)` determined by a morphism `V ⟶ Spec A`. -/
noncomputable def baseHom (f : V ⟶ Spec (CommRingCat.of A)) : A →+* Γ(V, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom

/-- The standard open of the image of `x` in `Γ(V, 𝒪_V)` is the inverse image of the standard
open of `x`. -/
theorem basicOpen_baseHom (f : V ⟶ Spec (CommRingCat.of A)) (x : A) :
    V.basicOpen (baseHom f x) = f ⁻¹ᵁ specBasicOpen A x :=
  (Scheme.preimage_basicOpen_top f _).symm

/-- If the structure morphism of `V` factors through an open `W ⊆ Spec A` by an affine morphism,
then the standard open of the image in `Γ(V, 𝒪_V)` of an element whose standard open lies in `W`
is an affine open of `V`. -/
theorem isAffineOpen_basicOpen_baseHom {f : V ⟶ Spec (CommRingCat.of A)}
    {W : (Spec (CommRingCat.of A)).Opens} (g : V ⟶ (W : Scheme)) [IsAffineHom g]
    (hg : g ≫ W.ι = f) {x : A} (hx : specBasicOpen A x ≤ W) :
    IsAffineOpen (V.basicOpen (baseHom f x)) := by
  have hW : IsAffineOpen (W.ι ⁻¹ᵁ specBasicOpen A x) := by
    refine (isAffineOpen_specBasicOpen x).preimage_of_isOpenImmersion _ ?_
    rwa [Scheme.Opens.opensRange_ι]
  rw [basicOpen_baseHom, ← hg]
  exact hW.preimage g

/-- **The final step of [Stacks, Tag 0ECC].** Let `V` be a scheme over `Spec A` whose structure
morphism factors through an open `W ⊆ Spec A` by an affine morphism. Let `s ⊆ A` be a set of
elements whose standard opens all lie in `W`, and whose image in `Γ(V, 𝒪_V)` generates the unit
ideal. Then `V` is affine. -/
theorem isAffine_of_span_baseHom_eq_top {f : V ⟶ Spec (CommRingCat.of A)}
    {W : (Spec (CommRingCat.of A)).Opens} (g : V ⟶ (W : Scheme)) [IsAffineHom g]
    (hg : g ≫ W.ι = f) (s : Set A) (hs : ∀ x ∈ s, specBasicOpen A x ≤ W)
    (hspan : Ideal.span (baseHom f '' s) = ⊤) :
    IsAffine V := by
  refine isAffine_of_isAffineOpen_basicOpen (baseHom f '' s) hspan ?_
  rintro _ ⟨x, hx, rfl⟩
  exact isAffineOpen_basicOpen_baseHom g hg (hs x hx)

/-- `V` is affine if the image of an ideal `I` generates the unit ideal of `Γ(V, 𝒪_V)` and the
standard opens of the elements of `I` lie in an open `W` over which `V` is affine. -/
private theorem isAffine_of_map_eq_top_of_le {f : V ⟶ Spec (CommRingCat.of A)} (I : Ideal A)
    {W : (Spec (CommRingCat.of A)).Opens} (g : V ⟶ (W : Scheme)) [IsAffineHom g]
    (hg : g ≫ W.ι = f) (hW : ∀ x ∈ I, specBasicOpen A x ≤ W) (hI : I.map (baseHom f) = ⊤) :
    IsAffine V := by
  refine isAffine_of_span_baseHom_eq_top g hg (I : Set A) hW ?_
  rw [← Ideal.map_span, Ideal.span_eq, hI]

/-- The same, for the complement of the zero locus of an ideal `I` and the family `I` itself:
`V` is affine as soon as the image of `I` generates the unit ideal of `Γ(V, 𝒪_V)`. -/
theorem isAffine_of_map_eq_top {f : V ⟶ Spec (CommRingCat.of A)} (I : Ideal A)
    (g : V ⟶ (LocalCohomology.complementZeroLocus A I : Scheme)) [IsAffineHom g]
    (hg : g ≫ (LocalCohomology.complementZeroLocus A I).ι = f)
    (hI : I.map (baseHom f) = ⊤) :
    IsAffine V :=
  isAffine_of_map_eq_top_of_le I g hg (fun _ hx ↦ specBasicOpen_le_complementZeroLocus I hx) hI

/-- A morphism to `Spec A` which factors through an open `W` has image inside `W`. -/
theorem mem_of_comp_ι_eq {f : V ⟶ Spec (CommRingCat.of A)}
    {W : (Spec (CommRingCat.of A)).Opens} (g : V ⟶ (W : Scheme)) (hg : g ≫ W.ι = f) (v : V) :
    f.base v ∈ W := by
  rw [← hg]
  simpa using Set.mem_range_self (f := W.ι.base) (g.base v)

/-- In the situation of [Stacks, Tag 0ECB] the closed point of `Spec A` is not in the image of
`V`: that is what factoring the structure morphism through the punctured spectrum says. -/
theorem closedPoint_notMem_range_base [IsLocalRing A] {f : V ⟶ Spec (CommRingCat.of A)}
    (g : V ⟶ (LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme))
    (hg : g ≫ (LocalCohomology.puncturedSpectrum (CommRingCat.of A)).ι = f) :
    IsLocalRing.closedPoint A ∉ Set.range f.base := by
  rintro ⟨v, hv⟩
  have hmem := mem_of_comp_ι_eq g hg v
  rw [hv] at hmem
  exact hmem rfl

/-! ### The vanishing of the residue tensor product -/

/-- An ideal maps onto the unit ideal of an algebra exactly when tensoring the algebra with the
quotient by the ideal gives the zero module. -/
theorem map_eq_top_iff_subsingleton_quotTensor {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) :
    I.map (algebraMap A B) = ⊤ ↔ Subsingleton ((A ⧸ I) ⊗[A] B) := by
  have hsmul : I • (⊤ : Submodule A B) = (I.map (algebraMap A B)).restrictScalars A :=
    Ideal.smul_top_eq_map I
  have hiff : I • (⊤ : Submodule A B) = ⊤ ↔ I.map (algebraMap A B) = ⊤ := by
    rw [hsmul]
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; rfl⟩
    exact Ideal.eq_top_iff_one _ |>.mpr (by simpa using (Submodule.eq_top_iff'.mp h) (1 : B))
  rw [← hiff]
  constructor
  · intro htop
    refine (TensorProduct.quotTensorEquivQuotSMul B I).toEquiv.subsingleton_congr.mpr ?_
    rw [htop]
    exact ⟨fun a b ↦ by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      exact (Submodule.Quotient.eq _).mpr (by simp)⟩
  · intro h
    have h' : Subsingleton (B ⧸ I • (⊤ : Submodule A B)) :=
      (TensorProduct.quotTensorEquivQuotSMul B I).toEquiv.subsingleton_congr.mp h
    refine eq_top_iff.mpr fun x _ ↦ ?_
    simpa [Submodule.Quotient.eq] using
      h'.allEq (Submodule.Quotient.mk x) (Submodule.Quotient.mk 0)

/-- **[Stacks, Tag 0ECC], the final step of the proof.** In the situation of [Stacks, Tag 0ECB] —
`A` a regular local ring containing a field `k`, `f : V ⟶ Spec A` étale and quasi-compact, and
the structure morphism factored through the punctured spectrum `Spec A \ {𝔪}` by an affine
morphism `g` — if `H⁰(V, 𝒪_V) ⊗_A A/𝔪 = 0`, then `V` is affine.

This is the last paragraph of the source's proof: the vanishing of the residue tensor product
says that a system of generators of `𝔪` maps to a system of generators of the unit ideal of
`Γ(V, 𝒪_V)`, so the affine opens `V_{x_i}` cover `V`.

What the source derives this vanishing from — the hypothesis `H^i(V, 𝒪_V) = 0` for
`i ≥ dim(A) - 1`, Tag 0ECB, Tag 0EBT and cohomology and base change — is not formalized here;
see the module documentation.

The hypotheses of Tag 0ECB that this step does not use are nevertheless imposed, so that the
statement is literally in the situation of that lemma. The ambient algebra structure on
`Γ(V, 𝒪_V)` is required to be the one induced by `f`. -/
@[stacks 0ECC "the final step: affineness once the residue field kills the global sections"]
theorem isAffine_of_subsingleton_quotTensor_globalSections
    (A _k : Type u) [CommRing A] [IsRegularLocalRing A] [Field _k] [Algebra _k A]
    {V : Scheme.{u}} (f : V ⟶ Spec (CommRingCat.of A)) [Etale f] [QuasiCompact f]
    (g : V ⟶ (LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme)) [IsAffineHom g]
    (hg : g ≫ (LocalCohomology.puncturedSpectrum (CommRingCat.of A)).ι = f)
    [Algebra A Γ(V, ⊤)] (halg : algebraMap A Γ(V, ⊤) = baseHom f)
    (hzero : Subsingleton ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] Γ(V, ⊤))) :
    IsAffine V := by
  have hI : (IsLocalRing.maximalIdeal A).map (baseHom f) = ⊤ := by
    rw [← halg]
    exact (map_eq_top_iff_subsingleton_quotTensor (IsLocalRing.maximalIdeal A)).mpr hzero
  exact isAffine_of_map_eq_top_of_le _ g hg (fun _ hx ↦ specBasicOpen_le_puncturedSpectrum hx) hI

/-! ### The algebra structure on the global sections -/

/-- The restriction map of `f` from the whole of `Spec A` to the whole of `V` is `f.appTop`.

This identification is what connects `baseHom` with the `A`-module structure on the global
sections used by the derived-global-sections functor, which is written with `appLE`. -/
theorem appLE_top_top (f : V ⟶ Spec (CommRingCat.of A))
    (h : (⊤ : V.Opens) ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens)) :
    f.appLE ⊤ ⊤ h = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  congr 1

/-- `baseHom` written with `appLE` instead of `appTop`. -/
theorem baseHom_eq_appLE (f : V ⟶ Spec (CommRingCat.of A))
    (h : (⊤ : V.Opens) ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens)) :
    baseHom f = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ ⊤ h).hom := by
  rw [baseHom, appLE_top_top]

/-- **`Γ(V, 𝒪_V)` as an `A`-algebra**, through the ring map `baseHom f` induced by a morphism
`f : V ⟶ Spec A`. This is the algebra structure in which the hypothesis of
`Stacks.PuncturedSpectrum.isAffine_of_subsingleton_quotTensor_globalSections` is to be read. -/
@[instance_reducible]
noncomputable def baseAlgebra (f : V ⟶ Spec (CommRingCat.of A)) : Algebra A Γ(V, ⊤) :=
  (baseHom f).toAlgebra

/-- The structure map of `baseAlgebra` is `baseHom`. -/
theorem algebraMap_baseAlgebra (f : V ⟶ Spec (CommRingCat.of A)) :
    @algebraMap A Γ(V, ⊤) _ _ (baseAlgebra f) = baseHom f := rfl

/-- **[Stacks, Tag 0ECC], the final step of the proof, with the algebra structure supplied.**
This is `Stacks.PuncturedSpectrum.isAffine_of_subsingleton_quotTensor_globalSections` with the
canonical `A`-algebra structure `baseAlgebra f` on `Γ(V, 𝒪_V)` put in place of the arbitrary one
required there; so the hypothesis is literally the vanishing of `H⁰(V, 𝒪_V) ⊗_A A/𝔪` for the
algebra structure induced by `f`. -/
theorem isAffine_of_subsingleton_quotTensor_baseAlgebra
    (A _k : Type u) [CommRing A] [IsRegularLocalRing A] [Field _k] [Algebra _k A]
    {V : Scheme.{u}} (f : V ⟶ Spec (CommRingCat.of A)) [Etale f] [QuasiCompact f]
    (g : V ⟶ (LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme)) [IsAffineHom g]
    (hg : g ≫ (LocalCohomology.puncturedSpectrum (CommRingCat.of A)).ι = f)
    (hzero : letI := baseAlgebra f
      Subsingleton ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] Γ(V, ⊤))) :
    IsAffine V :=
  let := baseAlgebra f
  isAffine_of_subsingleton_quotTensor_globalSections A _k f g hg
    (algebraMap_baseAlgebra f) hzero

end Stacks.PuncturedSpectrum
