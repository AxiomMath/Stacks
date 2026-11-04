module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CanonicalTruncation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.MooreCochainComplex
public import StacksFrontier.Cotangent.QuillenSpectralSequence
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationPowVanishing
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationTor
public import StacksFrontier.Homology.DerivedComplete.FilteredCompletionSpectralSequence

/-!
# The filtered complex of Quillen's spectral sequence

Let `A → B` be a ring map, let `C_{B/A}` be the polynomial site on the small model
`CommAlgCat.smallBoundedPolynomialSite A B κ`, let `Ō = 𝒪 ⊗_A B̲` be the presheaf of
`StacksFrontier.Cotangent.SurjectionSiteAugmentationFiltration` and let `𝒦ⁿ` be the `n`-th power of
its augmentation ideal.  This file builds the filtered complex of `B`-modules out of which
`StacksFrontier.Cotangent.QuillenSpectralSequence` assembles Theorem 08RF, i.e. a term of
`CommAlgCat.QuillenFiltrationData A B`.

The complex is the extended Moore cochain complex `C = Ō(U_•)` of `Ō` evaluated on a cosimplicial
object `U_•` of the site, which sits in cohomological degrees `≤ 0` with
`H^{-n}(C) = H_n(C_{B/A}, Ō)`.  The filtration is **not** the naive one `F^p = 𝒦^p(U_•)`: that is
degreewise the `𝒦`-adic filtration of a polynomial ring, where no power vanishes, so it is not
degreewise finite.  Following the design note in the module docstring of
`StacksFrontier.Cotangent.QuillenSpectralSequence`, the filtration used here is the canonical
truncation

`F^p = τ^{≤ -p}(𝒦^p(U_•))`,

read for every `p : ℤ` as `τ^{≤ -p⁺}(𝒦^{p⁺}(U_•))` with `p⁺ = max p 0`, so that `F^p = C` up to
canonical isomorphism for `p ≤ 0` and no case distinction is needed anywhere.  This is degreewise
zero above `p = -n`, which is exactly what `isDegreewiseFinite` asks for, and it has the same
graded pieces as the naive filtration up to quasi-isomorphism because the footnote vanishing
`H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n` makes every inclusion `τ^{≤ -p}(𝒦^p(U_•)) ⟶ 𝒦^p(U_•)` a
quasi-isomorphism.

## Main definitions

* `Stacks.ChaoticSite.GeneralValued.mooreCochainHomologyLeftDerivedColimIso`:
  `H^{-n}` of the extended Moore cochain complex of `ℱ(U_•)` is `H_n(C, ℱ) = (L_n colim)(ℱ)`.
* `CommAlgCat.quillenComplex`: the complex `C = Ō(U_•)`.
* `CommAlgCat.quillenFiltrationObj`, `CommAlgCat.quillenFiltrationι`,
  `CommAlgCat.quillenFiltrationMap`: the steps `F^p = τ^{≤ -p⁺}(𝒦^{p⁺}(U_•))` of the filtration,
  their inclusions into `C`, and the inclusions `F^q ⊆ F^p` for `p ≤ q`.
* `CommAlgCat.quillenDiagram` and `CommAlgCat.quillenFiltered`: the filtration as a diagram over
  `ℤᵒᵖ` and the resulting filtered complex.

## Main results

* `Stacks.ChaoticSite.GeneralValued.mooreCochainComplex_map_shortExact` and
  `Stacks.ChaoticSite.GeneralValued.preservesMonomorphisms_mooreCochainComplex`: the extended
  Moore cochain complex functor is exact, so it carries the inclusions `𝒦ⁿ ⊆ Ō` to inclusions of
  subcomplexes and the graded pieces of the naive filtration to its own graded pieces.
* `CommAlgCat.isDegreewiseFinite_quillenFiltration`: **the filtration is degreewise finite**, by
  the truncation.
* `CommAlgCat.filtrationSubobject_quillenFiltered_eq_top`: the filtration is the whole complex in
  nonpositive filtration degrees.
* `CommAlgCat.quillenCohomologyIso`: the cohomology of `C` is `Tor^A_*(B, B)`.
* `CommAlgCat.quillenPageOneIso`: the first page of the spectral sequence of the filtered complex
  is `H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))`.
* `CommAlgCat.nonempty_quillenFiltrationData`: **a term of `CommAlgCat.QuillenFiltrationData A B`**,
  and hence, through
  `CommAlgCat.nonempty_quillenSpectralSequenceData_of_nonempty_quillenFiltrationData`, the whole of
  Theorem 08RF -- on the two inputs `hsym` and `hvan` recorded below.
* `CommAlgCat.nonempty_quillenFiltrationData_of_surjective`: the same with the footnote vanishing
  replaced by the pro-nilpotence statement it is deduced from in
  `StacksFrontier.Cotangent.SurjectionSiteAugmentationPowVanishing`.

## Implementation notes

*Why `Int.toNat` and not a case distinction.*  Writing `𝒦^{p.toNat}` and truncating at
`-(p.toNat : ℤ)` gives, for `p ≤ 0`, the complex `τ^{≤ 0}(𝒦^0(U_•))`, which is `C` up to the two
isomorphisms `τ^{≤ 0}X ≅ X` for `X` concentrated in degrees `≤ 0` and `𝒦^0 ≅ Ō`.  So the
filtration is a single uniform formula, its functoriality over `ℤᵒᵖ` needs no case analysis, and
the clause `filtrationSubobject = ⊤` for `p ≤ 0` is the statement that those two isomorphisms are
isomorphisms.

*Functoriality for free.*  The step maps `F^q ⟶ F^p` are defined by
`CochainComplex.liftTruncLE`, whose characterising property is exactly the compatibility
`F^q ⟶ F^p ⟶ C` with the inclusions into `C` (`CommAlgCat.quillenFiltrationMap_comp_ι`).  Since
those inclusions are monomorphisms, `map_id` and `map_comp` of
`CommAlgCat.quillenDiagram` follow from that one lemma by cancelling them.

*The two inputs that are carried as hypotheses.*  The construction of the filtered complex is
unconditional, and the identification of the cohomology of `C` with `Tor^A_*(B, B)` is
`CommAlgCat.leftDerivedColimQuotientTorIso` of
`StacksFrontier.Cotangent.SurjectionSiteAugmentationTor`.  The identification of the first page
needs two facts about the homology of the site which this library does not yet have, and they
are explicit hypotheses of the statements below and of the exported theorems:

* `hsym`: `𝒦ⁿ/𝒦ⁿ⁺¹ ≅ Sym^n_{B̲}(Ω)` as presheaves of `B`-modules;
* `hvan`: `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n`, the footnote of [Stacks, Tag 08RF], which
  `CommAlgCat.isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow` deduces from `hsym`,
  the surjectivity of `A → B` and `CommAlgCat.SmallPolynomialAugmentationProNilpotent`.

Everything else — the complex, the filtration, its degreewise finiteness, its being the whole
complex in nonpositive filtration degrees, and the whole route from the first page of its spectral
sequence to the homology of the symmetric powers — is proved here.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### A cokernel read off a short exact sequence -/

namespace Stacks

/-- The third term of a short exact sequence is the cokernel of its first map. -/
def cokernelIsoShortExactX₃ {D : Type*} [Category* D] [Abelian D] {S : ShortComplex D}
    (hS : S.ShortExact) : cokernel S.f ≅ S.X₃ :=
  have := hS.epi_g
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hS.gIsCokernel

end Stacks

/-! ### Exactness of the extended Moore cochain complex -/

namespace Stacks.ChaoticSite.GeneralValued

section CochainMoore

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)
  {A : Type*} [Category* A] [Abelian A]

/-- **The extended Moore cochain complex is concentrated in nonpositive degrees**, which is what
`Stacks.ChaoticSite.GeneralValued.isZero_mooreCochainComplex_X` says, read as the strict
boundedness that the canonical truncations are taken relative to. -/
instance isStrictlyLE_mooreCochainComplex_obj (F : Cᵒᵖ ⥤ A) :
    ((mooreCochainComplex U A).obj F).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi => isZero_mooreCochainComplex_X U F i hi

/-- **Evaluating the extended Moore cochain complex in a nonpositive degree is evaluation at an
object of the site**: in cohomological degree `q = -n` it is the value at `U_n`. -/
def mooreCochainCompEvalIso {n : ℕ} {q : ℤ}
    (hn : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q) :
    mooreCochainComplex U A ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q ≅
      (evaluation Cᵒᵖ A).obj (op (U.obj (SimplexCategory.mk n))) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (cosimplicialMooreComplex A U)
      ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctorCompEvalIso A hn)

/-- **Evaluating the extended Moore cochain complex in a fixed degree preserves
monomorphisms**: in a nonpositive degree it is evaluation at an object of the site, and in a
positive degree its source is a zero object. -/
instance preservesMonomorphisms_mooreCochainComplex_comp_eval (q : ℤ) :
    (mooreCochainComplex U A ⋙
      HomologicalComplex.eval A (ComplexShape.up ℤ) q).PreservesMonomorphisms := by
  rcases le_or_gt q 0 with hq | hq
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q :=
      ⟨(-q).toNat, by simp; omega⟩
    exact Functor.PreservesMonomorphisms.of_iso (mooreCochainCompEvalIso U hn).symm
  · refine ⟨fun {X _} f _ => ⟨fun g h _ => ?_⟩⟩
    exact (isZero_mooreCochainComplex_X U X q hq).eq_of_tgt g h

/-- **The extended Moore cochain complex functor preserves monomorphisms**: a monomorphism of
presheaves becomes an inclusion of subcomplexes, because in each degree the functor is an
evaluation. -/
instance preservesMonomorphisms_mooreCochainComplex :
    (mooreCochainComplex U A).PreservesMonomorphisms where
  preserves f _ := HomologicalComplex.mono_of_mono_f _ fun q =>
    inferInstanceAs (Mono ((mooreCochainComplex U A ⋙
      HomologicalComplex.eval A (ComplexShape.up ℤ) q).map f))

/-- **The extended Moore cochain complex functor is exact**: it carries a short exact sequence of
presheaves to a short exact sequence of complexes.  In a nonpositive degree it is evaluation at an
object of the site, which is exact; in a positive degree all three terms vanish. -/
theorem mooreCochainComplex_map_shortExact {S : ShortComplex (Cᵒᵖ ⥤ A)} (hS : S.ShortExact) :
    (S.map (mooreCochainComplex U A)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun q => ?_
  rcases le_or_gt q 0 with hq | hq
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q :=
      ⟨(-q).toNat, by simp; omega⟩
    exact ShortComplex.shortExact_of_iso
      (S.mapNatIso (mooreCochainCompEvalIso U hn)).symm
      (hS.map_of_exact ((evaluation Cᵒᵖ A).obj (op (U.obj (SimplexCategory.mk n)))))
  · exact
      { mono_f := ⟨fun g h _ => (isZero_mooreCochainComplex_X U S.X₁ q hq).eq_of_tgt g h⟩
        epi_g := ⟨fun g h _ => (isZero_mooreCochainComplex_X U S.X₃ q hq).eq_of_src g h⟩
        exact := ShortComplex.exact_of_isZero_X₂ _ (isZero_mooreCochainComplex_X U S.X₂ q hq) }

end CochainMoore

section ModuleCoefficients

variable {C : Type u} [SmallCategory C] {R : Type u} [Ring R] (U : CosimplicialObject C)

/-- **`H^{-n}` of the extended Moore cochain complex of `ℱ(U_•)` is `H_n(C, ℱ)`**, the `n`-th
left derived functor of the colimit over `Cᵒᵖ` applied to `ℱ` — Tag 08PF's definition of the
homology of the site.  The two steps are the reindexing along `ComplexShape.embeddingUpIntLE 0`,
which identifies the cohomology of the extended complex in degree `-n` with the homology of the
Moore complex in degree `n`, and [Stacks, Tag 08Q9] at module coefficients. -/
def mooreCochainHomologyLeftDerivedColimIso (hU : IsPointResolution U)
    (F : Cᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ) (m : ℤ) (hm : m = -(n : ℤ)) :
    ((mooreCochainComplex U (ModuleCat.{u} R)).obj F).homology m ≅
      ((colim : (Cᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).leftDerived n).obj F :=
  (((ModuleValued.moduleCosimplicialMooreComplex U).obj F).extendHomologyIso
      (ComplexShape.embeddingUpIntLE (0 : ℤ)) (j := n) (j' := m) (by simp [hm])) ≪≫
    ((ModuleValued.moduleLeftDerivedColimitNatIso U hU n).app F).symm

/-- **The extended Moore cochain complex of `ℱ(U_•)` has no cohomology above degree `-p`** as
soon as `H_i(C, ℱ) = 0` for every `i < p`: in positive degrees the complex itself vanishes, and
in a degree `-i` with `i < p` the cohomology is `H_i(C, ℱ)`. -/
lemma isLE_mooreCochainComplex (hU : IsPointResolution U) (F : Cᵒᵖ ⥤ ModuleCat.{u} R) (p : ℕ)
    (hvan : ∀ i : ℕ, i < p →
      IsZero (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).leftDerived i).obj F)) :
    ((mooreCochainComplex U (ModuleCat.{u} R)).obj F).IsLE (-(p : ℤ)) := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  rcases le_or_gt i 0 with h | h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, -(n : ℤ) = i := ⟨(-i).toNat, by omega⟩
    exact (hvan n (by omega)).of_iso
      (mooreCochainHomologyLeftDerivedColimIso U hU F n (-(n : ℤ)) rfl)
  · exact isZero_mooreCochainComplex_homology_pos U F i h

end ModuleCoefficients

end Stacks.ChaoticSite.GeneralValued

/-! ### The complex and its filtration -/

namespace CommAlgCat

open Stacks.ChaoticSite Stacks.ChaoticSite.GeneralValued

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})
  (U : CosimplicialObject (smallBoundedPolynomialSite A B κ))

/-- **The complex `C` of [Stacks, Tag 08RF]**: the extended Moore cochain complex of
`Ō = 𝒪 ⊗_A B̲` evaluated on the cosimplicial object `U_•` of the small model of the polynomial
site.  It is concentrated in cohomological degrees `≤ 0`, with `H^{-n}(C) = H_n(C_{B/A}, Ō)`.

This is an `abbrev` so that the degreewise exactness of the extended Moore cochain complex, and
with it the monomorphisms and isomorphisms the filtration below is assembled from, are visible to
instance search. -/
abbrev quillenComplex : CochainComplex (ModuleCat.{u} B) ℤ :=
  (mooreCochainComplex U (ModuleCat.{u} B)).obj (smallPolynomialQuotientModule A B κ)

/-- **The extended Moore cochain complex of `𝒦ⁿ(U_•)`**, the `n`-th step of the naive filtration
of `CommAlgCat.quillenComplex`. -/
abbrev quillenAugmentationComplex (n : ℕ) : CochainComplex (ModuleCat.{u} B) ℤ :=
  (mooreCochainComplex U (ModuleCat.{u} B)).obj (smallPolynomialAugmentationIdealPow A B κ n)

/-- The inclusions `𝒦ᵐ ⊆ 𝒦ⁿ` are compatible with the inclusions into `Ō`. -/
lemma smallPolynomialAugmentationIdealPowMap_comp_ι {n m : ℕ} (h : n ≤ m) :
    smallPolynomialAugmentationIdealPowMap A B κ h ≫
        smallPolynomialAugmentationIdealPowι A B κ n =
      smallPolynomialAugmentationIdealPowι A B κ m :=
  NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- **The inclusion `𝒦ⁿ ⊆ Ō` is a monomorphism of presheaves**: over every object of the site it
is the inclusion of a submodule. -/
instance mono_smallPolynomialAugmentationIdealPowι (n : ℕ) :
    Mono (smallPolynomialAugmentationIdealPowι A B κ n) := by
  have : ∀ X, Mono ((smallPolynomialAugmentationIdealPowι A B κ n).app X) := fun X =>
    (ModuleCat.mono_iff_injective _).2 Subtype.coe_injective
  exact NatTrans.mono_of_mono_app _

/-- **The inclusion `𝒦ᵐ ⊆ 𝒦ⁿ` is a monomorphism of presheaves**, because the composite
`𝒦ᵐ ⊆ 𝒦ⁿ ⊆ Ō` is. -/
instance mono_smallPolynomialAugmentationIdealPowMap {n m : ℕ} (h : n ≤ m) :
    Mono (smallPolynomialAugmentationIdealPowMap A B κ h) :=
  mono_of_mono_fac (smallPolynomialAugmentationIdealPowMap_comp_ι A B κ h)

/-- **The zeroth step of the augmentation filtration is the whole of `Ō`**: the submodule
`𝒦(U)⁰` is `⊤`, so its inclusion is bijective. -/
instance isIso_smallPolynomialAugmentationIdealPowι_zero :
    IsIso (smallPolynomialAugmentationIdealPowι A B κ 0) := by
  have : ∀ X, IsIso ((smallPolynomialAugmentationIdealPowι A B κ 0).app X) := fun X => by
    have : Mono ((smallPolynomialAugmentationIdealPowι A B κ 0).app X) :=
      (ModuleCat.mono_iff_injective _).2 Subtype.coe_injective
    have : Epi ((smallPolynomialAugmentationIdealPowι A B κ 0).app X) :=
      (ModuleCat.epi_iff_surjective _).2 fun y =>
        ⟨⟨y, by rw [smallPolynomialAugmentationIdealPowSubmodule_zero]; exact Submodule.mem_top⟩,
          rfl⟩
    exact isIso_of_mono_of_epi _
  exact NatIso.isIso_of_isIso_app _

/-- **The step `F^p` of the filtration of [Stacks, Tag 08RF] used here**: the canonical truncation
`τ^{≤ -p⁺}` of the extended Moore cochain complex of `𝒦^{p⁺}(U_•)`, where `p⁺ = max p 0`.  For
`p ≤ 0` this is the whole complex `C` up to canonical isomorphism, and for `p ≥ 1` it is the
truncation of the `p`-th step of the naive filtration, which is what makes the filtration
degreewise finite. -/
abbrev quillenFiltrationObj (p : ℤ) : CochainComplex (ModuleCat.{u} B) ℤ :=
  (quillenAugmentationComplex A B κ U p.toNat).truncLE (-(p.toNat : ℤ))

/-- **The inclusion `τ^{≤ -p⁺}(𝒦^{p⁺}(U_•)) ⟶ 𝒦^{p⁺}(U_•)`** of the step `F^p` into the
corresponding step of the naive filtration. -/
abbrev quillenFiltrationTruncι (p : ℤ) :
    quillenFiltrationObj A B κ U p ⟶ quillenAugmentationComplex A B κ U p.toNat :=
  (quillenAugmentationComplex A B κ U p.toNat).ιTruncLE (-(p.toNat : ℤ))

/-- **The inclusion `F^p ⟶ C`** of a step of the filtration into the complex: the inclusion into
the naive step followed by the extended Moore cochain complex of `𝒦^{p⁺} ⊆ Ō`. -/
abbrev quillenFiltrationι (p : ℤ) :
    quillenFiltrationObj A B κ U p ⟶ quillenComplex A B κ U :=
  quillenFiltrationTruncι A B κ U p ≫
    (mooreCochainComplex U (ModuleCat.{u} B)).map
      (smallPolynomialAugmentationIdealPowι A B κ p.toNat)

/-- **The filtration is the whole complex in filtration degree `0`**: there the step `F^0` is
`τ^{≤ 0}(𝒦^0(U_•))`, and both the truncation, the complex being concentrated in degrees `≤ 0`,
and the inclusion `𝒦^0 ⊆ Ō` are isomorphisms. -/
instance isIso_quillenFiltrationι_zero : IsIso (quillenFiltrationι A B κ U 0) := by
  have h : IsIso ((quillenAugmentationComplex A B κ U 0).ιTruncLE 0 ≫
      (mooreCochainComplex U (ModuleCat.{u} B)).map
        (smallPolynomialAugmentationIdealPowι A B κ 0)) := inferInstance
  exact h

/-- **The inclusion `F^q ⊆ F^p` for `p ≤ q`**, obtained by factoring the composite
`F^q ⟶ 𝒦^{q⁺}(U_•) ⟶ 𝒦^{p⁺}(U_•)` through the canonical truncation `τ^{≤ -p⁺}`, which it does
because `F^q` is concentrated in degrees `≤ -q⁺ ≤ -p⁺`. -/
def quillenFiltrationMap {p q : ℤ} (h : p ≤ q) :
    quillenFiltrationObj A B κ U q ⟶ quillenFiltrationObj A B κ U p :=
  let : (quillenFiltrationObj A B κ U q).IsStrictlyLE (-(p.toNat : ℤ)) :=
    (quillenFiltrationObj A B κ U q).isStrictlyLE_of_le (-(q.toNat : ℤ)) (-(p.toNat : ℤ))
      (by omega)
  CochainComplex.liftTruncLE
    (quillenFiltrationTruncι A B κ U q ≫
      (mooreCochainComplex U (ModuleCat.{u} B)).map
        (smallPolynomialAugmentationIdealPowMap A B κ (show p.toNat ≤ q.toNat by omega)))
    (-(p.toNat : ℤ))

/-- **The characterising property of the step maps**: `F^q ⟶ F^p ⟶ 𝒦^{p⁺}(U_•)` is
`F^q ⟶ 𝒦^{q⁺}(U_•) ⟶ 𝒦^{p⁺}(U_•)`.  This is the defining equation of
`CochainComplex.liftTruncLE`. -/
lemma quillenFiltrationMap_comp_truncι {p q : ℤ} (h : p ≤ q) :
    quillenFiltrationMap A B κ U h ≫ quillenFiltrationTruncι A B κ U p =
      quillenFiltrationTruncι A B κ U q ≫
        (mooreCochainComplex U (ModuleCat.{u} B)).map
          (smallPolynomialAugmentationIdealPowMap A B κ (show p.toNat ≤ q.toNat by omega)) :=
  let : (quillenFiltrationObj A B κ U q).IsStrictlyLE (-(p.toNat : ℤ)) :=
    (quillenFiltrationObj A B κ U q).isStrictlyLE_of_le (-(q.toNat : ℤ)) (-(p.toNat : ℤ))
      (by omega)
  CochainComplex.liftTruncLE_ιTruncLE _ _

/-- **The step maps are compatible with the inclusions into `C`**: `F^q ⟶ F^p ⟶ C` is
`F^q ⟶ C`.  Together with the fact that those inclusions are monomorphisms this is the whole
functoriality of the filtration. -/
lemma quillenFiltrationMap_comp_ι {p q : ℤ} (h : p ≤ q) :
    quillenFiltrationMap A B κ U h ≫ quillenFiltrationι A B κ U p =
      quillenFiltrationι A B κ U q := by
  have hassoc : quillenFiltrationMap A B κ U h ≫ quillenFiltrationι A B κ U p =
      (quillenFiltrationMap A B κ U h ≫ quillenFiltrationTruncι A B κ U p) ≫
        (mooreCochainComplex U (ModuleCat.{u} B)).map
          (smallPolynomialAugmentationIdealPowι A B κ p.toNat) :=
    (Category.assoc _ _ _).symm
  rw [hassoc, quillenFiltrationMap_comp_truncι, Category.assoc, ← Functor.map_comp,
    smallPolynomialAugmentationIdealPowMap_comp_ι]

/-- **Each step of the filtration is a subcomplex of `C`**, and the step maps are inclusions. -/
instance mono_quillenFiltrationMap {p q : ℤ} (h : p ≤ q) :
    Mono (quillenFiltrationMap A B κ U h) :=
  mono_of_mono_fac (quillenFiltrationMap_comp_ι A B κ U h)

/-- **The filtration as a diagram over `ℤᵒᵖ`.**  Its functoriality is `cancel_mono` applied to
`CommAlgCat.quillenFiltrationMap_comp_ι`: two step maps with the same source and target agree
because they agree after the monomorphism `F^p ⟶ C`. -/
def quillenDiagram : ℤᵒᵖ ⥤ CochainComplex (ModuleCat.{u} B) ℤ where
  obj p := quillenFiltrationObj A B κ U p.unop
  map f := quillenFiltrationMap A B κ U (leOfHom f.unop)
  map_id p := by
    rw [← cancel_mono (quillenFiltrationι A B κ U p.unop), quillenFiltrationMap_comp_ι,
      Category.id_comp]
  map_comp {p q r} f g := by
    rw [← cancel_mono (quillenFiltrationι A B κ U r.unop), quillenFiltrationMap_comp_ι,
      Category.assoc, quillenFiltrationMap_comp_ι, quillenFiltrationMap_comp_ι]

/-- **The inclusions of the filtration into `C`, as a natural transformation** from
`CommAlgCat.quillenDiagram` to the constant diagram on `CommAlgCat.quillenComplex`. -/
def quillenFiltrationNatTrans :
    quillenDiagram A B κ U ⟶ (Functor.const ℤᵒᵖ).obj (quillenComplex A B κ U) where
  app p := quillenFiltrationι A B κ U p.unop
  naturality p _ f :=
    (quillenFiltrationMap_comp_ι A B κ U (leOfHom f.unop)).trans
      (Category.comp_id (quillenFiltrationι A B κ U p.unop)).symm

/-- **The filtered complex of [Stacks, Tag 08RF]**: the complex `C = Ō(U_•)` filtered by the
subcomplexes `F^p = τ^{≤ -p⁺}(𝒦^{p⁺}(U_•))`. -/
def quillenFiltered : CochainComplex.Filtered (ModuleCat.{u} B) where
  X := quillenComplex A B κ U
  filtration :=
    let : ∀ p : ℤᵒᵖ, Mono ((quillenFiltrationNatTrans A B κ U).app p) := fun p =>
      inferInstanceAs (Mono (quillenFiltrationι A B κ U p.unop))
    Filtration.ofDiagram (quillenDiagram A B κ U) (quillenFiltrationNatTrans A B κ U)

/-- The step `F^0` of the filtration is the whole complex in every cohomological degree. -/
private lemma isIso_eval_map_quillenFiltrationι_zero (n : ℤ) :
    IsIso ((HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.up ℤ) n).map
      (quillenFiltrationι A B κ U 0)) :=
  inferInstance

/-- **The filtration is finite in every degree** ([Stacks, Tag 012W]), which is what makes the
spectral sequence of the filtered complex converge.  It is the whole complex at `p = 0`, and in
degree `n` it vanishes at every `p` with `-p < n`, because `F^p` is concentrated in degrees
`≤ -p⁺`: this is the one thing the canonical truncation is there for, the naive filtration being
degreewise the `𝒦`-adic filtration of a polynomial ring, where no power vanishes. -/
theorem isDegreewiseFinite_quillenFiltration :
    (quillenFiltered A B κ U).filtration.IsDegreewiseFinite := by
  intro n
  refine ⟨0, 1 + (n.natAbs : ℤ), ?_, ?_⟩
  · exact isIso_eval_map_quillenFiltrationι_zero A B κ U n
  · exact CochainComplex.isZero_of_isStrictlyLE
      (quillenFiltrationObj A B κ U (1 + (n.natAbs : ℤ)))
      (-(((1 + (n.natAbs : ℤ))).toNat : ℤ)) n (by omega)

/-- **The filtration is the whole complex in nonpositive filtration degrees**, which is what makes
the spectral sequence concentrated in `p ≥ 0`.  It is everything already at `p = 0`, and the
filtration is decreasing. -/
theorem filtrationSubobject_quillenFiltered_eq_top (p n : ℤ) (hp : p ≤ 0) :
    CochainComplex.filtrationSubobject (quillenFiltered A B κ U) p n = ⊤ := by
  have h0 : CochainComplex.filtrationSubobject (quillenFiltered A B κ U) 0 n = ⊤ := by
    have : IsIso (((quillenFiltered A B κ U).filtration.ι.app (op 0)).f n) :=
      isIso_eval_map_quillenFiltrationι_zero A B κ U n
    exact Subobject.mk_eq_top_of_isIso _
  refine eq_top_iff.2 ?_
  rw [← h0]
  exact CochainComplex.filtrationSubobject_antitone (quillenFiltered A B κ U) p 0 n hp

/-! ### The graded pieces -/

/-- **The inclusion `F^p ⟶ 𝒦^{p⁺}(U_•)` is a quasi-isomorphism**, given the footnote vanishing
`H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n` of [Stacks, Tag 08RF]: the complex `𝒦^{p⁺}(U_•)` has no
cohomology above degree `-p⁺`, so its canonical truncation there does not change its cohomology.
This is the second use of the footnote vanishing, the one that gets the filtration into a
degreewise finite shape. -/
lemma quasiIso_quillenFiltrationTruncι (hU : IsPointResolution U)
    (hvan : ∀ i n : ℕ, i < n →
      IsZero ((((colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} B) ⥤
          ModuleCat.{u} B)).leftDerived i).obj (smallPolynomialAugmentationIdealPow A B κ n)))
    (p : ℤ) : QuasiIso (quillenFiltrationTruncι A B κ U p) :=
  have := isLE_mooreCochainComplex U hU
    (smallPolynomialAugmentationIdealPow A B κ p.toNat) p.toNat fun i hi => hvan i p.toNat hi
  inferInstance

/-- **The comparison of the `p`-th graded piece of the filtration with that of the naive
filtration.**  Both are cokernels of an inclusion -- the graded piece `gr^p` of the filtration is
by definition the cokernel of `F^{p+1} ⟶ F^p` -- and the map is the one induced on cokernels by
the square whose vertical maps are the inclusions `F^{p+1} ⟶ 𝒦^{p+1}(U_•)` and
`F^p ⟶ 𝒦^p(U_•)`. -/
def quillenGradedCompare (p : ℕ) :
    (FilteredObject.gr (p : ℤ)).obj (quillenFiltered A B κ U) ⟶
      cokernel ((mooreCochainComplex U (ModuleCat.{u} B)).map
        (smallPolynomialAugmentationIdealPowMap A B κ (Nat.le_succ p))) :=
  cokernel.map
    (quillenFiltrationMap A B κ U (show (p : ℤ) ≤ (p : ℤ) + 1 by omega))
    ((mooreCochainComplex U (ModuleCat.{u} B)).map
      (smallPolynomialAugmentationIdealPowMap A B κ (Nat.le_succ p)))
    (quillenFiltrationTruncι A B κ U ((p : ℤ) + 1))
    (quillenFiltrationTruncι A B κ U (p : ℤ))
    (quillenFiltrationMap_comp_truncι A B κ U (show (p : ℤ) ≤ (p : ℤ) + 1 by omega))

/-- **The comparison of the graded pieces is a quasi-isomorphism**, by
`CochainComplex.quasiIso_cokernelMap` and the two quasi-isomorphisms
`CommAlgCat.quasiIso_quillenFiltrationTruncι`. -/
lemma quasiIso_quillenGradedCompare (hU : IsPointResolution U)
    (hvan : ∀ i n : ℕ, i < n →
      IsZero ((((colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} B) ⥤
          ModuleCat.{u} B)).leftDerived i).obj (smallPolynomialAugmentationIdealPow A B κ n)))
    (p : ℕ) : QuasiIso (quillenGradedCompare A B κ U p) := by
  have := quasiIso_quillenFiltrationTruncι A B κ U hU hvan ((p : ℤ) + 1)
  have := quasiIso_quillenFiltrationTruncι A B κ U hU hvan (p : ℤ)
  exact CochainComplex.quasiIso_cokernelMap _ _ (quillenFiltrationTruncι A B κ U ((p : ℤ) + 1))
    (quillenFiltrationTruncι A B κ U p) (quillenFiltrationMap_comp_truncι A B κ U (by omega))

/-- **The `p`-th graded piece of the naive filtration is the extended Moore cochain complex of
`𝒦^p/𝒦^{p+1}`**: the sequence `0 → 𝒦^{p+1} → 𝒦^p → 𝒦^p/𝒦^{p+1} → 0` is short exact and the
extended Moore cochain complex functor is exact. -/
def quillenNaiveGradedIso (p : ℕ) :
    cokernel ((mooreCochainComplex U (ModuleCat.{u} B)).map
        (smallPolynomialAugmentationIdealPowMap A B κ (Nat.le_succ p))) ≅
      (mooreCochainComplex U (ModuleCat.{u} B)).obj
        (smallPolynomialAugmentationGraded A B κ p) :=
  Stacks.cokernelIsoShortExactX₃ (mooreCochainComplex_map_shortExact U
    (shortExact_smallPolynomialAugmentationGradedShortComplex A B κ p))

/-- **The `p`-th graded piece of the filtration, in cohomological degree `p + q`, is the
cohomology of the extended Moore cochain complex of `Sym^p_{B̲}(Ω)`** — given the identification
`hsym` of the graded pieces of the augmentation filtration with the symmetric powers and the
footnote vanishing `hvan`.  The three steps are the comparison with the naive filtration, the
exactness of the extended Moore cochain complex, and `hsym`. -/
def quillenGradedHomologyIso (hU : IsPointResolution U)
    (hsym : ∀ n : ℕ, smallPolynomialAugmentationGraded A B κ n ≅
      symmetricPowerDiagram (smallBoundedPolynomialSite A B κ) (B : Type u)
        (smallPolynomialCotangentModulePresheaf A B κ) n)
    (hvan : ∀ i n : ℕ, i < n →
      IsZero ((((colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} B) ⥤
          ModuleCat.{u} B)).leftDerived i).obj (smallPolynomialAugmentationIdealPow A B κ n)))
    (p : ℕ) (q : ℤ) :
    ((FilteredObject.gr (p : ℤ)).obj (quillenFiltered A B κ U)).homology ((p : ℤ) + q) ≅
      ((mooreCochainComplex U (ModuleCat.{u} B)).obj
        (symmetricPowerDiagram (smallBoundedPolynomialSite A B κ) (B : Type u)
          (smallPolynomialCotangentModulePresheaf A B κ) p)).homology ((p : ℤ) + q) := by
  have := quasiIso_quillenGradedCompare A B κ U hU hvan p
  have : IsIso (HomologicalComplex.homologyMap (quillenGradedCompare A B κ U p)
      ((p : ℤ) + q)) := (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  exact asIso (HomologicalComplex.homologyMap (quillenGradedCompare A B κ U p)
      ((p : ℤ) + q)) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ)
      ((p : ℤ) + q)).mapIso (quillenNaiveGradedIso A B κ U p ≪≫
        (mooreCochainComplex U (ModuleCat.{u} B)).mapIso (hsym p))

end CommAlgCat

/-! ### The two identifications of Theorem 08RF, and the datum -/

namespace CommAlgCat

open Stacks.ChaoticSite Stacks.ChaoticSite.GeneralValued

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **The cohomology of `C` in degree `n = -k` is `Tor^A_k(B, B)`**, given the identification
`htor` of `H_k(C_{B/A}, Ō)` with `Tor^A_k(B, B)`: the left hand side is `H_k(C_{B/A}, Ō)` by
[Stacks, Tag 08Q9].  The degree is taken as a parameter so that
`CommAlgCat.quillenCohomologyIso` can supply it in unreduced form. -/
def quillenCohomologyIsoOfNeg
    (htor : ∀ k : ℕ,
      (((colim : ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} B) ⥤ ModuleCat.{u} B)).leftDerived k).obj
          (smallPolynomialQuotientModule A B (standardResolutionVarCardinal A B)) ≅
        (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) k).obj
          (ModuleCat.of A (B : Type u)))
    (k : ℕ) (n : ℤ) (hn : n = -(k : ℤ)) :
    (quillenComplex A B (standardResolutionVarCardinal A B)
        (standardResolutionSmallCosimplicialObject A B)).homology n ≅ torAbutment A B n :=
  mooreCochainHomologyLeftDerivedColimIso (standardResolutionSmallCosimplicialObject A B)
      (isPointResolution_standardResolutionSmallCosimplicialObject A B) _ k n hn ≪≫
    htor k ≪≫ eqToIso (by rw [hn, torAbutment_neg_natCast])

/-- **The cohomology of `C` is `Tor^A_{-n}(B, B)`**, given the identification `htor` of
`H_k(C_{B/A}, Ō)` with `Tor^A_k(B, B)`.  In positive cohomological degree both sides vanish --
the complex because it is concentrated in degrees `≤ 0`, the abutment by definition -- and in
nonpositive degree this is `CommAlgCat.quillenCohomologyIsoOfNeg`. -/
def quillenCohomologyIso
    (htor : ∀ k : ℕ,
      (((colim : ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} B) ⥤ ModuleCat.{u} B)).leftDerived k).obj
          (smallPolynomialQuotientModule A B (standardResolutionVarCardinal A B)) ≅
        (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) k).obj
          (ModuleCat.of A (B : Type u)))
    (n : ℤ) :
    (quillenComplex A B (standardResolutionVarCardinal A B)
        (standardResolutionSmallCosimplicialObject A B)).homology n ≅ torAbutment A B n :=
  if hn : n ≤ 0 then quillenCohomologyIsoOfNeg A B htor (-n).toNat n (by omega)
  else
    IsZero.iso
      (isZero_mooreCochainComplex_homology_pos (standardResolutionSmallCosimplicialObject A B)
        (smallPolynomialQuotientModule A B (standardResolutionVarCardinal A B)) n (by omega))
      (isZero_torAbutment_of_pos A B (by omega))

/-- **For `p + q = -k ≤ 0` the cohomology of the extended Moore cochain complex of `Sym^p_{B̲}(Ω)`
in degree `p + q` is `H_k(C_{B/A}, Sym^p_{B̲}(Ω))`**, by [Stacks, Tag 08Q9], and that is the
entry `H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))` of the first page.  The homological degree `k` is taken
as a parameter so that `CommAlgCat.quillenSymmetricPowerHomologyIso` can supply it in unreduced
form. -/
def quillenSymmetricPowerHomologyIsoOfNeg (p : ℕ) (q : ℤ) (k : ℕ)
    (hk : (p : ℤ) + q = -(k : ℤ)) :
    ((mooreCochainComplex (standardResolutionSmallCosimplicialObject A B)
        (ModuleCat.{u} B)).obj
      (symmetricPowerDiagram
        (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
        (smallPolynomialCotangentModulePresheaf A B
          (standardResolutionVarCardinal A B)) p)).homology ((p : ℤ) + q) ≅
      symmetricPowerSiteHomology A B p (-(p : ℤ) - q) :=
  mooreCochainHomologyLeftDerivedColimIso (standardResolutionSmallCosimplicialObject A B)
      (isPointResolution_standardResolutionSmallCosimplicialObject A B) _ k ((p : ℤ) + q) hk ≪≫
    eqToIso (by
      rw [show -(p : ℤ) - q = ((k : ℕ) : ℤ) by omega, symmetricPowerSiteHomology_natCast])

/-- **The cohomology of the extended Moore cochain complex of `Sym^p_{B̲}(Ω)` in degree `p + q` is
`H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))`**, the entry of the first page of Quillen's spectral sequence
at the bidegree `(p, q)`.  For `p + q ≤ 0` this is
`CommAlgCat.quillenSymmetricPowerHomologyIsoOfNeg`; for `p + q > 0` both sides vanish, the left
because the complex does and the right because the symmetric powers are indexed by the natural
numbers. -/
def quillenSymmetricPowerHomologyIso (p : ℕ) (q : ℤ) :
    ((mooreCochainComplex (standardResolutionSmallCosimplicialObject A B)
        (ModuleCat.{u} B)).obj
      (symmetricPowerDiagram
        (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
        (smallPolynomialCotangentModulePresheaf A B
          (standardResolutionVarCardinal A B)) p)).homology ((p : ℤ) + q) ≅
      symmetricPowerSiteHomology A B p (-(p : ℤ) - q) :=
  if hpq : (p : ℤ) + q ≤ 0 then
    quillenSymmetricPowerHomologyIsoOfNeg A B p q (-((p : ℤ) + q)).toNat (by omega)
  else
    IsZero.iso
      (isZero_mooreCochainComplex_homology_pos (standardResolutionSmallCosimplicialObject A B) _
        ((p : ℤ) + q) (by omega))
      (isZero_symmetricPowerSiteHomology_of_neg A B p (by omega))

/-- **The first page of the spectral sequence of the filtered complex is
`H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))`**, the identification [Stacks, Tag 08RF] asserts.  The first
page of the spectral sequence of a filtered complex is the cohomology of its associated graded
(`AdicFilteredCompletion.nonempty_firstPage_iso_gradedPiece_homology`), the graded pieces here are
those of the naive filtration up to quasi-isomorphism, and those are the extended Moore cochain
complexes of the symmetric powers. -/
def quillenPageOneIso
    (hsym : ∀ n : ℕ,
      smallPolynomialAugmentationGraded A B (standardResolutionVarCardinal A B) n ≅
        symmetricPowerDiagram
          (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
          (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) n)
    (hvan : ∀ i n : ℕ, i < n →
      IsZero ((((colim :
            ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
              ModuleCat.{u} B) ⥤ ModuleCat.{u} B)).leftDerived i).obj
        (smallPolynomialAugmentationIdealPow A B (standardResolutionVarCardinal A B) n)))
    (p : ℕ) (q : ℤ) :
    ((CochainComplex.Filtered.spectralSequenceFunctor.obj
        (quillenFiltered A B (standardResolutionVarCardinal A B)
          (standardResolutionSmallCosimplicialObject A B))).page 1).X ((p : ℤ), q) ≅
      symmetricPowerSiteHomology A B p (-(p : ℤ) - q) :=
  (AdicFilteredCompletion.nonempty_firstPage_iso_gradedPiece_homology
      (quillenFiltered A B (standardResolutionVarCardinal A B)
        (standardResolutionSmallCosimplicialObject A B)) (p : ℤ) q).some ≪≫
    quillenGradedHomologyIso A B (standardResolutionVarCardinal A B)
      (standardResolutionSmallCosimplicialObject A B)
      (isPointResolution_standardResolutionSmallCosimplicialObject A B) hsym hvan p q ≪≫
    quillenSymmetricPowerHomologyIso A B p q

/-- **The filtered complex of Quillen's spectral sequence exists**, hence by
`CommAlgCat.nonempty_quillenSpectralSequenceData_of_nonempty_quillenFiltrationData` so does the
whole datum of [Stacks, Tag 08RF].

The filtered complex, its degreewise finiteness and its being the whole complex in nonpositive
filtration degrees are proved here with no hypothesis at all; the two identifications of
[Stacks, Tag 08RF] rest on facts about the homology of the polynomial site.  The identification
of the cohomology with `Tor^A_*(B, B)` is discharged by
`CommAlgCat.leftDerivedColimQuotientTorIso`; the two that this library does not yet have are
carried here as the hypotheses `hsym` and `hvan`. -/
theorem nonempty_quillenFiltrationData
    (hsym : ∀ n : ℕ,
      smallPolynomialAugmentationGraded A B (standardResolutionVarCardinal A B) n ≅
        symmetricPowerDiagram
          (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
          (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) n)
    (hvan : ∀ i n : ℕ, i < n →
      IsZero ((((colim :
            ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
              ModuleCat.{u} B) ⥤ ModuleCat.{u} B)).leftDerived i).obj
        (smallPolynomialAugmentationIdealPow A B (standardResolutionVarCardinal A B) n))) :
    Nonempty (QuillenFiltrationData A B) :=
  ⟨{ complex :=
       quillenFiltered A B (standardResolutionVarCardinal A B)
         (standardResolutionSmallCosimplicialObject A B)
     isDegreewiseFinite :=
       isDegreewiseFinite_quillenFiltration A B (standardResolutionVarCardinal A B)
         (standardResolutionSmallCosimplicialObject A B)
     filtrationSubobject_eq_top :=
       filtrationSubobject_quillenFiltered_eq_top A B (standardResolutionVarCardinal A B)
         (standardResolutionSmallCosimplicialObject A B)
     cohomologyIso := quillenCohomologyIso A B (leftDerivedColimQuotientTorIso A B)
     pageOneIso := quillenPageOneIso A B hsym hvan }⟩

/-- **The filtered complex of Quillen's spectral sequence exists for a surjective ring map**, with
the footnote vanishing `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n` replaced by the pro-nilpotence statement
`CommAlgCat.SmallPolynomialAugmentationProNilpotent` that
`CommAlgCat.isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow` deduces it from: the
dévissage half of that deduction needs the graded pieces of the augmentation filtration to be the
symmetric powers, which is `hsym`, together with the final vanishing clause of
[Stacks, Tag 08RF], which holds for a surjective `A → B` and is proved in this library
(`CommAlgCat.isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective`). -/
theorem nonempty_quillenFiltrationData_of_surjective
    (h : Function.Surjective (algebraMap A (B : Type u)))
    (hsym : ∀ n : ℕ,
      smallPolynomialAugmentationGraded A B (standardResolutionVarCardinal A B) n ≅
        symmetricPowerDiagram
          (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
          (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) n)
    (hpro : SmallPolynomialAugmentationProNilpotent A B (standardResolutionVarCardinal A B)) :
    Nonempty (QuillenFiltrationData A B) := by
  have hgr : ∀ k i : ℕ, i < k →
      IsZero ((((colim :
            ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
              ModuleCat.{u} B) ⥤ ModuleCat.{u} B)).leftDerived i).obj
        (smallPolynomialAugmentationGraded A B (standardResolutionVarCardinal A B) k)) :=
    fun k i hik =>
      (isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective A B h k i
        hik).of_iso ((((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} B) ⥤ ModuleCat.{u} B)).leftDerived i).mapIso (hsym k))
  exact nonempty_quillenFiltrationData A B hsym fun i n hin =>
    isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow A B
      (standardResolutionVarCardinal A B) hgr hpro i n hin

end CommAlgCat

end
