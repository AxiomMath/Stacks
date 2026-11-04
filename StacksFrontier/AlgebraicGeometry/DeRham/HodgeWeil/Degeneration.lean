module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToMap
public import StacksFrontier.Algebra.Homology.SpectralSequence.LengthDegeneration
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.CupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.HodgeToDeRhamSpectralSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ConnectiveHypercohomology

/-!
# The numerical criterion for `E_1`-degeneration of the Hodge-to-de Rham spectral sequence

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X`, let
`Ω^•_{𝒪_X/A}` be the relative de Rham complex and let `R = A(X)` be the ring of global sections
of `A`. The Hodge-to-de Rham spectral sequence of the brutal filtration of `Ω^•`,
`E_1^{p, q} = H^q(X, Ω^p) ⟹ H^{p + q}_{dR}(X/A)`, is a first quadrant spectral sequence of
`R`-modules, and `H^n_{dR}` has a finite filtration whose graded pieces are the `E_∞^{p, n - p}`.
Since `E_∞^{p,q}` is a subquotient of `E_1^{p,q}`, a length count gives

`ℓ(H^n_{dR}) ≤ ∑_{p + q = n} ℓ(H^q(X, Ω^p))`,

with equality in every degree exactly when the spectral sequence degenerates at `E_1`, provided
the Hodge groups have finite length. The same holds with lengths over `R` replaced by dimensions
over a field `k` mapping to `R`: the length over `k` is additive on short exact sequences of
`R`-modules as well. Over a field `k`, for `X` proper over `k`, this is the form used by
[Stacks, Remark 0FWE]: if the betti numbers of a Weil cohomology theory are independent of the
theory, then applied to Hodge and to de Rham cohomology they give
`dim_k H^n_{dR}(X/k) = ∑_{p + q = n} dim_k H^q(X, Ω^p_{X/k})`, so the Hodge-to-de Rham spectral
sequence degenerates at `E_1`.

## Main results

* `Stacks.HodgeWeil.degeneratesAt_map_iff`: a spectral sequence degenerates at a page exactly
  when its image under a faithful exact functor does.
* `Stacks.HodgeWeil.degeneratesAt_iff_length_eq_sum_antidiagonal` and
  `Stacks.HodgeWeil.degeneratesAt_iff_finrank_eq_sum_antidiagonal`: for a spectral sequence of
  modules whose page `E_r` lies in the first quadrant, degeneration at `E_r` is the equality
  `ℓ(H^n) = ∑_{p + q = n} ℓ(E_r^{p, q})` for every `n ≥ 0`, and likewise with dimensions over a
  field `k` acting through a ring map `k →+* R`.
* `Stacks.HodgeWeil.isZero_page_one_of_neg`: the first page of the brutal-truncation spectral
  sequence of a complex concentrated in nonnegative degrees lies in the first quadrant.
* `Stacks.HodgeWeil.nonempty_page_one_iso_hodgeCohomologyComponent`: the first-page term
  `E_1^{p, q}` of any brutal-truncation spectral sequence of the de Rham complex is the Hodge
  group `H^q(X, Ω^p)`, as a module over `A(X)`.
* `Stacks.HodgeWeil.degeneratesAt_one_iff_length_deRham_eq_sum_hodge`: **the Hodge-to-de Rham
  spectral sequence degenerates at `E_1` if and only if
  `ℓ(H^n_{dR}) = ∑_{p + q = n} ℓ(H^q(X, Ω^p))` for every `n`**, when the Hodge groups have
  finite length.
* `Stacks.HodgeWeil.degeneratesAt_one_iff_finrank_deRham_eq_sum_hodge`: **the same with
  dimensions over a field `k` acting on `A(X)` through `σ : k →+* A(X)`**:
  `E_1`-degeneration holds if and only if `dim_k H^n_{dR} = ∑_{p + q = n} dim_k H^q(X, Ω^p)` for
  every `n`, when the Hodge groups are finite dimensional over `k`.

## Implementation notes

The spectral sequence is any `Stacks.Cohomology.FilteredComplex.StupidTruncationSpectralSequence`
of the de Rham complex that abuts to `H^*_{dR}(X/A)`, which is what
`AlgebraicGeometry.SheafOfModules.exists_hodgeToDeRhamSpectralSequence` provides. Its derived
global-sections functor is not assumed to be the one de Rham and Hodge cohomology are taken
with; both are right derived functors of global sections, so they agree by the uniqueness of
right derived functors, and this is how its first page is identified with the Hodge groups
`AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent`. The boundedness of the spectral
sequence is not needed: abutment alone gives the finite filtration of `H^n_{dR}`.

Dimensions over `k` are not lengths over `A(X)`. The criterion over `k` is obtained by restricting
scalars along `σ`, which is a faithful exact functor: it transports the spectral sequence and its
abutment to `k`-vector spaces, and it does not change which differentials vanish. Over `k` the
length is the dimension.

The Hodge group `H^q(X, Ω^p)` is indexed by `p : ℕ`, the degree of the forms. The bidegrees of
total degree `n` that contribute are those of `Finset.antidiagonal n`: the first page vanishes
when `p < 0`, because the de Rham complex vanishes in negative degrees, and when `q < 0`,
because derived global sections of a sheaf have no cohomology in negative degrees. For the same
reason `H^n_{dR}` vanishes for `n < 0`, so only `n ≥ 0` appears in the criterion.

The ring `A(X)` appears in two spellings, as the sections of
`AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A` — the spelling of the Hodge and de Rham
groups — and as the sections of the structure sheaf of
`AlgebraicGeometry.SheafOfModules.baseRingedSpace A` — the spelling of the spectral sequence.
The two are equal by definition, but instance search does not cross between them, and neither
spelling carries the commutative ring structure of `A(X)` as an instance; the proofs supply it.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FM7](https://stacks.math.columbia.edu/tag/0FM7)
* [Stacks Project, Tag 0FLK](https://stacks.math.columbia.edu/tag/0FLK)
* [Stacks Project, Tag 011O](https://stacks.math.columbia.edu/tag/011O)
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.SheafOfModules RingedSpaceModuleAdjunction
open Stacks.Cohomology.FilteredComplex

namespace Stacks.HodgeWeil

/-! ### Degeneration and faithful exact functors -/

section Map

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-- **A faithful exact functor detects degeneration.** The differentials of `E.map F` are the
images under `F` of those of `E`, and a faithful functor preserving zero morphisms sends exactly
the zero morphisms to zero. -/
theorem degeneratesAt_map_iff (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [F.Faithful]
    (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r) :
    (E.map F).DegeneratesAt r hr ↔ E.DegeneratesAt r hr :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    F.map_eq_zero_iff

end Map

/-! ### The numerical criterion for a first quadrant page -/

section Length

/-- Reindexing a sum over the bidegrees `(p, n - p)`, `0 ≤ p ≤ n`, as a sum over the
antidiagonal `p + q = n` of `ℕ × ℕ`. -/
theorem sum_Icc_eq_sum_antidiagonal {M : Type*} [AddCommMonoid M] (f : ℤ → ℤ → M) (n : ℕ) :
    ∑ p ∈ Finset.Icc (0 : ℤ) n, f p (n - p) =
      ∑ pq ∈ Finset.antidiagonal n, f pq.1 pq.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  refine Finset.sum_bij (fun k _ => (k : ℤ)) (fun k hk => ?_)
    (fun a _ b _ h => by exact_mod_cast h) (fun p hp => ?_) (fun k hk => ?_)
  · rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc]
    omega
  · rw [Finset.mem_Icc] at hp
    exact ⟨p.toNat, Finset.mem_range.2 (by omega), by omega⟩
  · rw [Finset.mem_range] at hk
    rw [show ((n - k : ℕ) : ℤ) = (n : ℤ) - k by omega]

variable {R : Type u} [CommRing R] {r₀ : ℤ}
  {E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀} {H : ℤ → ModuleCat.{v} R}

/-- On a page lying in the first quadrant, the terms `E_r^{p, n - p}` vanish outside
`0 ≤ p ≤ n`. -/
theorem isZero_page_of_notMem_Icc {r : ℤ} {hr : r₀ ≤ r}
    (hzero : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r hr).X (p, q)))
    (n p : ℤ) (hp : p ∉ Finset.Icc 0 n) : IsZero ((E.page r hr).X (p, n - p)) :=
  hzero p (n - p) (by rw [Finset.mem_Icc] at hp; omega)

/-- **`ℓ(H^n) ≤ ∑_{p + q = n} ℓ(E_r^{p, q})`** for a spectral sequence of modules abutting to
`H` whose page `E_r` lies in the first quadrant. -/
theorem length_abutment_le_sum_antidiagonal (hE : SpectralSequence.AbutsTo E H) (r : ℤ)
    (hr : r₀ ≤ r) (hzero : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r hr).X (p, q)))
    (n : ℕ) :
    Module.length R (H n) ≤ ∑ pq ∈ Finset.antidiagonal n,
      Module.length R ((E.page r hr).X ((pq.1 : ℤ), (pq.2 : ℤ))) := by
  rw [← sum_Icc_eq_sum_antidiagonal (fun p q => Module.length R ((E.page r hr).X (p, q)))]
  exact SpectralSequence.length_abutment_le_sum hE n r hr _ (isZero_page_of_notMem_Icc hzero n)

/-- If the page `E_r` of a spectral sequence abutting to `H` lies in the first quadrant, then
`H^n = 0` for `n < 0`. -/
theorem isZero_abutment_of_neg (hE : SpectralSequence.AbutsTo E H) (r : ℤ) (hr : r₀ ≤ r)
    (hzero : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r hr).X (p, q))) {n : ℤ} (hn : n < 0) :
    IsZero (H n) := by
  rw [← ModuleCat.length_eq_zero_iff_isZero]
  exact le_antisymm ((SpectralSequence.length_abutment_le_sum hE n r hr ∅
    fun p _ => hzero p (n - p) (by omega)).trans_eq Finset.sum_empty) zero_le

/-- **The numerical criterion for degeneration, first quadrant form.** Let `E` be a spectral
sequence of modules abutting to `H` whose page `E_r` lies in the first quadrant and has terms of
finite length. Then `E` degenerates at `E_r` if and only if
`ℓ(H^n) = ∑_{p + q = n} ℓ(E_r^{p, q})` for every `n ≥ 0`. -/
theorem degeneratesAt_iff_length_eq_sum_antidiagonal (hE : SpectralSequence.AbutsTo E H)
    (r : ℤ) (hr : r₀ ≤ r)
    (hzero : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r hr).X (p, q)))
    (hfin : ∀ p q : ℕ, Module.length R ((E.page r hr).X ((p : ℤ), (q : ℤ))) ≠ ⊤) :
    E.DegeneratesAt r hr ↔ ∀ n : ℕ, Module.length R (H n) =
      ∑ pq ∈ Finset.antidiagonal n, Module.length R ((E.page r hr).X ((pq.1 : ℤ), (pq.2 : ℤ))) := by
  have hfin' : ∀ pq : ℤ × ℤ, Module.length R ((E.page r hr).X pq) ≠ ⊤ := by
    rintro ⟨p, q⟩
    by_cases h : p < 0 ∨ q < 0
    · exact ((ModuleCat.length_eq_zero_iff_isZero _).2 (hzero p q h)).trans_ne ENat.zero_ne_top
    · lift p to ℕ using (by omega)
      lift q to ℕ using (by omega)
      exact hfin p q
  have hsum := sum_Icc_eq_sum_antidiagonal (fun p q => Module.length R ((E.page r hr).X (p, q)))
  rw [SpectralSequence.degeneratesAt_iff_length_eq hE r hr (fun n => Finset.Icc 0 n)
    (isZero_page_of_notMem_Icc hzero) hfin']
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · rw [h n, hsum]
  · rcases lt_or_ge n 0 with hn | hn
    · rw [(ModuleCat.length_eq_zero_iff_isZero _).2 (isZero_abutment_of_neg hE r hr hzero hn),
        Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    · lift n to ℕ using hn
      rw [h n, hsum]

variable {k : Type w} [Field k] (σ : k →+* R)

/-- **The numerical criterion for degeneration, with dimensions over a field.** Let `E` be a
spectral sequence of `R`-modules abutting to `H` whose page `E_r` lies in the first quadrant, and
let `σ : k →+* R` be a ring map from a field. If the terms of `E_r` are finite dimensional over
`k`, then `E` degenerates at `E_r` if and only if `dim_k H^n = ∑_{p + q = n} dim_k E_r^{p, q}`
for every `n ≥ 0`. -/
theorem degeneratesAt_iff_finrank_eq_sum_antidiagonal (hE : SpectralSequence.AbutsTo E H)
    (r : ℤ) (hr : r₀ ≤ r)
    (hzero : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r hr).X (p, q)))
    (hfin : ∀ p q : ℕ, FiniteDimensional k
      ((ModuleCat.restrictScalars.{v} σ).obj ((E.page r hr).X ((p : ℤ), (q : ℤ))))) :
    E.DegeneratesAt r hr ↔ ∀ n : ℕ,
      Module.finrank k ((ModuleCat.restrictScalars.{v} σ).obj (H n)) =
        ∑ pq ∈ Finset.antidiagonal n, Module.finrank k
          ((ModuleCat.restrictScalars.{v} σ).obj ((E.page r hr).X ((pq.1 : ℤ), (pq.2 : ℤ)))) := by
  let F := ModuleCat.restrictScalars.{v} σ
  have hE' := hE.map F
  have hzero' : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero (((E.map F).page r hr).X (p, q)) :=
    fun p q h => F.map_isZero (hzero p q h)
  have hlen : ∀ p q : ℕ, Module.length k (((E.map F).page r hr).X ((p : ℤ), (q : ℤ))) =
      Module.finrank k (F.obj ((E.page r hr).X ((p : ℤ), (q : ℤ)))) := fun p q => by
    have := hfin p q
    exact Module.length_eq_finrank k (F.obj ((E.page r hr).X ((p : ℤ), (q : ℤ))))
  have hfinℓ : ∀ p q : ℕ, Module.length k (((E.map F).page r hr).X ((p : ℤ), (q : ℤ))) ≠ ⊤ :=
    fun p q => (hlen p q).trans_ne (ENat.natCast_ne_top _)
  have hH : ∀ n : ℕ, FiniteDimensional k (F.obj (H n)) := fun n => by
    have hle := length_abutment_le_sum_antidiagonal hE' r hr hzero' n
    have hne : Module.length k (F.obj (H n)) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.sum_ne_top.2 fun pq _ => hfinℓ pq.1 pq.2) hle
    rw [Module.length_eq_rank, ne_eq, Cardinal.toENat_eq_top, not_le] at hne
    exact Module.rank_lt_aleph0_iff.1 hne
  rw [← degeneratesAt_map_iff F E r hr,
    degeneratesAt_iff_length_eq_sum_antidiagonal hE' r hr hzero' hfinℓ]
  refine forall_congr' fun n => ?_
  have := hH n
  rw [Finset.sum_congr rfl fun pq _ => hlen pq.1 pq.2]
  show Module.length k (F.obj (H n)) = _ ↔ _
  rw [Module.length_eq_finrank, ← Nat.cast_sum, Nat.cast_inj]

end Length

/-! ### The first page of a brutal-truncation spectral sequence -/

section FirstPage

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.HypercohomologyEdge.evaluation_additive

variable {X : RingedSpace.{u, u}}
  {F : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ}
  (S : StupidTruncationSpectralSequence X F)

/-- The derived global sections functor of a brutal-truncation package sends an object of the
derived category with no cohomology in negative degrees to one with the same property. -/
private theorem isZero_homology_RΓ_of_isGE
    (N : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (hN : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor _ i).obj N))
    {q : ℤ} (hq : q < 0) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) q).obj (S.RΓ.obj N)) := by
  have := S.isRightDerived
  exact Stacks.Cohomology.Connective.isZero_homology_rightDerived_of_isGE
    (_root_.SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) S.RΓ S.α _ hN q hq

/-- The derived global sections functor of a brutal-truncation package has no cohomology in
negative degrees on a sheaf: `H^q(X, M) = 0` for `q < 0`. -/
theorem isZero_homology_obj_single_of_neg (M : _root_.SheafOfModules.{u} (structureSheafRing X))
    {q : ℤ} (hq : q < 0) :
    IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) q).obj
      (S.RΓ.obj ((DerivedCategory.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj M))) := by
  exact isZero_homology_RΓ_of_isGE S _ (fun i hi => DerivedCategory.isZero_of_isGE _ 0 i hi) hq

/-- The derived global sections functor of a brutal-truncation package kills the zero sheaf:
`H^q(X, 0) = 0` in every degree. The degree `q` is moved to the negative degree `-1` by the
commutation of the derived functor with the shift, a shift of the zero object being zero. -/
theorem isZero_homology_obj_single_of_isZero
    {M : _root_.SheafOfModules.{u} (structureSheafRing X)} (hM : IsZero M) (q : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) q).obj
      (S.RΓ.obj ((DerivedCategory.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj M))) := by
  have hM' : IsZero (((DerivedCategory.singleFunctor
      (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj M)⟦(-(-q - 1) : ℤ)⟧) :=
    (shiftFunctor _ _).map_isZero ((DerivedCategory.singleFunctor _ 0).map_isZero hM)
  refine IsZero.of_iso ?_ (shiftHypercohomologyIso X S.RΓ S.α S.isRightDerived M (-q - 1) q).symm
  exact isZero_homology_RΓ_of_isGE S _
    (fun i _ => (DerivedCategory.homologyFunctor _ i).map_isZero hM') (by omega)

/-- **The first page of the brutal-truncation spectral sequence of a complex concentrated in
nonnegative degrees lies in the first quadrant**: `E_1^{p, q} = H^q(X, F^p)` vanishes when
`p < 0`, because then `F^p = 0`, and when `q < 0`. -/
theorem isZero_page_one_of_neg [hF : F.IsStrictlyGE 0] (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero ((S.spectralSequence.page 1 le_rfl).X (p, q)) := by
  obtain ⟨e⟩ := S.e₁Iso p q
  refine IsZero.of_iso ?_ e
  rcases h with hp | hq
  · exact isZero_homology_obj_single_of_isZero S
      (CochainComplex.isZero_of_isStrictlyGE F 0 p hp) q
  · exact isZero_homology_obj_single_of_neg S _ hq

end FirstPage

/-! ### The Hodge-to-de Rham spectral sequence -/

section HodgeToDeRham

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}
variable {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **The first page of a brutal-truncation spectral sequence of the de Rham complex consists of
the Hodge groups**: `E_1^{p, q} ≅ H^q(X, Ω^p_{𝒪_X/A})` as modules over `A(X)`. The derived
global-sections functor of the package is a right derived functor of global sections, hence
isomorphic to the one Hodge cohomology is taken with. -/
theorem nonempty_page_one_iso_hodgeCohomologyComponent
    (S : StupidTruncationSpectralSequence (baseRingedSpace A) (deRhamComplexInt (X := X) B D))
    (p : ℕ) (q : ℤ) :
    Nonempty (hodgeCohomologyComponent (X := X) B p q ≅
      (S.spectralSequence.page 1 le_rfl).X ((p : ℤ), q)) := by
  have := S.isRightDerived
  obtain ⟨e⟩ := S.e₁Iso p q
  exact ⟨(e ≪≫ (DerivedCategory.homologyFunctor _ q).mapIso
    ((Functor.rightDerivedUnique S.RΓ (derivedSectionsBase A) S.α
      (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit (baseRingedSpace A) ⊤)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).app _ ≪≫
      (derivedSectionsBase A).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
        (deRhamComplexIntXIso B D p)))).symm⟩

/-- **The numerical criterion for `E_1`-degeneration of the Hodge-to-de Rham spectral
sequence, with lengths.** Let `S` be a brutal-truncation spectral sequence of the de Rham
complex abutting to `H^*_{dR}(X/A)`, as provided by
`AlgebraicGeometry.SheafOfModules.exists_hodgeToDeRhamSpectralSequence`, and suppose that the
Hodge groups `H^q(X, Ω^p)` have finite length over `A(X)`. Then `S` degenerates at `E_1` if and
only if `ℓ(H^n_{dR}) = ∑_{p + q = n} ℓ(H^q(X, Ω^p))` for every `n`. -/
theorem degeneratesAt_one_iff_length_deRham_eq_sum_hodge
    (S : StupidTruncationSpectralSequence (baseRingedSpace A) (deRhamComplexInt (X := X) B D))
    (hS : SpectralSequence.AbutsTo S.spectralSequence (deRhamCohomology (X := X) B D))
    (hfin : ∀ p q : ℕ, Module.length ((underlyingRingSheaf.{u, u} A).obj.obj (op ⊤))
      (hodgeCohomologyComponent (X := X) B p q) ≠ ⊤) :
    S.spectralSequence.DegeneratesAt 1 ↔ ∀ n : ℕ,
      Module.length ((underlyingRingSheaf.{u, u} A).obj.obj (op ⊤))
          (deRhamCohomology (X := X) B D n) =
        ∑ pq ∈ Finset.antidiagonal n, Module.length ((underlyingRingSheaf.{u, u} A).obj.obj (op ⊤))
          (hodgeCohomologyComponent (X := X) B pq.1 (pq.2 : ℤ)) := by
  let E : CohomologicalSpectralSequence
      (ModuleCat.{u} ((underlyingRingSheaf.{u, u} A).obj.obj (op ⊤))) 1 := S.spectralSequence
  have hlen : ∀ p q : ℕ, Module.length ((underlyingRingSheaf.{u, u} A).obj.obj (op ⊤))
      ((E.page 1 le_rfl).X ((p : ℤ), (q : ℤ))) =
        Module.length ((underlyingRingSheaf.{u, u} A).obj.obj (op ⊤))
          (hodgeCohomologyComponent (X := X) B p q) := fun p q =>
    (show hodgeCohomologyComponent (X := X) B p q ≅ (E.page 1 le_rfl).X ((p : ℤ), (q : ℤ)) from
      (nonempty_page_one_iso_hodgeCohomologyComponent B D S p q).some).toLinearEquiv.length_eq.symm
  have key := @degeneratesAt_iff_length_eq_sum_antidiagonal
    ((underlyingRingSheaf.{u, u} A).obj.obj (op ⊤))
    (inferInstanceAs (CommRing (A.obj.obj (op ⊤)))) _ E _ hS 1 le_rfl
    (isZero_page_one_of_neg S (hF := isStrictlyGE_deRhamComplexInt B D))
    fun p q => (hlen p q).trans_ne (hfin p q)
  exact key.trans (forall_congr' fun n => by
    rw [Finset.sum_congr rfl fun (pq : ℕ × ℕ) _ => hlen pq.1 pq.2])

/-- **The numerical criterion for `E_1`-degeneration of the Hodge-to-de Rham spectral
sequence, with dimensions over a field.** Let `S` be a brutal-truncation spectral sequence of
the de Rham complex abutting to `H^*_{dR}(X/A)`, let `k` be a field acting on `A(X)` through a
ring map `σ : k →+* A(X)`, and suppose that the Hodge groups `H^q(X, Ω^p)` are finite dimensional
over `k`. Then `S` degenerates at `E_1` if and only if
`dim_k H^n_{dR} = ∑_{p + q = n} dim_k H^q(X, Ω^p)` for every `n`.

This is the form in which [Stacks, Remark 0FWE] uses it, for `X` smooth projective over `k`: the
betti numbers of a Weil cohomology theory are dimensions over `k`. -/
theorem degeneratesAt_one_iff_finrank_deRham_eq_sum_hodge {k : Type w} [Field k]
    (σ : k →+* (underlyingRingSheaf.{u, u} A).obj.obj (op ⊤))
    (S : StupidTruncationSpectralSequence (baseRingedSpace A) (deRhamComplexInt (X := X) B D))
    (hS : SpectralSequence.AbutsTo S.spectralSequence (deRhamCohomology (X := X) B D))
    (hfin : ∀ p q : ℕ, FiniteDimensional k
      ((ModuleCat.restrictScalars.{u} σ).obj (hodgeCohomologyComponent (X := X) B p q))) :
    S.spectralSequence.DegeneratesAt 1 ↔ ∀ n : ℕ,
      Module.finrank k ((ModuleCat.restrictScalars.{u} σ).obj
          (deRhamCohomology (X := X) B D n)) =
        ∑ pq ∈ Finset.antidiagonal n, Module.finrank k
          ((ModuleCat.restrictScalars.{u} σ).obj
            (hodgeCohomologyComponent (X := X) B pq.1 (pq.2 : ℤ))) := by
  let E : CohomologicalSpectralSequence
      (ModuleCat.{u} ((underlyingRingSheaf.{u, u} A).obj.obj (op ⊤))) 1 := S.spectralSequence
  have hiso : ∀ p q : ℕ, Nonempty ((ModuleCat.restrictScalars.{u} σ).obj
      ((E.page 1 le_rfl).X ((p : ℤ), (q : ℤ))) ≅
        (ModuleCat.restrictScalars.{u} σ).obj (hodgeCohomologyComponent (X := X) B p q)) :=
    fun p q => ⟨(ModuleCat.restrictScalars.{u} σ).mapIso
      (nonempty_page_one_iso_hodgeCohomologyComponent B D S p q).some.symm⟩
  have hfinE : ∀ p q : ℕ, FiniteDimensional k ((ModuleCat.restrictScalars.{u} σ).obj
      ((E.page 1 le_rfl).X ((p : ℤ), (q : ℤ)))) := fun p q => by
    have := hfin p q
    exact (hiso p q).some.toLinearEquiv.symm.finiteDimensional
  have key := @degeneratesAt_iff_finrank_eq_sum_antidiagonal
    ((underlyingRingSheaf.{u, u} A).obj.obj (op ⊤))
    (inferInstanceAs (CommRing (A.obj.obj (op ⊤)))) _ E _ _ _ σ hS 1 le_rfl
    (isZero_page_one_of_neg S (hF := isStrictlyGE_deRhamComplexInt B D)) hfinE
  exact key.trans (forall_congr' fun n => by
    rw [Finset.sum_congr rfl fun (pq : ℕ × ℕ) _ => (hiso pq.1 pq.2).some.toLinearEquiv.finrank_eq])

end HodgeToDeRham

end Stacks.HodgeWeil

end
