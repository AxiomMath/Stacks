module

public import StacksFrontier.CategoryTheory.Subobject.CokernelOfLE
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CanonicalTruncation
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Cycles
public import StacksFrontier.Algebra.Homology.SpectralSequence.Kunneth
public import StacksFrontier.Algebra.Homology.SpectralSequence.Renumbering
public import StacksFrontier.CategoryTheory.Subobject.Butterfly
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Algebra.Homology.SpectralSequence.HomologicalFiltration

/-!
# The Künneth spectral sequence of two bounded complexes

Let `R` be a commutative ring and let `K` and `L` be cohomologically bounded complexes of
`R`-modules. Filtering `K` and `L` by their truncations `τ^{≤ i}` and applying the Künneth
spectral sequence of a pair of filtered complexes to those filtrations produces a bounded
cohomological spectral sequence
```
E₂^{p, q} = ⨁_{i + j = q} Tor_{-p}(H^i(K), H^j(L))  ⟹  H^{p + q}(K ⊗^L L),
```
the Künneth spectral sequence. The graded pieces of the truncation filtration are the cohomology
modules of `K` and `L`, placed in a single degree, so the first page of the filtered Künneth
sequence is a direct sum of hyper-tensor products of single complexes; resolving the first factor
projectively identifies those with the Tor modules of the cohomology.

Over a Dedekind domain every module has a two-term projective resolution, so `Tor_i` vanishes for
`i ≥ 2`. The second page of the Künneth spectral sequence is then concentrated in the two columns
`p = 0` and `p = -1`, every differential of every page vanishes, and the induced filtration on
`H^n(K ⊗^L L)` has a single step. The two edge maps of that filtration exhibit each cohomology
module of the derived tensor product as an extension
```
0 ⟶ ⨁_{i + j = n} H^i(K) ⊗ H^j(L) ⟶ H^n(K ⊗^L L) ⟶ ⨁_{i + j = n + 1} Tor_1(H^i(K), H^j(L)) ⟶ 0,
```
the Künneth short exact sequence.

## Main results

* `CochainComplex.Kunneth.exists_kunneth_spectral_sequence`: the Künneth spectral sequence of two
  bounded complexes of modules, with second page the direct sums of Tor modules of their
  cohomology and converging to the cohomology of their derived tensor product.
* `CochainComplex.Kunneth.tor_isZero_and_exists_kunneth_shortExact`: over a Dedekind domain the
  higher Tor modules vanish, the Künneth spectral sequence degenerates, and its edge maps are a
  short exact sequence computing the cohomology of a derived tensor product.

## Implementation notes

The derived tensor product is represented by the ordinary tensor product of K-flat replacements,
and the filtered representative of it is the one produced by the filtered Künneth construction
applied to the truncation filtrations. Since `Tor` is indexed by natural numbers, the half-plane
where the source asks for negative Tor degrees is stated separately as vanishing. Convergence is
expressed through the cycle and boundary subobjects of the filtered representative together with
their canonical comparison with the successive quotients of the induced finite filtration on
cohomology; under the reindexing used here the filtration degree belonging to `(p, q)` is `-q`.

The truncation filtration is decreasing in the opposite order to the truncation degree, so it is
indexed by `i ↦ τ^{≤ -i}`; it is eventually acyclic and eventually a quasi-isomorphism precisely
because `K` and `L` are bounded, which is what makes the filtered spectral sequence converge. The
subobjects of cycles and boundaries use raw representatives, so their stabilization equalities
carry the extra step `F (i + 1) n`, as do the preimages of the spectral cycles and boundaries.

Reindexing from the filtered sequence, whose first page carries the graded pieces, to the Künneth
sequence, whose second page carries the Tor modules, is performed by restricting each page along
the shift `(p, q) ↦ (-q, p + 2q)` of the index lattice, an isomorphism of complex shapes between
`up' (r, 1 - r)` and `up' (r - 1, 2 - r)`; that shift and the embedding of shapes it induces are
`CategoryTheory.SpectralSequence.truncationRenumberingEquiv` and
`CategoryTheory.SpectralSequence.truncationRenumberingEmbedding`.

The ring and the two complexes have independent universes. They are lifted to a common universe
and their scalars transported along `ULift.ringEquiv`, because the monoidal category of modules
and the functor `Tor'` both require the modules and the ring to share a universe.

Degeneration over a Dedekind domain is deduced from the vanishing of `Tor_i` for `i ≥ 2`, which in
turn comes from the kernel of a projective cover being torsion-free, hence flat: the two-column
support forces every differential to vanish and every page from the second on to be isomorphic to
the second, so the stable page is the second page and the two surviving columns are the two
successive quotients of the filtration on cohomology.

## References

* [The Stacks Project, Tag 0H7Z](https://stacks.math.columbia.edu/tag/0H7Z)
* [The Stacks Project, Tag 0H80](https://stacks.math.columbia.edu/tag/0H80)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CochainComplex.Kunneth

universe u v w u'

/-! ### Reindexing the filtered spectral sequence to the Künneth indexing -/

/-- A cohomological spectral sequence starting on the first page, reindexed to one starting on the
second page: the `r`-th page is the restriction of the `(r - 1)`-st along the index shift. -/
private noncomputable def kunnethReindex
    {C : Type*} [Category* C] [Abelian C]
    (E : CohomologicalSpectralSequence C 0) : E₂CohomologicalSpectralSequence C := by
  refine
    { page := fun r hr ↦ (E.page (r - 1) (by omega)).restriction
        (SpectralSequence.truncationRenumberingEmbedding r)
      iso := fun r r' pq hrr' hr ↦ ?_ }
  refine (E.page (r - 1) (by omega)).restrictionHomologyIso
    (SpectralSequence.truncationRenumberingEmbedding r)
    (pq - (r, 1 - r)) pq (pq + (r, 1 - r)) ?_ ?_ rfl rfl rfl ?_ ?_ ≪≫
      E.iso (r - 1) (r' - 1) (SpectralSequence.truncationRenumberingEquiv pq)
        (by omega) (by omega)
  · apply ComplexShape.prev_eq'
    change pq - (r, 1 - r) + (r, 1 - r) = pq
    exact sub_add_cancel _ _
  · apply ComplexShape.next_eq'
    rfl
  · apply ComplexShape.prev_eq'
    apply (SpectralSequence.truncationRenumberingEmbedding r).rel
    change pq - (r, 1 - r) + (r, 1 - r) = pq
    exact sub_add_cancel _ _
  · apply ComplexShape.next_eq'
    apply (SpectralSequence.truncationRenumberingEmbedding r).rel
    rfl

/-- The terms of the reindexed spectral sequence are the terms of the original at shifted
indices. -/
private lemma kunnethReindex_page_X
    {C : Type*} [Category* C] [Abelian C]
    (E : CohomologicalSpectralSequence C 0) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    ((kunnethReindex E).page r hr).X pq =
      (E.page (r - 1) (by omega)).X (SpectralSequence.truncationRenumberingEquiv pq) := rfl

/-- Finiteness of the support of a diagonal of the first page transfers to the second page of the
reindexed sequence. -/
private lemma kunnethReindex_finite_diagonal
    {C : Type*} [Category* C] [Abelian C]
    (E : CohomologicalSpectralSequence C 0)
    (hE : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite) :
    ∀ n : ℤ, {p : ℤ | ¬ IsZero (((kunnethReindex E).page 2).X (p, n - p))}.Finite := by
  intro n
  have h := (hE n).preimage
    (show Function.Injective (fun p : ℤ ↦ p - n) by
      intro a b h
      dsimp at h
      omega).injOn
  convert h using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, kunnethReindex_page_X]
  have hi : SpectralSequence.truncationRenumberingEquiv (p, n - p) = (p - n, n - (p - n)) := by
    ext <;> dsimp [SpectralSequence.truncationRenumberingEquiv] <;> omega
  rw [hi]
  rfl

/-- Eventual vanishing of the differentials transfers to the reindexed sequence. -/
private lemma kunnethReindex_eventually_d_eq_zero
    {C : Type*} [Category* C] [Abelian C]
    (E : CohomologicalSpectralSequence C 0)
    (hE : ∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) :
    ∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 2 ≤ r), b ≤ r →
      ((kunnethReindex E).page r hr).d (p, q) (p + r, q - r + 1) = 0 := by
  intro p q
  obtain ⟨b, hb⟩ := hE (-q) (p + 2 * q)
  refine ⟨b + 1, fun r hr hbr ↦ ?_⟩
  change (E.page (r - 1) (by omega)).d
    (SpectralSequence.truncationRenumberingEquiv (p, q))
    (SpectralSequence.truncationRenumberingEquiv (p + r, q - r + 1)) = 0
  have hi : SpectralSequence.truncationRenumberingEquiv (p + r, q - r + 1) =
      (-q + (r - 1), p + 2 * q - (r - 1) + 1) := by
    ext <;> dsimp [SpectralSequence.truncationRenumberingEquiv] <;> omega
  rw [hi]
  exact hb (r - 1) (by omega) (by omega)

/-! ### The truncation filtration of a bounded complex -/

/-- The `i`-th step of the truncation filtration is `τ^{≤ -i}`. -/
private lemma canonicalTruncationFiltration_obj
    {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (i : ℤ) :
    (canonicalTruncationFiltration K).filtration.obj (op i) = K.truncLE (-i) := rfl

/-- The `i`-th inclusion of the truncation filtration is `ιTruncLE (-i)`. -/
private lemma canonicalTruncationFiltration_ι_app
    {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (i : ℤ) :
    (canonicalTruncationFiltration K).filtration.ι.app (op i) = K.ιTruncLE (-i) := rfl

/-- For a complex concentrated in degrees `≥ a`, the steps of the truncation filtration are
eventually acyclic. -/
private lemma canonicalTruncationFiltration_eventually_acyclic
    {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (a : ℤ) [K.IsGE a] :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      ((canonicalTruncationFiltration K).filtration.obj (op i)).Acyclic := by
  refine ⟨-a, fun i hi ↦ ?_⟩
  rw [canonicalTruncationFiltration_obj, K.acyclic_truncLE_iff (-i) (-i + 1)]
  exact K.isGE_of_ge (-i + 1) a (by omega)

/-- For a complex concentrated in degrees `≤ b`, the steps of the truncation filtration are
eventually quasi-isomorphic to the whole complex. -/
private lemma canonicalTruncationFiltration_eventually_quasiIso
    {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (b : ℤ) [K.IsLE b] :
    ∃ a : ℤ, ∀ i : ℤ, i < a →
      QuasiIso ((canonicalTruncationFiltration K).filtration.ι.app (op i)) := by
  refine ⟨-b, fun i hi ↦ ?_⟩
  change QuasiIso (K.ιTruncLE (-i))
  rw [K.quasiIso_ιTruncLE_iff]
  exact K.isLE_of_le b (-i) (by omega)


/-- Any two quasi-isomorphisms onto a common target, the source of the first being K-projective,
are connected by a quasi-isomorphism. -/
private lemma exists_quasiIso_of_isKProjective
    {C : Type*} [Category* C] [Abelian C]
    {P Q K : CochainComplex C ℤ} [P.IsKProjective]
    (f : P ⟶ K) (g : Q ⟶ K) [QuasiIso f] [QuasiIso g] :
    ∃ h : P ⟶ Q, QuasiIso h := by
  let := HasDerivedCategory.standard C
  let H := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let F := DerivedCategory.Qh (C := C)
  have hiso {A B : CochainComplex C ℤ} (k : A ⟶ B) [QuasiIso k] : IsIso (F.map (H.map k)) := by
    rw [← Functor.comp_map]
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) k).2 inferInstance
  have := hiso f
  have := hiso g
  obtain ⟨h, hh⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P (H.obj Q)).surjective
    (F.map (H.map f) ≫ inv (F.map (H.map g)))
  obtain ⟨h', rfl⟩ := H.map_surjective h
  refine ⟨h', ?_⟩
  have : IsIso (F.map (H.map h')) := by
    rw [hh]
    infer_instance
  have : IsIso (DerivedCategory.Q.map h') :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) h').1 this
  rwa [DerivedCategory.isIso_Q_map_iff_quasiIso] at this

/-- A map of complexes is a quasi-isomorphism exactly when its mapping cone is acyclic. -/
private lemma quasiIso_iff_acyclic_mappingCone
    {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

/-- Tensoring a quasi-isomorphism with a K-flat complex gives a quasi-isomorphism. -/
private lemma quasiIso_tensorHom_id_of_kFlat
    {R : Type*} [CommRing R]
    {K L : CochainComplex (ModuleCat R) ℤ} (f : K ⟶ L) [QuasiIso f]
    (P : CochainComplex (ModuleCat R) ℤ) (hP : P.KFlat) :
    QuasiIso (f ⊗ₘ 𝟙 P) := by
  rw [quasiIso_iff_acyclic_mappingCone]
  exact (hP (CochainComplex.mappingCone f)
    ((quasiIso_iff_acyclic_mappingCone f).1 inferInstance)).of_iso
      (TrightCochain_mappingCone_iso P f)

/-- The cohomology of `P ⊗ T` for `T` K-flat depends only on the quasi-isomorphism class of `P`,
provided one of the two complexes compared is K-projective. -/
private lemma nonempty_homology_tensor_iso_of_isKProjective
    {R : Type*} [CommRing R]
    {P Q K : CochainComplex (ModuleCat R) ℤ} [P.IsKProjective]
    (f : P ⟶ K) (g : Q ⟶ K) [QuasiIso f] [QuasiIso g]
    (T : CochainComplex (ModuleCat R) ℤ) (hT : T.KFlat) (n : ℤ) :
    Nonempty ((P ⊗ T).homology n ≅ (Q ⊗ T).homology n) := by
  obtain ⟨h, hh⟩ := exists_quasiIso_of_isKProjective f g
  let := hh
  let := quasiIso_tensorHom_id_of_kFlat h T hT
  exact ⟨asIso (HomologicalComplex.homologyMap (h ⊗ₘ 𝟙 T) n)⟩

/-! ### Stabilization of the cycles and boundaries of a filtration -/

/-- One step of the stabilization of the filtered cycles: if the filtration is exact at the
relevant spot, then enlarging the target step by one does not change the cycles modulo the next
filtration step. -/
private lemma filtered_cycles_succ
    {R : Type*} [Ring R] {M N O : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup O]
    [Module R M] [Module R N] [Module R O]
    (d : M →ₗ[R] N) (e : N →ₗ[R] O) (hed : e.comp d = 0)
    (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (H : ℤ → Submodule R O)
    (hF : Antitone F) (hG : Antitone G) (p r : ℤ) (hr : 1 ≤ r)
    (hex : G (p + r) ⊓ (H (p + r + 1)).comap e ≤
      G (p + r + 1) ⊔ (F (p + r)).map d) :
    F p ⊓ (G (p + r)).comap d ⊔ F (p + 1) =
      F p ⊓ (G (p + (r + 1))).comap d ⊔ F (p + 1) := by
  apply le_antisymm
  · refine sup_le (fun x hx ↦ ?_) le_sup_right
    have hdx : d x ∈ G (p + r) ⊓ (H (p + r + 1)).comap e := by
      refine ⟨hx.2, ?_⟩
      change e (d x) ∈ H (p + r + 1)
      have hz := LinearMap.congr_fun hed x
      simpa using (hz ▸ (H (p + r + 1)).zero_mem)
    obtain ⟨z, hz, y', hy', hzy⟩ := Submodule.mem_sup.mp (hex hdx)
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hy'
    have hdy : d (x - y) = z := by
      rw [map_sub]
      exact sub_eq_of_eq_add hzy.symm
    have hy₁ : y ∈ F (p + 1) := hF (by omega) hy
    have hy₀ : y ∈ F p := hF (by omega) hy
    exact Submodule.mem_sup.mpr ⟨x - y,
      ⟨(F p).sub_mem hx.1 hy₀, by simpa [hdy, add_assoc] using hz⟩,
      y, hy₁, sub_add_cancel x y⟩
  · exact sup_le_sup_right (inf_le_inf_left _
      (Submodule.comap_mono (hG (by omega)))) _

/-- One step of the stabilization of the filtered boundaries. -/
private lemma filtered_boundaries_succ
    {R : Type*} [Ring R] {M N O : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup O]
    [Module R M] [Module R N] [Module R O]
    (d : M →ₗ[R] N) (e : N →ₗ[R] O) (hed : e.comp d = 0)
    (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (H : ℤ → Submodule R O)
    (hG : Antitone G) (hH : Antitone H) (p r : ℤ) (hr : 0 ≤ r)
    (hex : G (p - (r + 1)) ⊓ (H (p - r)).comap e ≤
      G (p - r) ⊔ (F (p - (r + 1))).map d) :
    H p ⊓ (G (p - (r + 1))).map e = H p ⊓ (G (p - r)).map e := by
  apply le_antisymm
  · rintro x ⟨hx, y, hy, rfl⟩
    have hey : e y ∈ H (p - r) := hH (by omega) hx
    obtain ⟨z, hz, w', hw', hzw⟩ := Submodule.mem_sup.mp (hex ⟨hy, hey⟩)
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hw'
    refine ⟨hx, z, hz, ?_⟩
    rw [← hzw, map_add]
    have hz := LinearMap.congr_fun hed w
    simpa using hz
  · exact inf_le_inf_left _ (Submodule.map_mono (hG (by omega)))

/-- An antitone family that is eventually constant equals its greatest lower bound from that
point on. -/
private lemma eq_isGLB_of_antitone_of_eventually_eq_succ
    {α : Type*} [PartialOrder α] (f : ℕ → α) (hf : Antitone f)
    {x : α} (hx : IsGLB (Set.range f) x) (b : ℕ)
    (hb : ∀ r, b ≤ r → f (r + 1) = f r) (r : ℕ) (hr : b ≤ r) : f r = x := by
  apply le_antisymm
  · apply hx.2
    rintro _ ⟨s, rfl⟩
    by_cases hsr : s ≤ r
    · exact hf hsr
    · have h : f s = f r := by
        have hrs : r ≤ s := by omega
        clear hsr
        induction s, hrs using Nat.le_induction with
        | base => rfl
        | succ k hk ih => exact (hb k (by omega)).trans ih
      exact h.ge
  · exact hx.1 ⟨r, rfl⟩

/-- A monotone family that is eventually constant equals its least upper bound from that point
on. -/
private lemma eq_isLUB_of_monotone_of_eventually_eq_succ
    {α : Type*} [PartialOrder α] (f : ℕ → α) (hf : Monotone f)
    {x : α} (hx : IsLUB (Set.range f) x) (b : ℕ)
    (hb : ∀ r, b ≤ r → f (r + 1) = f r) (r : ℕ) (hr : b ≤ r) : f r = x :=
  eq_isGLB_of_antitone_of_eventually_eq_succ (α := αᵒᵈ) f hf hx b hb r hr

/-- A subobject inclusion with vanishing cokernel is an equality. -/
private lemma le_of_isZero_cokernel_ofLE
    {C : Type*} [Category* C] [Abelian C] {X : C} {A B : Subobject X} (h : A ≤ B)
    (hz : IsZero (cokernel (Subobject.ofLE A B h))) : B ≤ A := by
  have : Epi (Subobject.ofLE A B h) := (Preadditive.epi_iff_isZero_cokernel _).2 hz
  have : IsIso (Subobject.ofLE A B h) := isIso_of_mono_of_epi _
  apply Subobject.le_of_comm (inv (Subobject.ofLE A B h))
  rw [← Subobject.ofLE_arrow h, IsIso.inv_hom_id_assoc]

/-! ### Cycles and boundaries of a filtered complex of modules -/

/-- The filtration of a filtered complex, presented by subobjects, is antitone. -/
private lemma antitone_filtration {C : Type*} [Category* C] [Abelian C]
    (T : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
    (hF : ∀ p n, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n))
    (n : ℤ) : Antitone (fun p => F p n) := by
  simp only [hF]
  intro p q hpq
  apply Subobject.mk_le_mk_of_comm
    ((T.filtration.diagram.map (homOfLE hpq).op).f n)
  have h : T.filtration.diagram.map (homOfLE hpq).op ≫ T.filtration.ι.app (op p) =
      T.filtration.ι.app (op q) := by simp
  exact congrArg (fun f => HomologicalComplex.Hom.f f n) h

/-- Each filtration step is carried into the corresponding step by the differential. -/
private lemma filtrationSubobject_le_pullback
    {C : Type*} [Category* C] [Abelian C]
    (T : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ) (p n m : ℤ) :
    Subobject.mk ((T.filtration.ι.app (op p)).f n) ≤
      (Subobject.pullback (T.X.d n m)).obj
        (Subobject.mk ((T.filtration.ι.app (op p)).f m)) := by
  refine Subobject.le_pullback_of_comm _
    ((Subobject.underlyingIso ((T.filtration.ι.app (op p)).f n)).hom ≫
      (T.filtration.diagram.obj (op p)).d n m ≫
      (Subobject.underlyingIso ((T.filtration.ι.app (op p)).f m)).inv) ?_
  rw [Category.assoc, Category.assoc, Subobject.underlyingIso_arrow,
    ← (T.filtration.ι.app (op p)).comm n m, ← Category.assoc,
    Subobject.underlyingIso_hom_comp_eq_mk]
  rfl

/-- The zeroth cycles of a filtered complex are the filtration steps themselves. -/
private lemma filtered_cycles_zero
    {C : Type*} [Category* C] [Abelian C]
    (T : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
    (hF : ∀ p n, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n))
    (p n : ℤ) : FilteredComplexSpectralSequence.cycles T.X F 0 p n = F p n := by
  simp only [FilteredComplexSpectralSequence.cycles, add_zero, inf_eq_left]
  simpa only [hF] using filtrationSubobject_le_pullback T p n (n + 1)

/-- A vanishing term on the first page is an exactness statement about the filtration, read in
submodules. -/
private lemma filtered_exact_of_isZero_first_page
    {R : Type*} [CommRing R]
    (T : FilteredObject (CochainComplex (ModuleCat.{u'} R) ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
    (hF : ∀ p n, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n))
    (p n : ℤ)
    (hz : IsZero (cokernel (Subobject.ofLE
      (FilteredComplexSpectralSequence.boundaries T.X F 1 p n ⊓
        FilteredComplexSpectralSequence.cycles T.X F 1 p n)
      (FilteredComplexSpectralSequence.cycles T.X F 1 p n) inf_le_right))) :
    ModuleCat.subobjectModule _ (F p n) ⊓
        (ModuleCat.subobjectModule _ (F (p + 1) (n + 1))).comap (T.X.d n (n + 1)).hom ≤
      ModuleCat.subobjectModule _ (F (p + 1) n) ⊔
        (ModuleCat.subobjectModule _ (F p (n - 1))).map (T.X.d (n - 1) n).hom := by
  have h := (le_of_isZero_cokernel_ofLE inf_le_right hz).trans inf_le_left
  simp only [FilteredComplexSpectralSequence.boundaries, show (1 : ℤ) - 1 = 0 from rfl,
    show p - 1 + 1 = p from by omega] at h
  rw [filtered_cycles_zero T F hF, filtered_cycles_zero T F hF] at h
  simp only [FilteredComplexSpectralSequence.cycles] at h
  have h' := (ModuleCat.subobjectModule (T.X.X n)).monotone h
  simpa only [OrderIso.map_inf, OrderIso.map_sup,
    CochainComplex.Tor.subobjectModule_pullback, CochainComplex.Tor.subobjectModule_exists] using h'

/-- Under eventual exactness of the filtration, the filtered cycles stabilize at their greatest
lower bound. -/
private lemma filtered_cycles_eventually_eq
    {R : Type*} [Ring R] {M N O : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup O]
    [Module R M] [Module R N] [Module R O]
    (d : M →ₗ[R] N) (e : N →ₗ[R] O) (hed : e.comp d = 0)
    (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (H : ℤ → Submodule R O)
    (hF : Antitone F) (hG : Antitone G) (p b : ℤ)
    (hex : ∀ j, b ≤ j → G j ⊓ (H (j + 1)).comap e ≤ G (j + 1) ⊔ (F j).map d)
    (Z : Submodule R M)
    (hZ : IsGLB (Set.range fun r : ℕ ↦ F p ⊓ (G (p + r)).comap d ⊔ F (p + 1)) Z) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → F p ⊓ (G (p + r)).comap d ⊔ F (p + 1) = Z := by
  let r₀ := max 1 (b - p).toNat
  refine ⟨r₀, fun r hr ↦ eq_isGLB_of_antitone_of_eventually_eq_succ _ ?_ hZ r₀ ?_ r hr⟩
  · intro i j hij
    exact sup_le_sup_right (inf_le_inf_left _ (Submodule.comap_mono (hG (by omega)))) _
  · intro s hs
    have hs' : 1 ≤ (s : ℤ) ∧ b ≤ p + s := by dsimp [r₀] at hs; omega
    simpa only [Nat.cast_add, Nat.cast_one] using
      (filtered_cycles_succ d e hed F G H hF hG p s hs'.1
        (hex (p + s) hs'.2)).symm

/-- Under eventual exactness of the filtration, the filtered boundaries stabilize at their least
upper bound. -/
private lemma filtered_boundaries_eventually_eq
    {R : Type*} [Ring R] {M N O : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup O]
    [Module R M] [Module R N] [Module R O]
    (d : M →ₗ[R] N) (e : N →ₗ[R] O) (hed : e.comp d = 0)
    (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (H : ℤ → Submodule R O)
    (hG : Antitone G) (hH : Antitone H) (p a : ℤ)
    (hex : ∀ j, j ≤ a → G j ⊓ (H (j + 1)).comap e ≤ G (j + 1) ⊔ (F j).map d)
    (B : Submodule R O)
    (hB : IsLUB (Set.range fun r : ℕ ↦ H p ⊓ (G (p - r)).map e ⊔ H (p + 1)) B) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → H p ⊓ (G (p - r)).map e ⊔ H (p + 1) = B := by
  let r₀ := (p - a).toNat
  refine ⟨r₀, fun r hr ↦ eq_isLUB_of_monotone_of_eventually_eq_succ _ ?_ hB r₀ ?_ r hr⟩
  · intro i j hij
    exact sup_le_sup_right (inf_le_inf_left _ (Submodule.map_mono (hG (by omega)))) _
  · intro s hs
    have hs' : p - ((s : ℤ) + 1) ≤ a := by dsimp [r₀] at hs; omega
    have h := filtered_boundaries_succ d e hed F G H hG hH p s (by omega)
      (by simpa only [show p - ((s : ℤ) + 1) + 1 = p - s from by omega]
        using hex (p - (s + 1)) hs')
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (· ⊔ H (p + 1)) h

/-- The intersection of the filtered boundaries with the filtered cycles, modulo the next
filtration step, is the image of a single filtration step under the differential. -/
private lemma filtered_boundaries_inf_cycles_sup
    {R : Type*} [Ring R] {M N O : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup O]
    [Module R M] [Module R N] [Module R O]
    (d : M →ₗ[R] N) (e : N →ₗ[R] O) (hed : e.comp d = 0)
    (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (H : ℤ → Submodule R O)
    (hG : Antitone G) (p r : ℤ) :
    ((G (p + 1) ⊓ (H (p + r)).comap e ⊔
        (F (p - r + 1) ⊓ (G p).comap d).map d) ⊓
      (G p ⊓ (H (p + r)).comap e)) ⊔ G (p + 1) =
      G p ⊓ (F (p - r + 1)).map d ⊔ G (p + 1) := by
  rw [← Submodule.map_inf_eq_map_inf_comap]
  have h₁ : G (p + 1) ⊓ (H (p + r)).comap e ≤ G p ⊓ (H (p + r)).comap e :=
    inf_le_inf_right _ (hG (by omega))
  have h₂ : (F (p - r + 1)).map d ⊓ G p ≤ G p ⊓ (H (p + r)).comap e := by
    rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨hy, ?_⟩
    change e (d x) ∈ H (p + r)
    have hz := LinearMap.congr_fun hed x
    simpa using hz ▸ (H (p + r)).zero_mem
  rw [inf_eq_left.mpr (sup_le h₁ h₂), sup_right_comm,
    sup_eq_right.mpr (inf_le_left : G (p + 1) ⊓ (H (p + r)).comap e ≤ G (p + 1)),
    sup_comm, inf_comm]

/-- The boundaries met with the cycles, modulo the next filtration step, are the image of a
filtration step under the differential. -/
private lemma filtered_boundary_preimage_eq
    {R : Type*} [CommRing R] (K : CochainComplex (ModuleCat.{u'} R) ℤ)
    (F : ∀ (_p n : ℤ), Subobject (K.X n))
    (hF : ∀ n, Antitone (fun p ↦ F p n)) (p r n : ℤ) :
    (FilteredComplexSpectralSequence.boundaries K F r p n ⊓
        FilteredComplexSpectralSequence.cycles K F r p n) ⊔ F (p + 1) n =
      F p n ⊓ (Subobject.«exists» (K.d (n - 1) n)).obj (F (p - r + 1) (n - 1)) ⊔
        F (p + 1) n := by
  apply (ModuleCat.subobjectModule (K.X n)).injective
  simp only [FilteredComplexSpectralSequence.boundaries,
    FilteredComplexSpectralSequence.cycles,
    show p + 1 + (r - 1) = p + r from by omega,
    show p - r + 1 + (r - 1) = p from by omega,
    OrderIso.map_sup, OrderIso.map_inf, CochainComplex.Tor.subobjectModule_exists,
    CochainComplex.Tor.subobjectModule_pullback]
  rw [show (ModuleCat.subobjectModule (K.X (n - 1 + 1)) (F p (n - 1 + 1))).comap
      (K.d (n - 1) (n - 1 + 1)).hom =
      (ModuleCat.subobjectModule (K.X n) (F p n)).comap (K.d (n - 1) n).hom from
    congrArg (fun m ↦ (ModuleCat.subobjectModule (K.X m) (F p m)).comap
      (K.d (n - 1) m).hom) (by omega)]
  exact filtered_boundaries_inf_cycles_sup (K.d (n - 1) n).hom (K.d n (n + 1)).hom
    (by rw [← ModuleCat.hom_comp, K.d_comp_d]; rfl)
    (fun i ↦ ModuleCat.subobjectModule _ (F i (n - 1)))
    (fun i ↦ ModuleCat.subobjectModule _ (F i n))
    (fun i ↦ ModuleCat.subobjectModule _ (F i (n + 1)))
    ((ModuleCat.subobjectModule _).monotone.comp_antitone (hF n)) p r

/-- If every diagonal of the first page has finite support, then the filtered cycles and
boundaries stabilize, and their limits are the ordinary cycles and boundaries met with the
filtration step. -/
private lemma filtered_preimages_eventually_eq_of_finite_first_page
    {R : Type*} [CommRing R]
    (T : FilteredObject (CochainComplex (ModuleCat.{u'} R) ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
    (hF : ∀ p n, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n))
    (N B : ∀ (_p n : ℤ), Subobject (T.X.X n))
    (hN : ∀ p n, IsGLB (Set.range fun r : ℕ ↦
      F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔
        F (p + 1) n) (N p n))
    (hB : ∀ p n, IsLUB (Set.range fun r : ℕ ↦
      F p n ⊓ (Subobject.«exists» (T.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔
        F (p + 1) n) (B p n))
    (hfinite : ∀ n : ℤ, {p : ℤ | ¬ IsZero (cokernel (Subobject.ofLE
      (FilteredComplexSpectralSequence.boundaries T.X F 1 p n ⊓
        FilteredComplexSpectralSequence.cycles T.X F 1 p n)
      (FilteredComplexSpectralSequence.cycles T.X F 1 p n) inf_le_right))}.Finite)
    (p n : ℤ) :
    ∃ r₀ : ℤ, 1 ≤ r₀ ∧ ∀ r : ℤ, r₀ ≤ r →
      FilteredComplexSpectralSequence.cycles T.X F r p n ⊔ F (p + 1) n = N p n ∧
      (FilteredComplexSpectralSequence.boundaries T.X F r p n ⊓
        FilteredComplexSpectralSequence.cycles T.X F r p n) ⊔
        F (p + 1) n = B p n ⊓ N p n := by
  classical
  let S (i m : ℤ) := ModuleCat.subobjectModule (T.X.X m) (F i m)
  have hanti := antitone_filtration T F hF
  have hsanti (m : ℤ) : Antitone (fun i ↦ S i m) :=
    (ModuleCat.subobjectModule _).monotone.comp_antitone (hanti m)
  obtain ⟨b, hb⟩ := (hfinite (n + 1)).bddAbove
  obtain ⟨a, ha⟩ := (hfinite (n - 1)).bddBelow
  have hz (i : ℤ) (hi : b + 1 ≤ i) := filtered_exact_of_isZero_first_page T F hF i (n + 1)
    (by by_contra h; have := hb h; omega)
  have hd (i : ℤ) (hi : i ≤ a - 1) := filtered_exact_of_isZero_first_page T F hF i (n - 1)
    (by by_contra h; have := ha h; omega)
  have hglb : IsGLB (Set.range fun r : ℕ ↦
      S p n ⊓ (S (p + r) (n + 1)).comap (T.X.d n (n + 1)).hom ⊔ S (p + 1) n)
      (ModuleCat.subobjectModule _ (N p n)) := by
    have h := ((ModuleCat.subobjectModule (T.X.X n)).isGLB_image').2 (hN p n)
    simpa only [← Set.range_comp, Function.comp_def, OrderIso.map_sup, OrderIso.map_inf,
      CochainComplex.Tor.subobjectModule_pullback] using h
  have hlub : IsLUB (Set.range fun r : ℕ ↦
      S p n ⊓ (S (p - r) (n - 1)).map (T.X.d (n - 1) n).hom ⊔ S (p + 1) n)
      (ModuleCat.subobjectModule _ (B p n)) := by
    have h := ((ModuleCat.subobjectModule (T.X.X n)).isLUB_image').2 (hB p n)
    simpa only [← Set.range_comp, Function.comp_def, OrderIso.map_sup, OrderIso.map_inf,
      CochainComplex.Tor.subobjectModule_exists] using h
  obtain ⟨s, hs⟩ := filtered_cycles_eventually_eq
    (T.X.d n (n + 1)).hom (T.X.d (n + 1) (n + 1 + 1)).hom
    (by rw [← ModuleCat.hom_comp, T.X.d_comp_d]; rfl)
    (fun i ↦ S i n) (fun i ↦ S i (n + 1)) (fun i ↦ S i (n + 1 + 1))
    (hsanti n) (hsanti (n + 1)) p (b + 1)
    (by
      intro i hi
      have h := hz i hi
      rw [show (ModuleCat.subobjectModule _ (F i (n + 1 - 1))).map
          (T.X.d (n + 1 - 1) (n + 1)).hom =
          (ModuleCat.subobjectModule _ (F i n)).map (T.X.d n (n + 1)).hom from
        congrArg (fun m ↦ (ModuleCat.subobjectModule _ (F i m)).map
          (T.X.d m (n + 1)).hom) (by omega)] at h
      exact h)
    _ hglb
  obtain ⟨t, ht⟩ := filtered_boundaries_eventually_eq
    (T.X.d (n - 1 - 1) (n - 1)).hom (T.X.d (n - 1) n).hom
    (by rw [← ModuleCat.hom_comp, T.X.d_comp_d]; rfl)
    (fun i ↦ S i (n - 1 - 1)) (fun i ↦ S i (n - 1)) (fun i ↦ S i n)
    (hsanti (n - 1)) (hsanti n) p (a - 1)
    (by
      intro i hi
      have h := hd i hi
      rw [show (ModuleCat.subobjectModule _ (F (i + 1) (n - 1 + 1))).comap
          (T.X.d (n - 1) (n - 1 + 1)).hom =
          (ModuleCat.subobjectModule _ (F (i + 1) n)).comap (T.X.d (n - 1) n).hom from
        congrArg (fun m ↦ (ModuleCat.subobjectModule _ (F (i + 1) m)).comap
          (T.X.d (n - 1) m).hom) (by omega)] at h
      exact h)
    _ hlub
  refine ⟨max (s : ℤ) (t + 1), by omega, fun r hr ↦ ?_⟩
  have heN : FilteredComplexSpectralSequence.cycles T.X F r p n ⊔ F (p + 1) n = N p n := by
    apply (ModuleCat.subobjectModule (T.X.X n)).injective
    simpa only [FilteredComplexSpectralSequence.cycles, OrderIso.map_sup, OrderIso.map_inf,
      CochainComplex.Tor.subobjectModule_pullback, Int.toNat_of_nonneg (show 0 ≤ r by omega)] using
      hs r.toNat (by omega)
  have heB : (FilteredComplexSpectralSequence.boundaries T.X F r p n ⊓
      FilteredComplexSpectralSequence.cycles T.X F r p n) ⊔
      F (p + 1) n = B p n := by
    rw [filtered_boundary_preimage_eq T.X F hanti]
    apply (ModuleCat.subobjectModule (T.X.X n)).injective
    have h := ht (r - 1).toNat (by omega)
    simpa only [OrderIso.map_sup, OrderIso.map_inf, CochainComplex.Tor.subobjectModule_exists,
      Int.toNat_of_nonneg (show 0 ≤ r - 1 by omega),
      show p - (r - 1) = p - r + 1 from by omega] using h
  refine ⟨heN, heB.trans (inf_eq_left.mpr ?_).symm⟩
  rw [← heB, ← heN]
  exact sup_le_sup_right inf_le_right _

/-! ### Tensoring a projective resolution with a single complex computes Tor -/

/-- Commutativity of the tensor product of modules, read on the bicomplex of a tensor product
of two cochain complexes. -/
@[ega "III 6.3.5" "(i), special case"]
private noncomputable def tensorBicomplexFlipIso
    {R : Type*} [CommRing R] (K L : CochainComplex (ModuleCat R) ℤ) :
    (((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L ≅
    (((curriedTensor (ModuleCat R)).flip.mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ (TensorProduct.comm R (K.X p) (L.X q)).toModuleIso)
      (by intros; ext : 1; apply TensorProduct.ext'; intros; rfl))
    (by intros; ext q : 2; apply TensorProduct.ext'; intros; rfl)

/-- The tensor product of cochain complexes of modules is commutative. -/
private noncomputable def tensorFlipIso
    {R : Type*} [CommRing R] (K L : CochainComplex (ModuleCat R) ℤ) : K ⊗ L ≅ L ⊗ K :=
  HomologicalComplex₂.total.mapIso (tensorBicomplexFlipIso K L) (ComplexShape.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)

/-- The `-k`-th cohomology of the tensor product of a projective resolution of `M` with `N`
placed in degree `0` is `Tor_k(M, N)`. -/
private noncomputable def projectiveResolutionTensorSingleHomologyIso
    {R : Type*} [CommRing R] (M N : ModuleCat R) (k : ℕ) :
    ((ProjectiveResolution.of M).cochainComplex ⊗
      (CochainComplex.singleFunctor (ModuleCat R) 0).obj N).homology (-(k : ℤ)) ≅
      ((Tor' (ModuleCat R) k).obj M).obj N := by
  let P := ProjectiveResolution.of M
  let eA := StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso
    N P.cochainComplex
  let eB := StacksDraft.TorAmplitude.FaithfullyFlat.mapHomologicalComplexExtendIso N P.complex
  let eC := ((tensorLeft N).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  exact (HomologicalComplex.homologyFunctor _ _ (-(k : ℤ))).mapIso
      (tensorFlipIso _ _ ≪≫ eA ≪≫ eB) ≪≫
    eC.extendHomologyIso ComplexShape.embeddingDownNat (by rfl) ≪≫
    (HomologicalComplex.homologyFunctor _ _ k).mapIso
      ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight N)
        (ComplexShape.down ℕ)).app P.complex) ≪≫
    (P.isoLeftDerivedObj (tensorRight N) k).symm

/-- In positive degrees the tensor product of a projective resolution with a single complex is
acyclic. -/
private lemma isZero_projectiveResolutionTensorSingle_homology
    {R : Type*} [CommRing R] (M N : ModuleCat R) (k : ℤ) (hk : 0 < k) :
    IsZero (((ProjectiveResolution.of M).cochainComplex ⊗
      (CochainComplex.singleFunctor (ModuleCat R) 0).obj N).homology k) := by
  let P := ProjectiveResolution.of M
  let e := tensorFlipIso P.cochainComplex ((CochainComplex.singleFunctor _ 0).obj N) ≪≫
    StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso
      N P.cochainComplex
  apply IsZero.of_iso _ ((HomologicalComplex.homologyFunctor _ _ k).mapIso e)
  apply ShortComplex.isZero_homology_of_isZero_X₂
  exact (tensorLeft N).map_isZero (P.cochainComplex.isZero_of_isStrictlyLE 0 k hk)

/-- The cohomology of a tensor product of two complexes quasi-isomorphic to single complexes is
the cohomology of the tensor product of a projective resolution with a single complex. -/
private lemma nonempty_homology_tensor_iso_projectiveResolution
    {R : Type*} [CommRing R] (P Q : CochainComplex (ModuleCat R) ℤ)
    (M N : ModuleCat R) (i j n : ℤ)
    (f : P ⟶ (CochainComplex.singleFunctor (ModuleCat R) i).obj M)
    (g : Q ⟶ (CochainComplex.singleFunctor (ModuleCat R) j).obj N)
    [QuasiIso f] [QuasiIso g] (hQ : Q.KFlat) :
    Nonempty ((P ⊗ Q).homology n ≅
      ((ProjectiveResolution.of M).cochainComplex ⊗
        (CochainComplex.singleFunctor (ModuleCat R) 0).obj N).homology (n - i - j)) := by
  let A := (ProjectiveResolution.of M).cochainComplex
  let A' := A⟦-i⟧
  have hle : A'.IsStrictlyLE i := A.isStrictlyLE_shift 0 (-i) i (by omega)
  have hproj (m : ℤ) : Projective (A'.X m) := by
    change Projective (A.X (m + -i))
    infer_instance
  have hkp : A'.IsKProjective := CochainComplex.isKProjective_of_projective A' i
  have hflat : ∀ m : ℤ, Module.Flat R (A'.X m) := fun m => by
    have : Module.Projective R (A'.X m) := inferInstance
    infer_instance
  have hA' : A'.KFlat := CochainComplex.KFlat.kFlat_of_flat A' i
  let ei := ((CochainComplex.singleFunctors (ModuleCat R)).shiftIso (-i) i 0 (by omega)).app M
  let ej := ((CochainComplex.singleFunctors (ModuleCat R)).shiftIso (-j) j 0 (by omega)).app N
  let fA : A' ⟶ (CochainComplex.singleFunctor (ModuleCat R) i).obj M :=
    (ProjectiveResolution.of M).π'⟦-i⟧' ≫ ei.hom
  have hfA : QuasiIso fA := by dsimp [fA]; infer_instance
  obtain ⟨e₁⟩ := nonempty_homology_tensor_iso_of_isKProjective fA f Q hQ n
  have hgA := quasiIso_tensorHom_id_of_kFlat g A' hA'
  let e₂ := (HomologicalComplex.homologyFunctor _ _ n).mapIso (tensorFlipIso A' Q)
  let e₃ := asIso (HomologicalComplex.homologyMap (g ⊗ₘ 𝟙 A') n)
  let e₄ := tensorFlipIso ((CochainComplex.singleFunctor _ j).obj N) A' ≪≫
    (tensorLeft A').mapIso ej.symm ≪≫
    CochainComplex.mapBifunctorShift₁Iso A
      (((CochainComplex.singleFunctor _ 0).obj N)⟦-j⟧) (curriedTensor (ModuleCat R)) (-i) ≪≫
    (shiftFunctor _ (-i)).mapIso
      (CochainComplex.mapBifunctorShift₂Iso A ((CochainComplex.singleFunctor _ 0).obj N)
        (curriedTensor (ModuleCat R)) (-j))
  refine ⟨e₁.symm ≪≫ e₂ ≪≫ e₃ ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso e₄ ≪≫ ?_⟩
  exact (CochainComplex.ShiftSequence.shiftIso (ModuleCat R) (-i) n (n - i)
      (by omega)).app _ ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat R) (-j) (n - i) (n - i - j)
      (by omega)).app _

/-- An additive functor preserving homology preserves lower bounds on cohomological support. -/
private lemma isGE_mapHomologicalComplex
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (K : CochainComplex C ℤ) (a : ℤ) [K.IsGE a] :
    CochainComplex.IsGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (F.map_isZero (K.isZero_of_isGE a n hn)).of_iso ((K.sc n).mapHomologyIso F)

/-- An additive functor preserving homology preserves upper bounds on cohomological support. -/
private lemma isLE_mapHomologicalComplex
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (K : CochainComplex C ℤ) (a : ℤ) [K.IsLE a] :
    CochainComplex.IsLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a := by
  rw [CochainComplex.isLE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (F.map_isZero (K.isZero_of_isLE a n hn)).of_iso ((K.sc n).mapHomologyIso F)

/-- Negating both coordinates identifies the index sets of the two Künneth direct sums. -/
private def negPairEquiv (q : ℤ) :
    {ij : ℤ × ℤ // ij.1 + ij.2 = -q} ≃ {ij : ℤ × ℤ // ij.1 + ij.2 = q} where
  toFun ij := ⟨(-ij.1.1, -ij.1.2), by have := ij.2; dsimp; omega⟩
  invFun ij := ⟨(-ij.1.1, -ij.1.2), by have := ij.2; dsimp; omega⟩
  left_inv ij := by ext <;> simp
  right_inv ij := by ext <;> simp

/-- A coproduct of zero objects is zero. -/
private lemma isZero_sigma_of_isZero
    {C : Type*} [Category* C] [Preadditive C] {J : Type*} (G : J → C) [HasCoproduct G]
    (hG : ∀ j, IsZero (G j)) : IsZero (∐ G) := by
  rw [IsZero.iff_id_eq_zero]
  ext j
  simp only [Category.comp_id, comp_zero]
  exact (hG j).eq_of_src _ _

/-- In non-positive degrees the cohomology of a projective resolution tensored with a single
complex is a Tor module. -/
private lemma nonempty_projectiveResolutionTensorSingle_homology_iso_tor
    {R : Type*} [CommRing R] (M N : ModuleCat R) (m : ℤ) (hm : m ≤ 0) :
    Nonempty (((ProjectiveResolution.of M).cochainComplex ⊗
      (CochainComplex.singleFunctor (ModuleCat R) 0).obj N).homology m ≅
        ((Tor' (ModuleCat R) (-m).toNat).obj M).obj N) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
  rw [show (-(-(k : ℤ))).toNat = k by omega]
  exact ⟨projectiveResolutionTensorSingleHomologyIso M N k⟩

/-- The cohomology of the tensor product of the `i`-th and `j`-th graded pieces is that of a
projective resolution of `H^{-i}(K)` tensored with the single complex `H^{-j}(L)`. -/
private lemma nonempty_gradedPiece_tensor_homology_iso_projectiveResolution
    {R : Type*} [CommRing R]
    (K L : CochainComplex (ModuleCat R) ℤ)
    (P Q : FilteredObject (CochainComplex (ModuleCat R) ℤ) ℤᵒᵖ)
    (f : P ⟶ canonicalTruncationFiltration K) (g : Q ⟶ canonicalTruncationFiltration L)
    (hfgr : ∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map f))
    (hggr : ∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map g))
    (hQgr : ∀ i : ℤ, ((FilteredObject.gr i).obj Q).KFlat)
    (i j n : ℤ) :
    Nonempty ((((FilteredObject.gr i).obj P) ⊗
      ((FilteredObject.gr j).obj Q)).homology n ≅
      ((ProjectiveResolution.of (K.homology (-i))).cochainComplex ⊗
        (CochainComplex.singleFunctor (ModuleCat R) 0).obj (L.homology (-j))).homology
          (n + i + j)) := by
  have := hfgr i
  have := hggr j
  have := quasiIso_truncationGradedPieceToSingle K i
  have := quasiIso_truncationGradedPieceToSingle L j
  obtain ⟨e₁⟩ := nonempty_homology_tensor_iso_projectiveResolution
    ((FilteredObject.gr i).obj P) ((FilteredObject.gr j).obj Q)
    (K.homology (-i)) (L.homology (-j)) (-i) (-j) n
    ((FilteredObject.gr i).map f ≫ truncationGradedPieceToSingle K i)
    ((FilteredObject.gr j).map g ≫ truncationGradedPieceToSingle L j)
    (hQgr j)
  rw [show n - -i - -j = n + i + j by omega] at e₁
  exact ⟨e₁⟩

/-- **The Künneth summands are Tor modules.** For filtered resolutions `P` and `Q` of the
truncation filtrations of `K` and `L`, the cohomology of the tensor product of the `i`-th and
`j`-th graded pieces is `Tor_{-(n + i + j)}(H^{-i}(K), H^{-j}(L))` in every degree `n` where
that Tor index is non-negative. -/
private lemma nonempty_gradedPiece_tensor_homology_iso_tor
    {R : Type*} [CommRing R]
    (K L : CochainComplex (ModuleCat R) ℤ)
    (P Q : FilteredObject (CochainComplex (ModuleCat R) ℤ) ℤᵒᵖ)
    (f : P ⟶ canonicalTruncationFiltration K) (g : Q ⟶ canonicalTruncationFiltration L)
    (hfgr : ∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map f))
    (hggr : ∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map g))
    (hQgr : ∀ i : ℤ, ((FilteredObject.gr i).obj Q).KFlat)
    (i j n : ℤ) (hn : n + i + j ≤ 0) :
    Nonempty ((((FilteredObject.gr i).obj P) ⊗
      ((FilteredObject.gr j).obj Q)).homology n ≅
      ((Tor' (ModuleCat R) (-(n + i + j)).toNat).obj (K.homology (-i))).obj
        (L.homology (-j))) := by
  obtain ⟨e₁⟩ := nonempty_gradedPiece_tensor_homology_iso_projectiveResolution
    K L P Q f g hfgr hggr hQgr i j n
  obtain ⟨e₂⟩ := nonempty_projectiveResolutionTensorSingle_homology_iso_tor
    (K.homology (-i)) (L.homology (-j)) (n + i + j) hn
  exact ⟨e₁ ≪≫ e₂⟩

/-- **The Künneth summands vanish above the diagonal.** In the degrees where the Tor index
`-(n + i + j)` would be negative, the cohomology of the tensor product of the `i`-th and `j`-th
graded pieces vanishes. -/
private lemma isZero_gradedPiece_tensor_homology
    {R : Type*} [CommRing R]
    (K L : CochainComplex (ModuleCat R) ℤ)
    (P Q : FilteredObject (CochainComplex (ModuleCat R) ℤ) ℤᵒᵖ)
    (f : P ⟶ canonicalTruncationFiltration K) (g : Q ⟶ canonicalTruncationFiltration L)
    (hfgr : ∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map f))
    (hggr : ∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map g))
    (hQgr : ∀ i : ℤ, ((FilteredObject.gr i).obj Q).KFlat)
    (i j n : ℤ) (hn : 0 < n + i + j) :
    IsZero ((((FilteredObject.gr i).obj P) ⊗
      ((FilteredObject.gr j).obj Q)).homology n) := by
  obtain ⟨e₁⟩ := nonempty_gradedPiece_tensor_homology_iso_projectiveResolution
    K L P Q f g hfgr hggr hQgr i j n
  exact (isZero_projectiveResolutionTensorSingle_homology _ _ _ (by omega)).of_iso e₁

/-- **Regularity of the reindexed spectral sequence.** If the differentials of a filtered
spectral sequence eventually vanish, the terms of its first page have finite support in each
total degree, and the filtered cycles and boundaries converge to the ordinary ones met with the
filtration step, then from some page on the reindexed sequence has vanishing differential at
`(p, q)` and its cycles and boundaries there have reached their stable values. -/
private lemma kunnethReindex_regular
    {R : Type*} [CommRing R]
    (T : FilteredObject (CochainComplex (ModuleCat.{u'} R) ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
    (Z D : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
    (hF : ∀ p n, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
    (E : CohomologicalSpectralSequence (ModuleCat.{u'} R) 0)
    (hd : ∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0)
    (hfinite : ∀ n : ℤ, {i : ℤ | ¬ IsZero (cokernel (Subobject.ofLE
      (D 1 i n ⊓ Z 1 i n) (Z 1 i n) inf_le_right))}.Finite)
    (hglb : ∀ p n : ℤ,
      IsGLB (Set.range fun r : ℕ ↦
          F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj
            (F (p + r) (n + 1)) ⊔ F (p + 1) n)
        (kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ ↦
          F p n ⊓ (Subobject.«exists» (T.X.d (n - 1) n)).obj
            (F (p - r) (n - 1)) ⊔ F (p + 1) n)
        (imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n))
    (p q : ℤ) :
    ∃ (r₀ : ℤ) (hr₀ : 2 ≤ r₀), ∀ (r : ℤ) (hr : r₀ ≤ r),
      ((kunnethReindex E).page r (by omega)).d (p, q) (p + r, q - r + 1) = 0 ∧
        Z (r - 1) (-q) (p + q) ⊔ F (-q + 1) (p + q) =
          kernelSubobject (T.X.d (p + q) (p + q + 1)) ⊓ F (-q) (p + q) ⊔ F (-q + 1) (p + q) ∧
        (D (r - 1) (-q) (p + q) ⊓ Z (r - 1) (-q) (p + q)) ⊔ F (-q + 1) (p + q) =
          (imageSubobject (T.X.d (p + q - 1) (p + q)) ⊓ F (-q) (p + q) ⊔ F (-q + 1) (p + q)) ⊓
            (kernelSubobject (T.X.d (p + q) (p + q + 1)) ⊓ F (-q) (p + q) ⊔
              F (-q + 1) (p + q)) := by
  have hZ' : Z = FilteredComplexSpectralSequence.cycles T.X F := by
    funext r p n
    exact hZ r p n
  subst hZ'
  have hD' : D = FilteredComplexSpectralSequence.boundaries T.X F := by
    funext r p n
    exact hD r p n
  subst hD'
  obtain ⟨b, hb⟩ := kunnethReindex_eventually_d_eq_zero E hd p q
  obtain ⟨r₁, hr₁, hr₁'⟩ := filtered_preimages_eventually_eq_of_finite_first_page T F hF
    (fun i m ↦ kernelSubobject (T.X.d m (m + 1)) ⊓ F i m ⊔ F (i + 1) m)
    (fun i m ↦ imageSubobject (T.X.d (m - 1) m) ⊓ F i m ⊔ F (i + 1) m)
    (fun i m ↦ (hglb i m).1) (fun i m ↦ (hglb i m).2) hfinite (-q) (p + q)
  refine ⟨max 2 (max b (r₁ + 1)), le_max_left _ _, fun r hr ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := hr₁' (r - 1) (by omega)
  exact ⟨hb r (by omega) (by omega), h₁, h₂⟩

/-- **The second page of the reindexed sequence is a direct sum of Tor modules.** In the half-plane
`p ≤ 0`, where the Tor index `-p` is non-negative, the reindexing carries a first page whose terms
are the direct sums of the cohomology of the tensor products of the graded pieces to a second page
whose terms are the direct sums of the Tor modules of the cohomology of `K` and `L`. -/
private lemma nonempty_kunnethReindex_page_two_iso_tor
    {R : Type*} [CommRing R]
    (K L : CochainComplex (ModuleCat R) ℤ)
    (P Q : FilteredObject (CochainComplex (ModuleCat R) ℤ) ℤᵒᵖ)
    (f : P ⟶ canonicalTruncationFiltration K) (g : Q ⟶ canonicalTruncationFiltration L)
    (hfgr : ∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map f))
    (hggr : ∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map g))
    (hQgr : ∀ i : ℤ, ((FilteredObject.gr i).obj Q).KFlat)
    (E : CohomologicalSpectralSequence (ModuleCat R) 0)
    (hE1 : ∀ p q : ℤ, Nonempty ((E.page 1 (by omega)).X (p, q) ≅
      ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = p} ↦
        (((FilteredObject.gr ij.1.1).obj P) ⊗
          ((FilteredObject.gr ij.1.2).obj Q)).homology (p + q)))
    (p q : ℤ) (hp : p ≤ 0) :
    Nonempty (((kunnethReindex E).page 2).X (p, q) ≅
      ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} ↦
        ((Tor' (ModuleCat R) (-p).toNat).obj (K.homology ij.1.1)).obj
          (L.homology ij.1.2)) := by
  obtain ⟨e₁⟩ := hE1 (-q) (p + 2 * q)
  refine ⟨e₁ ≪≫ Sigma.whiskerEquiv (negPairEquiv q) (fun ij ↦ ?_)⟩
  have h := nonempty_gradedPiece_tensor_homology_iso_tor K L P Q f g hfgr hggr hQgr
    ij.1.1 ij.1.2 (-q + (p + 2 * q)) (by have := ij.2; omega)
  rw [show -(-q + (p + 2 * q) + ij.1.1 + ij.1.2) = -p by have := ij.2; omega] at h
  exact h.some.symm

/-- **The second page of the reindexed sequence vanishes below the diagonal.** In the half-plane
`0 < p` the Tor index `-p` is negative, and the tensor products of the graded pieces contributing
to that term are acyclic in the relevant degree. -/
private lemma isZero_kunnethReindex_page_two
    {R : Type*} [CommRing R]
    (K L : CochainComplex (ModuleCat R) ℤ)
    (P Q : FilteredObject (CochainComplex (ModuleCat R) ℤ) ℤᵒᵖ)
    (f : P ⟶ canonicalTruncationFiltration K) (g : Q ⟶ canonicalTruncationFiltration L)
    (hfgr : ∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map f))
    (hggr : ∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map g))
    (hQgr : ∀ i : ℤ, ((FilteredObject.gr i).obj Q).KFlat)
    (E : CohomologicalSpectralSequence (ModuleCat R) 0)
    (hE1 : ∀ p q : ℤ, Nonempty ((E.page 1 (by omega)).X (p, q) ≅
      ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = p} ↦
        (((FilteredObject.gr ij.1.1).obj P) ⊗
          ((FilteredObject.gr ij.1.2).obj Q)).homology (p + q)))
    (p q : ℤ) (hp : 0 < p) :
    IsZero (((kunnethReindex E).page 2).X (p, q)) := by
  obtain ⟨e₁⟩ := hE1 (-q) (p + 2 * q)
  refine IsZero.of_iso (isZero_sigma_of_isZero _ fun ij ↦ ?_) e₁
  exact isZero_gradedPiece_tensor_homology K L P Q f g hfgr hggr hQgr
    ij.1.1 ij.1.2 _ (by have := ij.2; omega)

/-! ### The Künneth spectral sequence -/

/-- **Künneth spectral sequence.** For bounded complexes `K` and `L` of modules over a
commutative ring, there is a bounded cohomological spectral sequence with
`E₂^(p,q) = ⊕_(i+j=q) Tor_(-p)(H^i(K), H^j(L))`, converging to the cohomology in degree
`p + q` of the derived tensor product. The derived tensor product is represented here by the
tensor product of K-flat replacements of `K` and `L`. -/
@[stacks 0H7Z,
  ega "III 6.3.2" "(6.3.2.2)",
  ega "III 6.5.4" "(6.5.4.2)",
  ega "III 6.8.2" "m=2, modules over a ring"]
public theorem exists_kunneth_spectral_sequence
    (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (L : CochainComplex (ModuleCat.{w} R) ℤ)
    (aK bK aL bL : ℤ) [K.IsGE aK] [K.IsLE bK] [L.IsGE aL] [L.IsLE bL] :
    let S := ULift.{max v w} R
    let U : ModuleCat.{v} R ⥤ ModuleCat.{max u v w} S :=
      ModuleCat.uliftFunctor.{max u w} R ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom
    let V : ModuleCat.{w} R ⥤ ModuleCat.{max u v w} S :=
      ModuleCat.uliftFunctor.{max u v} R ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom
    let K' := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    let L' := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
    ∃ (P Q : CochainComplex (ModuleCat S) ℤ) (f : P ⟶ K') (g : Q ⟶ L')
      (_ : QuasiIso f) (_ : QuasiIso g) (_ : P.KFlat) (_ : Q.KFlat)
      (T : FilteredObject (CochainComplex (ModuleCat S) ℤ) ℤᵒᵖ)
      (eT : P ⊗ Q ≅ T.X)
      (E : E₂CohomologicalSpectralSequence (ModuleCat S))
      (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
      (Z : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
      (D : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
      (FH : ∀ (_n _p : ℤ), Subobject (T.X.homology _n))
      (hE : ∀ (r p q : ℤ) (hr : 2 ≤ r), (E.page r hr).X (p, q) ≅
        cokernel (Subobject.ofLE _ _
          (inf_le_right : D (r - 1) (-q) (p + q) ⊓ Z (r - 1) (-q) (p + q) ≤
            Z (r - 1) (-q) (p + q)))),
      (∀ p n : ℤ, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n)) ∧
      (∀ r p n : ℤ, Z r p n =
        F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1))) ∧
      (∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
        (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1))) ∧
      (∀ n p : ℤ, FH n p =
        imageSubobject (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n)) ∧
      (∀ p q : ℤ, p ≤ 0 →
        Nonempty ((E.page 2).X (p, q) ≅
          ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} ↦
            ((Tor' (ModuleCat S) (-p).toNat).obj (K'.homology ij.1.1)).obj
              (L'.homology ij.1.2))) ∧
      (∀ p q : ℤ, 0 < p → IsZero ((E.page 2).X (p, q))) ∧
      (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 2).X (p, n - p))}.Finite) ∧
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
      (∀ p q : ℤ, ∃ (r₀ : ℤ) (hr₀ : 2 ≤ r₀), ∀ (r : ℤ) (hr : r₀ ≤ r),
        let n := p + q
        let i := -q
        let N := kernelSubobject (T.X.d n (n + 1)) ⊓ F i n ⊔ F (i + 1) n
        let B := imageSubobject (T.X.d (n - 1) n) ⊓ F i n ⊔ F (i + 1) n
        (E.page r (by omega)).d (p, q) (p + r, q - r + 1) = 0 ∧
          Z (r - 1) i n ⊔ F (i + 1) n = N ∧
          (D (r - 1) i n ⊓ Z (r - 1) i n) ⊔ F (i + 1) n = B ⊓ N) ∧
      (∀ p n : ℤ,
        let A := (Subobject.pullback (T.X.iCycles n)).obj (F p n)
        let N := kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
        let B := imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
        ∃ (a : (A : ModuleCat S) ⟶ (N : ModuleCat S))
          (b : (A : ModuleCat S) ⟶
            image (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))
          (e : cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) ≅
            cokernel (image.preComp
              (HomologicalComplex.homologyMap (T.filtration.diagram.map
                (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
              (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))),
          A.arrow ≫ T.X.iCycles n = a ≫ N.arrow ∧
          A.arrow ≫ T.X.homologyπ n =
            b ≫ image.ι (HomologicalComplex.homologyMap
              (T.filtration.ι.app (op p)) n) ∧
          a ≫ cokernel.π (Subobject.ofLE (B ⊓ N) N inf_le_right) ≫ e.hom =
            b ≫ cokernel.π (image.preComp
              (HomologicalComplex.homologyMap (T.filtration.diagram.map
                (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
              (HomologicalComplex.homologyMap
                (T.filtration.ι.app (op p)) n))) := by
  intro S U V K' L'
  have hK'ge : CochainComplex.IsGE K' aK := isGE_mapHomologicalComplex U K aK
  have hK'le : CochainComplex.IsLE K' bK := isLE_mapHomologicalComplex U K bK
  have hL'ge : CochainComplex.IsGE L' aL := isGE_mapHomologicalComplex V L aL
  have hL'le : CochainComplex.IsLE L' bL := isLE_mapHomologicalComplex V L bL
  obtain ⟨P, Q, f, g, T, eT, ⟨-, -, -, hPK, -, hPgr, hf, -, hfgr⟩,
    ⟨-, -, -, hQK, -, hQgr, hg, -, hggr⟩, -, F, Z, D, FH, E, hE, hF, hZ, hD, hFH, hE1,
    hbd⟩ := exists_kunneth_filtered_complex S
      (canonicalTruncationFiltration K') (canonicalTruncationFiltration L')
  obtain ⟨hfin, hFH', hd, hglb, hconv⟩ := hbd
    ⟨canonicalTruncationFiltration_eventually_acyclic K' aK,
      canonicalTruncationFiltration_eventually_quasiIso K' bK,
      canonicalTruncationFiltration_eventually_acyclic L' aL,
      canonicalTruncationFiltration_eventually_quasiIso L' bL⟩
  have hfin' : ∀ n : ℤ, {i : ℤ | ¬ IsZero (cokernel (Subobject.ofLE
      (D 1 i n ⊓ Z 1 i n) (Z 1 i n) inf_le_right))}.Finite := by
    intro n
    have hset : {i : ℤ | ¬ IsZero (cokernel (Subobject.ofLE
        (D 1 i n ⊓ Z 1 i n) (Z 1 i n) inf_le_right))} =
        {i : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (i, n - i))} := by
      ext i
      exact not_congr ⟨fun h ↦ h.of_iso (hE 1 i (n - i) n (by omega) (by omega)),
        fun h ↦ h.of_iso (hE 1 i (n - i) n (by omega) (by omega)).symm⟩
    rw [hset]
    exact hfin n
  have hpage := fun (r p q : ℤ) (hr : 2 ≤ r) ↦
    hE (r - 1) (-q) (p + 2 * q) (p + q) (by omega) (by omega)
  have htor := nonempty_kunnethReindex_page_two_iso_tor K' L' P Q f g hfgr hggr hQgr E hE1
  have hzero := isZero_kunnethReindex_page_two K' L' P Q f g hfgr hggr hQgr E hE1
  have hfindiag := kunnethReindex_finite_diagonal E hfin
  -- The module universe of `T` and `E` is written out as `u'` in `kunnethReindex_regular` and in
  -- the `ModuleCat`-specific helpers it calls. Left implicit, a bare `ModuleCat R` in those
  -- signatures does not auto-bind that level: it is defaulted to `0`, so the `Subobject` lattice
  -- is expected in `Type (max 1 …)` where `T` supplies `Type (… + 1)` and this application does
  -- not elaborate.
  have hreg := kunnethReindex_regular T F Z D hF hZ hD E hd hfin' hglb
  exact ⟨P.X, Q.X, f.hom, g.hom, hf, hg, hPK, hQK, T, eT, kunnethReindex E, F, Z, D, FH,
    hpage, hF, hZ, hD, hFH, htor, hzero, hfindiag, hFH', hreg, hconv⟩

/-! ### Degeneration of a spectral sequence supported in two columns -/

section TwoColumns

variable {C : Type*} [Category* C] [Abelian C]

/-- A spectral sequence whose second page is supported in the columns `p = -1` and `p = 0` has
every later page supported there too. -/
private lemma page_isZero_of_two_columns (E : E₂CohomologicalSpectralSequence C)
    (h : ∀ p q, p ≠ -1 → p ≠ 0 → IsZero ((E.page 2).X (p, q)))
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hp : p ≠ -1) (hp' : p ≠ 0) :
    IsZero ((E.page r hr).X (p, q)) := by
  induction r, hr using Int.leInduction with
  | base => exact h p q hp hp'
  | succ r hr ih =>
    exact ((HomologicalComplex.ExactAt.of_isZero ih).isZero_homology).of_iso
      (E.iso r (r + 1) (p, q)).symm

/-- Every differential of every page of a spectral sequence supported in the two columns
`p = -1` and `p = 0` vanishes: the differential moves the column by `r ≥ 2`, so one of its
endpoints lies outside the support. -/
private lemma page_d_eq_zero_of_two_columns (E : E₂CohomologicalSpectralSequence C)
    (h : ∀ p q, p ≠ -1 → p ≠ 0 → IsZero ((E.page 2).X (p, q)))
    (r : ℤ) (hr : 2 ≤ r) (a b : ℤ × ℤ) : (E.page r hr).d a b = 0 := by
  by_cases hab : (ComplexShape.up' (r, 1 - r)).Rel a b
  · have hab' : a + (r, 1 - r) = b := hab
    by_cases ha : a.1 = -1 ∨ a.1 = 0
    · exact (page_isZero_of_two_columns E h r hr b.1 b.2
        (by have := congrArg Prod.fst hab'; simp only [Prod.fst_add] at this; omega)
        (by have := congrArg Prod.fst hab'; simp only [Prod.fst_add] at this; omega)).eq_of_tgt _ _
    · exact (page_isZero_of_two_columns E h r hr a.1 a.2
        (by omega) (by omega)).eq_of_src _ _
  · exact (E.page r hr).shape a b hab

/-- Since all differentials vanish, every page of a two-column spectral sequence is isomorphic to
the second page. -/
private lemma nonempty_page_iso_of_two_columns (E : E₂CohomologicalSpectralSequence C)
    (h : ∀ p q, p ≠ -1 → p ≠ 0 → IsZero ((E.page 2).X (p, q)))
    (r : ℤ) (hr : 2 ≤ r) (a : ℤ × ℤ) :
    Nonempty ((E.page 2).X a ≅ (E.page r hr).X a) := by
  induction r, hr using Int.leInduction with
  | base => exact ⟨Iso.refl _⟩
  | succ r hr ih =>
    obtain ⟨e⟩ := ih
    let eH : (E.page r hr).homology a ≅ (E.page r hr).X a :=
      (ShortComplex.HomologyData.ofZeros ((E.page r hr).sc a)
        (page_d_eq_zero_of_two_columns E h r hr _ _)
        (page_d_eq_zero_of_two_columns E h r hr _ _)).left.homologyIso
    exact ⟨e ≪≫ eH.symm ≪≫ E.iso r (r + 1) a⟩

/-- Adding a subobject `F` to both terms of an inclusion `B ≤ A` does not change the cokernel,
provided `F` meets `A` inside `B`. -/
private lemma nonempty_cokernel_sup_iso {X : C} (A B F : Subobject X)
    (hBA : B ≤ A) (hAF : A ⊓ F ≤ B) :
    Nonempty (cokernel (Subobject.ofLE B A hBA) ≅
      cokernel (Subobject.ofLE (B ⊔ F) (A ⊔ F) (sup_le_sup_right hBA F))) := by
  let m := Subobject.ofLE B A hBA
  let m' := Subobject.ofLE (B ⊔ F) (A ⊔ F) (sup_le_sup_right hBA F)
  let j := Subobject.ofLE A (A ⊔ F) le_sup_left
  have hj : j ≫ (A ⊔ F).arrow = A.arrow := Subobject.ofLE_arrow _
  have hjmk : A ≤ Subobject.mk (j ≫ (A ⊔ F).arrow) :=
    Subobject.le_mk_of_comm (𝟙 _) (by simpa using hj)
  have : Epi (j ≫ cokernel.π m') :=
    Subobject.epi_comp_cokernel_π (Y := F) m' (Subobject.ofLE_arrow _) j
      (sup_le_sup_right hjmk F) le_sup_right
  have : Epi ((𝟙 (A : C)) ≫ cokernel.π m) := by simpa using inferInstanceAs (Epi (cokernel.π m))
  obtain ⟨e, -⟩ := Subobject.exists_iso_cokernel_of_factors_iff m (Subobject.ofLE_arrow _)
    m' (Subobject.ofLE_arrow _) (𝟙 (A : C)) j (by
      intro T g
      simp only [Category.id_comp, hj]
      constructor
      · exact Subobject.factors_of_le _ le_sup_left
      · intro hg
        have hcut : (B ⊔ F) ⊓ A ≤ B := by
          rw [sup_inf_assoc_of_le _ hBA]
          exact sup_le le_rfl (by simpa [inf_comm] using hAF)
        exact Subobject.factors_of_le _ hcut
          ((Subobject.inf_factors _).2 ⟨hg, Subobject.factors_comp_arrow g⟩))
  exact ⟨e⟩

/-- The cokernel of the comparison of images of `f ≫ g` and `g` is the cokernel of the
corresponding subobject inclusion. -/
private lemma cokernel_image_preComp_iso {X Y H : C} (f : X ⟶ Y) (g : Y ⟶ H) :
    Nonempty (cokernel (image.preComp f g) ≅
      cokernel (Subobject.ofLE _ _ (imageSubobject_comp_le f g))) := by
  refine ⟨cokernel.mapIso _ _ (imageSubobjectIso (f ≫ g)).symm
    (imageSubobjectIso g).symm ?_⟩
  rw [← cancel_mono (imageSubobject g).arrow]
  simp

/-- The induced filtration on cohomology is antitone. -/
private lemma antitone_homology_filtration
    (T : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ)
    (FH : ∀ n _p, Subobject (T.X.homology n))
    (hFH : ∀ n p, FH n p = imageSubobject
      (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))
    (n : ℤ) : Antitone (FH n) := by
  intro p p' hp
  rw [hFH, hFH]
  have heq : HomologicalComplex.homologyMap (T.filtration.ι.app (op p')) n =
      HomologicalComplex.homologyMap (T.filtration.diagram.map (homOfLE hp).op) n ≫
      HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun f => HomologicalComplex.homologyMap f n) (by simp)
  rw [heq]
  exact imageSubobject_comp_le _ _

/-- The cokernel of an inclusion of the zero subobject is the ambient subobject. -/
private lemma cokernel_bot_iso {X : C} {A B : Subobject X} (h : A ≤ B) (hA : A = ⊥) :
    Nonempty (cokernel (Subobject.ofLE A B h) ≅ (B : C)) := by
  have hz : IsZero (A : C) := by
    subst A
    exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
  exact ⟨cokernelIsoOfEq (hz.eq_of_src (Subobject.ofLE A B h) 0) ≪≫ cokernelZeroIsoTarget⟩

/-- The cokernel of an inclusion into the top subobject is the cokernel of the arrow. -/
private lemma cokernel_top_iso {X : C} {A B : Subobject X} (h : A ≤ B) (hB : B = ⊤) :
    Nonempty (cokernel (Subobject.ofLE A B h) ≅ cokernel A.arrow) := by
  have := (Subobject.isIso_arrow_iff_eq_top B).mpr hB
  exact ⟨cokernel.mapIso _ _ (Iso.refl _) (asIso B.arrow) (by simp)⟩

/-- A family on `ℤ` that is constant across each single step on an interval is constant on that
interval. -/
private lemma eq_of_eq_succ_on {α : Sort*} (f : ℤ → α) {a b : ℤ} (hab : a ≤ b)
    (h : ∀ p, a ≤ p → p < b → f (p + 1) = f p) : f b = f a := by
  induction b, hab using Int.leInduction with
  | base => rfl
  | succ b hb ih => exact (h b hb (by omega)).trans (ih (fun p hp hp' => h p hp (by omega)))

end TwoColumns

/-! ### Vanishing of the higher Tor modules over a Dedekind domain -/

/-- Tensoring a module on the right preserves finite colimits. Tensoring on the left is a left
adjoint for the closed monoidal structure, hence preserves all colimits, and the braiding
identifies the two. -/
private instance preservesFiniteColimits_tensorRight {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) : PreservesFiniteColimits (tensorRight M) :=
  ⟨fun _ _ _ ↦ ⟨inferInstance⟩⟩

/-- Being a Dedekind domain transports along a ring isomorphism. -/
private lemma isDedekindDomain_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] (e : R ≃+* S) : IsDedekindDomain S := by
  have hdomain : IsDomain S := Function.Injective.isDomain e.symm e.symm.injective
  have hnoeth := isNoetherianRing_of_ringEquiv R e
  have hdim := Ring.DimensionLEOne.of_ringEquiv e.symm
  have hclosed := IsIntegrallyClosed.of_equiv e
  have hring : IsDedekindRing S := IsDedekindRing.mk
  exact IsDedekindDomain.mk

/-- Over a Dedekind domain the kernel of a projective cover is torsion-free, hence flat. -/
private lemma syzygy_flat {R : Type u} [CommRing R] [IsDedekindDomain R]
    (N : ModuleCat.{u} R) : Module.Flat R (kernel (Projective.π N) : ModuleCat R) := by
  have : Module.IsTorsionFree R (kernel (Projective.π N) : ModuleCat R) :=
    Function.Injective.moduleIsTorsionFree (kernel.ι (Projective.π N))
      ((ModuleCat.mono_iff_injective _).mp inferInstance) (fun r m => map_smul _ r m)
  infer_instance

/-- The higher left derived functors of an exact functor vanish. -/
private lemma isZero_leftDerived_succ_of_exact
    {C : Type*} [Category* C] [Abelian C] [HasProjectiveResolutions C]
    {D : Type*} [Category* D] [Abelian D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (n : ℕ) (X : C) : IsZero ((G.leftDerived (n + 1)).obj X) := by
  refine IsZero.of_iso ?_ ((projectiveResolution X).isoLeftDerivedObj G (n + 1))
  have h : ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (projectiveResolution X).complex).ExactAt (n + 1) :=
    ((projectiveResolution X).complex_exactAt_succ n).map G
  exact h.isZero_homology

/-- A short exact sequence of functors, degreewise exact on a projective resolution, propagates
vanishing of left derived functors from its first two terms to its third. -/
private lemma isZero_leftDerived_X₃
    {C : Type*} [Category* C] [Abelian C] [HasProjectiveResolutions C]
    {D : Type*} [Category* D] [Abelian D]
    (T : ShortComplex (C ⥤ D)) [T.X₁.Additive] [T.X₂.Additive] [T.X₃.Additive]
    {M : C} (P : ProjectiveResolution M)
    (hT : ∀ n : ℕ, (T.map ((evaluation C D).obj (P.complex.X n))).ShortExact)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (h₂ : IsZero ((T.X₂.leftDerived i).obj M))
    (h₁ : IsZero ((T.X₁.leftDerived j).obj M)) :
    IsZero ((T.X₃.leftDerived i).obj M) := by
  have hz : (NatTrans.mapHomologicalComplex T.f (ComplexShape.down ℕ)).app P.complex ≫
      (NatTrans.mapHomologicalComplex T.g (ComplexShape.down ℕ)).app P.complex = 0 := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, T.zero]
    ext n
    simp
  let U := ShortComplex.mk _ _ hz
  have hU : U.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact U hT
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj T.X₃ i)
  refine (hU.homology_exact₃ i j hij).isZero_X₂ ?_ ?_
  · exact (h₂.of_iso (P.isoLeftDerivedObj T.X₂ i).symm).eq_of_src _ _
  · exact (h₁.of_iso (P.isoLeftDerivedObj T.X₁ j).symm).eq_of_tgt _ _

/-- **Tor vanishes in degrees at least two over a Dedekind domain**, because every module has a
projective resolution of length one: the kernel of a projective cover is torsion-free, hence
flat, so tensoring with it is exact. -/
@[sga "7 VIII 2.1" "special case"]
private lemma tor'_isZero_of_two_le {R : Type u} [CommRing R] [IsDedekindDomain R]
    (M N : ModuleCat.{u} R) (i : ℕ) (hi : 2 ≤ i) :
    IsZero (((Tor' (ModuleCat R) i).obj M).obj N) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  have := syzygy_flat N
  let S := ShortComplex.kernelSequence (Projective.π N)
  have hS : S.ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _
      mono_f := inferInstance
      epi_g := inferInstanceAs (Epi (Projective.π N)) }
  have hz : (tensoringRight (ModuleCat R)).map S.f ≫
      (tensoringRight (ModuleCat R)).map S.g = 0 := by
    rw [← Functor.map_comp, S.zero, Functor.map_zero]
  let T := ShortComplex.mk _ _ hz
  have h₂ := isZero_leftDerived_succ_of_exact
    ((tensoringRight (ModuleCat R)).obj (Projective.over N)) (j + 1) M
  have h₁ := isZero_leftDerived_succ_of_exact
    ((tensoringRight (ModuleCat R)).obj (kernel (Projective.π N))) j M
  refine isZero_leftDerived_X₃ T (projectiveResolution M) (fun n => ?_)
    (j + 2) (j + 1) rfl h₂ h₁
  exact hS.map_of_exact (tensorLeft ((projectiveResolution M).complex.X n))

/-! ### The Künneth short exact sequence over a Dedekind domain -/

set_option backward.defeqAttrib.useBackward true in
/-- **Künneth short exact sequence over a Dedekind domain.** Higher Tor modules vanish over a
Dedekind domain. Thus the bounded Künneth spectral sequence degenerates at `E₂`, and its edge
maps exhibit the cohomology of a derived tensor product as an extension of the direct sum of
tensor products in total degree `n` by the direct sum of first Tor modules in total degree
`n + 1`. -/
@[stacks 0H80, ega "III 7.6.4" "(i) short exact sequence"]
public theorem tor_isZero_and_exists_kunneth_shortExact
    (R : Type u) [CommRing R] [IsDedekindDomain R] :
    let S := ULift.{max v w} R
    let U : ModuleCat.{v} R ⥤ ModuleCat.{max u v w} S :=
      ModuleCat.uliftFunctor.{max u w} R ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom
    let V : ModuleCat.{w} R ⥤ ModuleCat.{max u v w} S :=
      ModuleCat.uliftFunctor.{max u v} R ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom
    (∀ (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (i : ℕ), i ≠ 0 → i ≠ 1 →
      IsZero (((Tor' (ModuleCat S) i).obj (U.obj M)).obj (V.obj N))) ∧
    ∀ (K : CochainComplex (ModuleCat.{v} R) ℤ) (L : CochainComplex (ModuleCat.{w} R) ℤ)
      (aK bK aL bL : ℤ) [K.IsGE aK] [K.IsLE bK] [L.IsGE aL] [L.IsLE bL],
      let K' := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
      let L' := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
      ∃ (P Q : CochainComplex (ModuleCat S) ℤ) (f : P ⟶ K') (g : Q ⟶ L')
        (_ : QuasiIso f) (_ : QuasiIso g) (_ : P.KFlat) (_ : Q.KFlat)
        (T : FilteredObject (CochainComplex (ModuleCat S) ℤ) ℤᵒᵖ)
        (eT : P ⊗ Q ≅ T.X)
        (E : E₂CohomologicalSpectralSequence (ModuleCat S))
        (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
        (Z : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
        (D : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
        (FH : ∀ (_n _p : ℤ), Subobject (T.X.homology _n))
        (_hE : ∀ (r p q : ℤ) (hr : 2 ≤ r), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _
            (inf_le_right : D (r - 1) (-q) (p + q) ⊓ Z (r - 1) (-q) (p + q) ≤
              Z (r - 1) (-q) (p + q))))
        (e₂ : ∀ (p q : ℤ) (_hp : p ≤ 0), (E.page 2).X (p, q) ≅
          ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} ↦
            ((Tor' (ModuleCat S) (-p).toNat).obj (K'.homology ij.1.1)).obj
              (L'.homology ij.1.2)),
        (∀ p n : ℤ, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n)) ∧
        (∀ r p n : ℤ, Z r p n =
          F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1))) ∧
        (∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1))) ∧
        (∀ n p : ℤ, FH n p =
          imageSubobject (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n)) ∧
        (∀ p q : ℤ, 0 < p → IsZero ((E.page 2).X (p, q))) ∧
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 2).X (p, n - p))}.Finite) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
        (∀ p q : ℤ, ∃ (r₀ : ℤ) (hr₀ : 2 ≤ r₀), ∀ (r : ℤ) (hr : r₀ ≤ r),
          let n := p + q
          let i := -q
          let N := kernelSubobject (T.X.d n (n + 1)) ⊓ F i n ⊔ F (i + 1) n
          let B := imageSubobject (T.X.d (n - 1) n) ⊓ F i n ⊔ F (i + 1) n
          (E.page r (by omega)).d (p, q) (p + r, q - r + 1) = 0 ∧
            Z (r - 1) i n ⊔ F (i + 1) n = N ∧
            (D (r - 1) i n ⊓ Z (r - 1) i n) ⊔ F (i + 1) n = B ⊓ N) ∧
        (∀ p n : ℤ,
          let A := (Subobject.pullback (T.X.iCycles n)).obj (F p n)
          let N := kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
          let B := imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
          ∃ (a : (A : ModuleCat S) ⟶ (N : ModuleCat S))
            (b : (A : ModuleCat S) ⟶
              image (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))
            (e : cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) ≅
              cokernel (image.preComp
                (HomologicalComplex.homologyMap (T.filtration.diagram.map
                  (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
                (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))),
            (A.arrow ≫ T.X.iCycles n = a ≫ N.arrow ∧
            A.arrow ≫ T.X.homologyπ n =
              b ≫ image.ι (HomologicalComplex.homologyMap
                (T.filtration.ι.app (op p)) n) ∧
            a ≫ cokernel.π (Subobject.ofLE (B ⊓ N) N inf_le_right) ≫ e.hom =
              b ≫ cokernel.π (image.preComp
                (HomologicalComplex.homologyMap (T.filtration.diagram.map
                  (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
                (HomologicalComplex.homologyMap
                  (T.filtration.ι.app (op p)) n)))) ∧
        (∀ (r p q : ℤ) (hr : 2 ≤ r),
          (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
        ∀ n : ℤ,
          FH n (-n - 1) = ⊤ ∧ FH n (-n + 1) = ⊥ ∧
          ∃ (torZeroTensor :
              (∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} ↦
                ((Tor' (ModuleCat S) (-0 : ℤ).toNat).obj
                  (K'.homology ij.1.1)).obj (L'.homology ij.1.2)) ≅
              ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} ↦
                K'.homology ij.1.1 ⊗ L'.homology ij.1.2)
            (torOne :
              (∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n + 1} ↦
                ((Tor' (ModuleCat S) (-(-1 : ℤ)).toNat).obj
                  (K'.homology ij.1.1)).obj (L'.homology ij.1.2)) ≅
              ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n + 1} ↦
                ((Tor' (ModuleCat S) 1).obj (K'.homology ij.1.1)).obj
                  (L'.homology ij.1.2))
            (eTensor : (E.page 2).X (0, n) ≅
              ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} ↦
                K'.homology ij.1.1 ⊗ L'.homology ij.1.2)
            (eTor : (E.page 2).X (-1, n + 1) ≅
              ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n + 1} ↦
                ((Tor' (ModuleCat S) 1).obj (K'.homology ij.1.1)).obj
                  (L'.homology ij.1.2))
            (e₀ : (E.page 2).X (0, n) ≅ (FH n (-n) : ModuleCat S))
            (e₁ : (E.page 2).X (-1, n + 1) ≅ cokernel (FH n (-n)).arrow)
            (ι : (∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} ↦
                K'.homology ij.1.1 ⊗ L'.homology ij.1.2) ⟶ (P ⊗ Q).homology n)
            (π : (P ⊗ Q).homology n ⟶
              ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n + 1} ↦
                ((Tor' (ModuleCat S) 1).obj (K'.homology ij.1.1)).obj
                  (L'.homology ij.1.2))
            (h : ι ≫ π = 0),
            eTensor = (e₂ 0 n (by omega)).trans torZeroTensor ∧
            eTor = (e₂ (-1) (n + 1) (by omega)).trans torOne ∧
            ι = eTensor.inv ≫ e₀.hom ≫ (FH n (-n)).arrow ≫
                HomologicalComplex.homologyMap eT.inv n ∧
            π = HomologicalComplex.homologyMap eT.hom n ≫
                cokernel.π (FH n (-n)).arrow ≫ e₁.inv ≫ eTor.hom ∧
            (ShortComplex.mk ι π h).ShortExact := by
  classical
  dsimp only
  let S := ULift.{max v w} R
  let U : ModuleCat.{v} R ⥤ ModuleCat.{max u v w} S :=
    ModuleCat.uliftFunctor.{max u w} R ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom
  let V : ModuleCat.{w} R ⥤ ModuleCat.{max u v w} S :=
    ModuleCat.uliftFunctor.{max u v} R ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom
  have : IsDedekindDomain S := isDedekindDomain_of_ringEquiv ULift.ringEquiv.symm
  refine ⟨fun M N i h₀ h₁ => tor'_isZero_of_two_le (U.obj M) (V.obj N) i (by omega), ?_⟩
  intro K L aK bK aL bL hKa hKb hLa hLb
  let K' := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let L' := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  obtain ⟨P, Q, f, g, hf, hg, hP, hQ, T, eT, E, F, Z, D, FH, hE,
    hF, hZ, hD, hFH, he₂, hpos, hfin, hbound, hstab, hcomp⟩ :=
    exists_kunneth_spectral_sequence R K L aK bK aL bL
  let e₂ := fun p q hp => (he₂ p q hp).some
  have hsupport : ∀ p q, p ≠ -1 → p ≠ 0 → IsZero ((E.page 2).X (p, q)) := by
    intro p q hp hp'
    by_cases h : 0 < p
    · exact hpos p q h
    · refine IsZero.of_iso ?_ (e₂ p q (by omega))
      exact (colimit.isColimit _).isZero_pt (Functor.isZero _ (fun ij =>
        tor'_isZero_of_two_le _ _ _ (by omega)))
  have hanti := antitone_filtration T F hF
  have hantiH := antitone_homology_filtration T FH hFH
  have egr : ∀ p n, Nonempty ((E.page 2).X (n + p, -p) ≅
      cokernel (Subobject.ofLE (FH n (p + 1)) (FH n p) (hantiH n (by omega)))) := by
    intro p n
    obtain ⟨r, hr, hst⟩ := hstab (n + p) (-p)
    obtain ⟨_, hn, hb⟩ := hst r le_rfl
    rw [add_neg_cancel_right] at hn hb
    simp only [neg_neg] at hn hb
    have hcut : Z (r - 1) p n ⊓ F (p + 1) n ≤ D (r - 1) p n ⊓ Z (r - 1) p n := by
      refine le_inf ?_ inf_le_left
      rw [hD]
      apply le_sup_of_le_left
      rw [hZ, hZ, inf_right_comm, inf_eq_right.mpr (hanti n (by omega))]
      convert le_rfl using 1
      congr 3
      omega
    obtain ⟨esup⟩ := nonempty_cokernel_sup_iso (Z (r - 1) p n)
      (D (r - 1) p n ⊓ Z (r - 1) p n) (F (p + 1) n) inf_le_right hcut
    let N := kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
    let B := imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
    have esup' : Nonempty (cokernel (Subobject.ofLE _ _
        (inf_le_right : D (r - 1) p n ⊓ Z (r - 1) p n ≤ Z (r - 1) p n)) ≅
        cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right)) :=
      ⟨esup ≪≫ Subobject.cokernelOfLEIsoOfEq _ _ hb hn⟩
    obtain ⟨a, b, ec, _⟩ := hcomp p n
    let fH := HomologicalComplex.homologyMap (T.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : p ⟶ p + 1).op) n
    let gH := HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n
    have heq : fH ≫ gH = HomologicalComplex.homologyMap
        (T.filtration.ι.app (op (p + 1))) n := by
      rw [← HomologicalComplex.homologyMap_comp]
      congr 1
      simp
    have eim : Nonempty (cokernel (image.preComp fH gH) ≅
        cokernel (Subobject.ofLE (FH n (p + 1)) (FH n p) (hantiH n (by omega)))) := by
      refine ⟨(cokernel_image_preComp_iso fH gH).some ≪≫
        Subobject.cokernelOfLEIsoOfEq _ _ ?_ ?_⟩
      · rw [heq, hFH]
      · exact (hFH n p).symm
    obtain ⟨er⟩ := nonempty_page_iso_of_two_columns E hsupport r hr (n + p, -p)
    have er' : Nonempty ((E.page r hr).X (n + p, -p) ≅
        cokernel (Subobject.ofLE _ _
          (inf_le_right : D (r - 1) p n ⊓ Z (r - 1) p n ≤ Z (r - 1) p n))) := by
      have hh := hE r (n + p) (-p) hr
      rw [add_neg_cancel_right, neg_neg] at hh
      exact ⟨hh⟩
    exact ⟨er ≪≫ er'.some ≪≫ esup'.some ≪≫ ec ≪≫ eim.some⟩
  refine ⟨P, Q, f, g, hf, hg, hP, hQ, T, eT, E, F, Z, D, FH, hE, e₂,
    hF, hZ, hD, hFH, hpos, hfin, hbound, hstab, hcomp,
    fun r p q hr => page_d_eq_zero_of_two_columns E hsupport r hr _ _, ?_⟩
  intro n
  have hstep : ∀ p : ℤ, p ≠ -n - 1 → p ≠ -n → FH n (p + 1) = FH n p := by
    intro p hp hp'
    exact Subobject.eq_of_isZero_cokernel_ofLE (hantiH n (by omega))
      ((hsupport (n + p) (-p) (by omega) (by omega)).of_iso (egr p n).some.symm)
  obtain ⟨a, b, hab, ha, hb⟩ := hbound n
  have hlo : FH n (-n - 1) = ⊤ := by
    by_cases h : -n - 1 ≤ a
    · exact top_le_iff.mp (ha.ge.trans (hantiH n h))
    · rw [eq_of_eq_succ_on (FH n) (by omega : a ≤ -n - 1)
        (fun p hp hp' => hstep p (by omega) (by omega)), ha]
  have hhi : FH n (-n + 1) = ⊥ := by
    by_cases h : b ≤ -n + 1
    · exact le_bot_iff.mp ((hantiH n h).trans hb.le)
    · rw [← eq_of_eq_succ_on (FH n) (by omega : -n + 1 ≤ b)
        (fun p hp hp' => hstep p (by omega) (by omega)), hb]
  refine ⟨hlo, hhi, ?_⟩
  let torZeroTensor :
      (∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} =>
        ((Tor' (ModuleCat S) (-0 : ℤ).toNat).obj (K'.homology ij.1.1)).obj
          (L'.homology ij.1.2)) ≅
      ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} =>
        K'.homology ij.1.1 ⊗ L'.homology ij.1.2 :=
    Sigma.mapIso (fun ij =>
      (((tensoringRight (ModuleCat S)).obj (L'.homology ij.1.2)).leftDerivedZeroIsoSelf).app
        (K'.homology ij.1.1))
  let torOne := Iso.refl
    (∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n + 1} =>
      ((Tor' (ModuleCat S) 1).obj (K'.homology ij.1.1)).obj (L'.homology ij.1.2))
  let eTensor := e₂ 0 n (by omega) ≪≫ torZeroTensor
  let eTor := e₂ (-1) (n + 1) (by omega) ≪≫ torOne
  have e₀' : Nonempty ((E.page 2).X (0, n) ≅
      cokernel (Subobject.ofLE (FH n (-n + 1)) (FH n (-n)) (hantiH n (by omega)))) := by
    simpa using egr (-n) n
  let e₀ := e₀'.some ≪≫ (cokernel_bot_iso (hantiH n (by omega)) hhi).some
  have e₁' : Nonempty ((E.page 2).X (-1, n + 1) ≅
      cokernel (Subobject.ofLE (FH n (-n)) (FH n (-n - 1)) (hantiH n (by omega)))) := by
    have hh := egr (-n - 1) n
    have hn₃ : -n - 1 + 1 = -n := by omega
    rw [show n + (-n - 1) = -1 by omega, show -(-n - 1) = n + 1 by omega] at hh
    exact ⟨hh.some ≪≫ Subobject.cokernelOfLEIsoOfEq _ _
      (congrArg (FH n) hn₃) rfl⟩
  let e₁ := e₁'.some ≪≫ (cokernel_top_iso (hantiH n (by omega)) hlo).some
  let eH : (P ⊗ Q).homology n ≅ T.X.homology n :=
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.up ℤ) n).mapIso eT
  let ι := eTensor.inv ≫ e₀.hom ≫ (FH n (-n)).arrow ≫ eH.inv
  let π := eH.hom ≫ cokernel.π (FH n (-n)).arrow ≫ e₁.inv ≫ eTor.hom
  have hιπ : ι ≫ π = 0 := by
    dsimp only [ι, π]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, cokernel.condition_assoc, comp_zero,
      zero_comp]
  refine ⟨torZeroTensor, torOne, eTensor, eTor, e₀, e₁, ι, π, hιπ,
    rfl, rfl, rfl, rfl, ?_⟩
  have hseq : (ShortComplex.cokernelSequence (FH n (-n)).arrow).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := inferInstanceAs (Mono (FH n (-n)).arrow)
      epi_g := inferInstance }
  apply ShortComplex.shortExact_of_iso (S₁ := ShortComplex.cokernelSequence (FH n (-n)).arrow)
    (ShortComplex.isoMk (S₂ := ShortComplex.mk ι π hιπ)
      (e₀.symm ≪≫ eTensor) eH.symm (e₁.symm ≪≫ eTor) ?_ ?_) hseq
  · simp [ι, Category.assoc]
  · change eH.inv ≫ (eH.hom ≫ cokernel.π (FH n (-n)).arrow ≫ e₁.inv ≫ eTor.hom) =
      cokernel.π (FH n (-n)).arrow ≫ (e₁.inv ≫ eTor.hom)
    exact eH.inv_hom_id_assoc _

end CochainComplex.Kunneth

end
