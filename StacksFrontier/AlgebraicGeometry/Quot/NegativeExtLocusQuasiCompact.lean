module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeDualExtLocus
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualProved
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesDiagonalCorrected
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.RingTheory.Fitting.Rank
public import StacksFrontier.LinearAlgebra.Matrix.MinorIdealRank
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsUlift

/-!
# The locus of vanishing negative fibre extensions is quasi-compact over the base

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces, `K` a
pseudo-coherent and `E` a `Y`-perfect object of `D(𝒪_X)`, and let `W ⊆ Y` be the open of
Stacks 0DLC, part (1): a point `y : Spec(k) ⟶ Y` lies in `|W|` exactly when
`Ext^i(K_y, E_y) = 0` for all `i < 0`.  This file proves that the inclusion `W ⟶ Y` is
quasi-compact.  For the projection `X_T ⟶ T` of a family of `Complexes_{X/Y}` these are the
hypotheses `hqc₁`, `hqc₂` of the corrected Stacks 0DPW
(`AlgebraicGeometry.Space.ComplexesSituation.complexesIsom_corrected_of_opens`), which the source
uses implicitly ("`W(E, E')` is a quasi-compact open").

## The argument

Quasi-compactness of `W ⟶ Y` may be tested on affine schemes `Spec(A) ⟶ Y`.  There Stacks 0DKY
gives a pseudo-coherent `L` on `Spec(A)` with `Ext^i(K_y, E_y) = Ext^i(L_y, 𝒪_y)` at every field
point (`AlgebraicGeometry.Space.exists_dual_forall_hasNoNegativeExtAt_iff`), and `L` is modelled
by a bounded above complex `P` of finite free `A`-modules, so that the preimage of `W` consists of
the primes `p` with `H^j(P ⊗ κ(p)) = 0` for `j > 0`, as in the proof of Stacks 0BDI
(`AlgebraicGeometry.Space.hasNoNegativeDualExt_comp_chart_iff`).  Only the degrees `0 < j ≤ b`
matter, `P` vanishing above `b`.  Writing `n` for the rank of `P^{j+1}` and
`M_j = P^j / d(P^{j-1})`, a dimension count over `κ(p)` gives

`H^j(P ⊗ κ(p)) = 0  ⟺  dim (M_j ⊗ κ(p)) + dim (M_{j+1} ⊗ κ(p)) ≤ n
                   ⟺  ∃ a ≤ n, Fit_a(M_j) ⊄ p ∧ Fit_{n-a}(M_{j+1}) ⊄ p`,

so the locus is a finite intersection of finite unions of complements `D(I)` of zero loci of
finitely generated ideals: a quasi-compact open of `Spec(A)`.

## Main results

* `AlgebraicGeometry.Space.isCompact_setOf_forall_fibreBetti_eq_zero`: for a bounded above complex
  `P` of finite free `A`-modules, the primes at which the derived fibre Betti numbers of `P` in
  positive degrees vanish form a quasi-compact subset of `Spec(A)`.
* `AlgebraicGeometry.Space.exists_isCompact_hasNoNegativeDualExt_iff`: the locus of Stacks 0BDI of
  a pseudo-coherent complex on an affine scheme is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompact_ι_of_isNegativeExtLocus`: the inclusion of the open of
  Stacks 0DLC, part (1), is quasi-compact.
* `ComplexesSituation.isQuasiCompact_openSubspaceImmersion_negativeExtLocus` and `..._swap` (in
  `AlgebraicGeometry.Space`): the hypotheses `hqc₁` and `hqc₂` of
  `AlgebraicGeometry.Space.ComplexesSituation.complexesIsom_corrected_of_opens`.

## Implementation notes

The sections reading the fibre Betti numbers pin `HasDerivedCategory.standard` at priority
`10000`, as `StacksFrontier/AlgebraicGeometry/Quot/NegativeDualExtLocus.lean` does.  Nothing is
registered.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
* [Stacks Project, Tag 07Z6](https://stacks.math.columbia.edu/tag/07Z6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Linear algebra -/

section Algebra

/-- For `V₁ → V₂ → V₃` with vanishing composite, exactness at `V₂` is a dimension count. -/
private theorem ker_le_range_iff_finrank_quotient_add_le {k : Type*} [Field k]
    {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    [FiniteDimensional k V₂] [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₃]
    (f : V₁ →ₗ[k] V₂) (g : V₂ →ₗ[k] V₃) (hfg : ∀ x, g (f x) = 0) :
    LinearMap.ker g ≤ LinearMap.range f ↔
      Module.finrank k (V₂ ⧸ LinearMap.range f) + Module.finrank k (V₃ ⧸ LinearMap.range g) ≤
        Module.finrank k V₃ := by
  have hle : LinearMap.range f ≤ LinearMap.ker g := by
    rintro _ ⟨x, rfl⟩
    exact hfg x
  have h₁ := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  have h₂ := Submodule.finrank_quotient_add_finrank (LinearMap.range g)
  have h₃ := LinearMap.finrank_range_add_finrank_ker g
  have h₄ := Submodule.finrank_mono hle
  constructor
  · intro h
    have h₅ := Submodule.finrank_mono h
    omega
  · intro h
    exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm.le

/-- Over a field `k` reached by `g : A →+* k`, the fibre `k ⊗_A N` of a finite module has dimension
at most `a` exactly when the `a`-th Fitting ideal of `N` is not contained in the kernel of `g`. -/
private theorem finrank_extendScalars_le_iff {A k : Type u} [CommRing A] [Field k] (g : A →+* k)
    (N : ModuleCat.{u} A) [Module.Finite A N] (a : ℕ) :
    Module.finrank k ((ModuleCat.extendScalars g).obj N) ≤ a ↔
      ¬ _root_.fittingIdeal (R := A) (M := N) (a : ℤ) ≤ RingHom.ker g := by
  let := g.toAlgebra
  show Module.finrank k ((ModuleCat.extendScalars (algebraMap A k)).obj N) ≤ a ↔ _
  rw [(ModuleCat.extendScalarsAlgebraEquiv N).finrank_eq,
    ← StacksDraft.MinorRank.fittingIdeal_eq_top_iff_finrank_le,
    (fittingIdeal_basic_properties.{u, u, u, u} (R := A) (M := N)).2.2.1 k a,
    ← Ideal.map_eq_bot_iff_le_ker]
  show Ideal.map (algebraMap A k) _ = ⊤ ↔ ¬ Ideal.map (algebraMap A k) _ = ⊥
  exact ⟨fun h h' => top_ne_bot (h.symm.trans h'), fun h => (Ideal.eq_bot_or_top _).resolve_left h⟩

/-- The fibre `k ⊗_A F` of a finite free module has the rank of `F` as dimension. -/
private theorem finrank_extendScalars_eq {A k : Type u} [CommRing A] [Field k] (g : A →+* k)
    (F : ModuleCat.{u} A) [Module.Finite A F] [Module.Free A F] :
    Module.finrank k ((ModuleCat.extendScalars g).obj F) = Module.finrank A F := by
  let := g.toAlgebra
  have : Nontrivial A := g.domain_nontrivial
  show Module.finrank k ((ModuleCat.extendScalars (algebraMap A k)).obj F) = _
  rw [(ModuleCat.extendScalarsAlgebraEquiv F).finrank_eq, Module.finrank_baseChange]

/-- Extension of scalars commutes with cokernels: the dimension of the cokernel of `k ⊗_A f` is
that of `k ⊗_A coker(f)`. -/
private theorem finrank_quotient_range_extendScalars_map {A k : Type u} [CommRing A] [Field k]
    (g : A →+* k) {M₁ M₂ : ModuleCat.{u} A} (f : M₁ ⟶ M₂) :
    Module.finrank k ((ModuleCat.extendScalars g).obj M₂ ⧸
        LinearMap.range ((ModuleCat.extendScalars g).map f).hom) =
      Module.finrank k ((ModuleCat.extendScalars g).obj
        (ModuleCat.of A (M₂ ⧸ LinearMap.range f.hom))) := by
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars g : ModuleCat.{u} A ⥤ _) :=
    (ModuleCat.extendRestrictScalarsAdj g).leftAdjoint_preservesColimits
  let e : ModuleCat.of k ((ModuleCat.extendScalars g).obj M₂ ⧸
        LinearMap.range ((ModuleCat.extendScalars g).map f).hom) ≅
      (ModuleCat.extendScalars g).obj (ModuleCat.of A (M₂ ⧸ LinearMap.range f.hom)) :=
    (ModuleCat.cokernelIsoRangeQuotient ((ModuleCat.extendScalars g).map f)).symm ≪≫
      (PreservesCokernel.iso (ModuleCat.extendScalars g) f).symm ≪≫
        (ModuleCat.extendScalars g).mapIso (ModuleCat.cokernelIsoRangeQuotient f)
  exact e.toLinearEquiv.finrank_eq

/-- The cokernel `P^j / d(P^{j-1})` of a differential of a complex of finite free modules is
finitely presented. -/
private theorem finitePresentation_quotient_range {A : Type u} [CommRing A]
    {M₁ M₂ : ModuleCat.{u} A} [Module.Finite A M₁] [Module.Finite A M₂] [Module.Free A M₂]
    (f : M₁ ⟶ M₂) : Module.FinitePresentation A (M₂ ⧸ LinearMap.range f.hom) := by
  have : Module.Projective A M₂ := Module.Projective.of_free
  have := Module.finitePresentation_of_projective A M₂
  refine Module.finitePresentation_of_surjective (LinearMap.range f.hom).mkQ
    (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ, LinearMap.range_eq_map]
  exact (Module.Finite.fg_top).map _

/-- **The vanishing of `H^j(P ⊗_A k)` through Fitting ideals.**  For a bounded above complex `P`
of finite free `A`-modules and `g : A →+* k` to a field, `H^j(P ⊗_A k) = 0` exactly when, with
`n` the rank of `P^{j+1}`, for some `a ≤ n` the `a`-th Fitting ideal of `P^j / d(P^{j-1})` and the
`(n - a)`-th Fitting ideal of `P^{j+1} / d(P^j)` are not contained in the kernel of `g`. -/
private theorem isZero_homology_extendScalars_iff {A k : Type u} [CommRing A] [Field k]
    (g : A →+* k) {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    [∀ i, Module.Finite A (P.X i)] (j : ℤ) :
    IsZero (((CochainComplex.extendScalars g).obj P).homology j) ↔
      ∃ a ≤ Module.finrank A (P.X (j + 1)),
        ¬ _root_.fittingIdeal (R := A) (M := P.X j ⧸ LinearMap.range (P.d (j - 1) j).hom)
            (a : ℤ) ≤ RingHom.ker g ∧
        ¬ _root_.fittingIdeal (R := A) (M := P.X (j + 1) ⧸ LinearMap.range (P.d j (j + 1)).hom)
            ((Module.finrank A (P.X (j + 1)) - a : ℕ) : ℤ) ≤ RingHom.ker g := by
  let K := (CochainComplex.extendScalars g).obj P
  have : Module.Free A (P.X (j + 1)) := (hP.finiteFree (j + 1)).2
  have : Module.Finite k (K.X j) := module_finite_extendScalars g (P.X j)
  have : Module.Finite k (K.X (j + 1)) := module_finite_extendScalars g (P.X (j + 1))
  have hex : IsZero (K.homology j) ↔
      LinearMap.ker (K.d j (j + 1)).hom ≤ LinearMap.range (K.d (j - 1) j).hom := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' K (j - 1) j (j + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_ker_sub_range]
    rfl
  have hdd : ∀ x, (K.d j (j + 1)).hom ((K.d (j - 1) j).hom x) = 0 := fun x => by
    exact congrArg (fun φ => φ.hom x) (K.d_comp_d (j - 1) j (j + 1))
  show IsZero (K.homology j) ↔ _
  rw [hex, ker_le_range_iff_finrank_quotient_add_le _ _ hdd]
  have e₁ := finrank_quotient_range_extendScalars_map g (P.d (j - 1) j)
  have e₂ := finrank_quotient_range_extendScalars_map g (P.d j (j + 1))
  have e₃ := finrank_extendScalars_eq g (P.X (j + 1))
  show Module.finrank k ((ModuleCat.extendScalars g).obj (P.X j) ⧸
        LinearMap.range ((ModuleCat.extendScalars g).map (P.d (j - 1) j)).hom) +
      Module.finrank k ((ModuleCat.extendScalars g).obj (P.X (j + 1)) ⧸
        LinearMap.range ((ModuleCat.extendScalars g).map (P.d j (j + 1))).hom) ≤
      Module.finrank k ((ModuleCat.extendScalars g).obj (P.X (j + 1))) ↔ _
  rw [e₁, e₂, e₃]
  have f₁ := fun a => finrank_extendScalars_le_iff g
    (ModuleCat.of A (P.X j ⧸ LinearMap.range (P.d (j - 1) j).hom)) a
  have f₂ := fun a => finrank_extendScalars_le_iff g
    (ModuleCat.of A (P.X (j + 1) ⧸ LinearMap.range (P.d j (j + 1)).hom)) a
  constructor
  · intro h
    exact ⟨_, Nat.le_of_add_right_le h, (f₁ _).1 le_rfl, (f₂ (Module.finrank A (P.X (j + 1)) -
      Module.finrank k ((ModuleCat.extendScalars g).obj
        (ModuleCat.of A (P.X j ⧸ LinearMap.range (P.d (j - 1) j).hom))))).1 (by omega)⟩
  · rintro ⟨a, ha, h₁, h₂⟩
    have := (f₁ a).2 h₁
    have := (f₂ _).2 h₂
    omega

end Algebra

/-! ### The locus on an affine chart is quasi-compact -/

section Compact

attribute [local instance 10000] HasDerivedCategory.standard

/-- A finite intersection of compact open subsets of a compact quasi-separated space is compact
and open. -/
private theorem isCompact_isOpen_biInter_finset {X ι : Type*} [TopologicalSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X] (s : Finset ι) (U : ι → Set X)
    (h : ∀ i ∈ s, IsCompact (U i) ∧ IsOpen (U i)) :
    IsCompact (⋂ i ∈ s, U i) ∧ IsOpen (⋂ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isCompact_univ : IsCompact (Set.univ : Set X))
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    have ha' := h a (Finset.mem_insert_self a s)
    have ih' := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨QuasiSeparatedSpace.inter_isCompact _ _ ha'.2 ha'.1 ih'.2 ih'.1, ha'.2.inter ih'.2⟩

/-- **The primes at which `H^j(P ⊗ κ(p))` vanishes form a quasi-compact open**, for a bounded above
complex `P` of finite free modules: a finite union of the complements `D(I)` of the zero loci of
the finitely generated ideals `I = Fit_a(P^j / d P^{j-1}) · Fit_{n-a}(P^{j+1} / d P^j)`. -/
private theorem isCompact_isOpen_setOf_isZero_homology {A : Type u} [CommRing A]
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P) (j : ℤ) :
    IsCompact {p : PrimeSpectrum A | IsZero (((CochainComplex.extendScalars
        (algebraMap A p.asIdeal.ResidueField)).obj P).homology j)} ∧
      IsOpen {p : PrimeSpectrum A | IsZero (((CochainComplex.extendScalars
        (algebraMap A p.asIdeal.ResidueField)).obj P).homology j)} := by
  have : ∀ i, Module.Finite A (P.X i) := fun i => (hP.finiteFree i).1
  have : Module.Free A (P.X j) := (hP.finiteFree j).2
  have : Module.Free A (P.X (j + 1)) := (hP.finiteFree (j + 1)).2
  let n := Module.finrank A (P.X (j + 1))
  let I : ℕ → Ideal A := fun a =>
    _root_.fittingIdeal (R := A) (M := P.X j ⧸ LinearMap.range (P.d (j - 1) j).hom) (a : ℤ) *
      _root_.fittingIdeal (R := A) (M := P.X (j + 1) ⧸ LinearMap.range (P.d j (j + 1)).hom)
        ((n - a : ℕ) : ℤ)
  have hI : ∀ a, (I a).FG := fun a =>
    Submodule.FG.mul
      ((fittingIdeal_basic_properties.{u, u, u, u} (R := A)
        (M := P.X j ⧸ LinearMap.range (P.d (j - 1) j).hom)).2.2.2.1
        (finitePresentation_quotient_range _) a)
      ((fittingIdeal_basic_properties.{u, u, u, u} (R := A)
        (M := P.X (j + 1) ⧸ LinearMap.range (P.d j (j + 1)).hom)).2.2.2.1
        (finitePresentation_quotient_range _) (n - a))
  have heq : {p : PrimeSpectrum A | IsZero (((CochainComplex.extendScalars
        (algebraMap A p.asIdeal.ResidueField)).obj P).homology j)} =
      ⋃ a ∈ Finset.range (n + 1), (PrimeSpectrum.zeroLocus (I a : Set A))ᶜ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
      SetLike.coe_subset_coe, Finset.mem_range, exists_prop]
    rw [isZero_homology_extendScalars_iff _ hP j, Ideal.ker_algebraMap_residueField]
    refine exists_congr fun a => ?_
    rw [Nat.lt_succ_iff, Ideal.IsPrime.mul_le (hp := p.isPrime)]
    tauto
  have hco : ∀ a ∈ Finset.range (n + 1),
      IsCompact (PrimeSpectrum.zeroLocus (I a : Set A))ᶜ ∧
        IsOpen (PrimeSpectrum.zeroLocus (I a : Set A))ᶜ := fun a _ =>
    PrimeSpectrum.isCompact_isOpen_iff_ideal.2 ⟨I a, hI a, rfl⟩
  rw [heq]
  exact ⟨(Finset.range (n + 1)).isCompact_biUnion fun a ha => (hco a ha).1,
    isOpen_biUnion fun a ha => (hco a ha).2⟩

/-- **The locus of Stacks 0BDI on an affine chart is quasi-compact.**  For a bounded above complex
`P` of finite free `A`-modules, the set of primes `p` of `A` at which the derived fibre Betti
numbers `dim_{κ(p)} H^j(P ⊗^L κ(p))`, `j > 0`, all vanish is quasi-compact: if `P` vanishes above
`b`, it is the intersection over `0 < j ≤ b` of the quasi-compact opens where `H^j(P ⊗ κ(p))`
vanishes, and the spectrum of a ring is quasi-separated. -/
theorem isCompact_setOf_forall_fibreBetti_eq_zero {A : Type u} [CommRing A]
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P) :
    IsCompact {p : PrimeSpectrum A | ∀ j : ℤ, 0 < j →
      StacksDraft.Perfect.fibreBetti.{u, u} (DerivedCategory.Q.obj P) j p = 0} := by
  obtain ⟨b, hb⟩ := hP.upperBound
  have hvan : ∀ (p : PrimeSpectrum A) (j : ℤ), b < j → IsZero (((CochainComplex.extendScalars
      (algebraMap A p.asIdeal.ResidueField)).obj P).homology j) := by
    intro p j hj
    let K := (CochainComplex.extendScalars (algebraMap A p.asIdeal.ResidueField)).obj P
    have : (DerivedCategory.Q.obj K).IsLE b := by
      have : K.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
        (ModuleCat.extendScalars _).map_isZero (P.isZero_of_isStrictlyLE b i hi)
      infer_instance
    exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj K) b j hj).of_iso
      (StacksDraft.PseudoCoherence.homologyQObjIso K j).symm
  have heq : {p : PrimeSpectrum A | ∀ j : ℤ, 0 < j →
      StacksDraft.Perfect.fibreBetti.{u, u} (DerivedCategory.Q.obj P) j p = 0} =
      ⋂ j ∈ Finset.Ioc 0 b, {p : PrimeSpectrum A | IsZero (((CochainComplex.extendScalars
        (algebraMap A p.asIdeal.ResidueField)).obj P).homology j)} := by
    ext p
    have hβ := fun j => fibreBetti_eq_zero_iff_isZero_homology
      (algebraMap A p.asIdeal.ResidueField) hP p (Ideal.ker_algebraMap_residueField p.asIdeal) j
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_Ioc, hβ]
    exact ⟨fun h j hj => h j hj.1, fun h j hj =>
      if hjb : j ≤ b then h j ⟨hj, hjb⟩ else hvan p j (by omega)⟩
  rw [heq]
  exact (isCompact_isOpen_biInter_finset _ _ fun j _ =>
    isCompact_isOpen_setOf_isZero_homology hP j).1

end Compact

/-! ### The locus on an affine chart, read at the points -/

section Chart

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The locus of Stacks 0BDI on an affine scheme is quasi-compact.**  For a pseudo-coherent `L`
on `Spec(A)`, there is a quasi-compact set of points of `Spec(A)` through which a test scheme `T`
over `Spec(A)` with values in a field passes exactly when `Ext^i(L_T, 𝒪_T) = 0` for all `i < 0`.

On the identity chart `L` is modelled by a bounded above complex `P` of finite free `A`-modules,
the condition at `T` is the vanishing of the derived fibre Betti numbers of `P` in positive
degrees at the prime `T` passes through
(`AlgebraicGeometry.Space.hasNoNegativeDualExt_comp_chart_iff`), and the set of those primes is
quasi-compact (`AlgebraicGeometry.Space.isCompact_setOf_forall_fibreBetti_eq_zero`). -/
theorem exists_isCompact_hasNoNegativeDualExt_iff {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (CommRingCat.of A))) (gA : B.obj hA ⟶ B.obj hS)
    (L : derivedModules B S hS (schemeSpace (specFppfOver B S hS hA gA)))
    (hL : (smallEtaleRingedSite B S hS _
      (schemeSpace (specFppfOver B S hS hA gA)).2).IsPseudoCoherent L) :
    ∃ Oc : Set (points B S hS (yoneda.obj (specFppfOver B S hS hA gA))),
      @IsCompact _ (pointTopology B S hS _) Oc ∧
        ∀ T : SchemesOver (schemeSpace (specFppfOver B S hS hA gA)),
          Stack.IsFieldObject B S hS T.left →
          (schemesOverPoints T ⊆ Oc ↔ HasNoNegativeDualExt L T.hom) := by
  let := pointTopology B S hS (yoneda.obj (specFppfOver B S hS hA gA))
  let φ := 𝟙 (schemeSpace (specFppfOver B S hS hA gA))
  have hφ : IsEtale B S hS φ.hom := isEtale_id B S hS _
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    exists_isBoundedAboveFiniteFree_etaleModulePullback_iso B S hS hA gA φ hφ L hL
  obtain ⟨e₁⟩ := nonempty_etaleModulePullback_mapDerivedCategory_iso φ hφ L
  let O : Set ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)) :=
    {p | ∀ j : ℤ, 0 < j →
      StacksDraft.Perfect.fibreBetti.{u, u} (DerivedCategory.Q.obj P) j p = 0}
  have hO : IsCompact O := isCompact_setOf_forall_fibreBetti_eq_zero hP
  refine ⟨schemePointsHomeomorph B S hS _ ⁻¹' O,
    (schemePointsHomeomorph B S hS _).isCompact_preimage.2 hO, fun T hT => ?_⟩
  obtain ⟨w⟩ := nonempty_points_yoneda_of_isFieldObject hT
  have h := hasNoNegativeDualExt_comp_chart_iff L hA gA φ P hP (e₁.symm ≪≫ eP) T hT w
  rw [Category.comp_id] at h
  exact (schemesOverPoints_subset_iff hT ⟨w, rfl⟩ _).trans h.symm

end Chart

/-! ### The locus is quasi-compact over the base -/

section Locus

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory
  AlgebraicGeometry.Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The locus of Stacks 0DLC, part (1), pulled back to an affine scheme, is quasi-compact.**  For
`φ : Spec(A) ⟶ Y` and an open `W ⊆ Y` characterized as in part (1), the points of `Spec(A)`
mapping into `|W|` form a quasi-compact set: Stacks 0DKY over `Spec(A)` gives a pseudo-coherent
`L` on `Spec(A)` with `Ext^i(K_y, E_y) = Ext^i(L_y, 𝒪_y)` at every field point `y`, and the locus
of `L` is quasi-compact (`AlgebraicGeometry.Space.exists_isCompact_hasNoNegativeDualExt_iff`). -/
private theorem isCompact_preimage_range_of_isNegativeExtLocus (f : X ⟶ Y)
    (hp : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) (W : OpenSubspaces B S hS Y.1)
    (hW : IsNegativeExtLocus f K E W) {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (CommRingCat.of A))) (gA : B.obj hA ⟶ B.obj hS)
    (φ : schemeSpace (specFppfOver B S hS hA gA) ⟶ Y) :
    @IsCompact _ (pointTopology B S hS _) (pointsMap B S hS _ φ.hom ⁻¹'
      Set.range (pointsMap B S hS W.1.toFunctor W.1.ι)) := by
  let U : AlgebraicSpaces B S hS := schemeSpace (specFppfOver B S hS hA gA)
  have hU : IsAffine ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hqc : IsQuasiCompactSpace B S hS U.1 :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS (specFppfOver B S hS hA gA) hU
  have hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal U.1 :=
    isAbsolutelyQuasiSeparated_yoneda_obj B S hS B.contains_terminal
      (specFppfOver B S hS hA gA) inferInstance
  have hrep : yoneda.relativelyRepresentable φ.hom := Y.2.diagonal_representable.of_diag φ.hom
  obtain ⟨L, hL, hLK⟩ := exists_dual_forall_hasNoNegativeExtAt_iff
    (relativeDerivedHomDualExists_proved B S hS) f hp hflat hfp K E hK hE (U := U) hqc hqs φ hrep
  obtain ⟨Oc, hOc, hOcL⟩ := exists_isCompact_hasNoNegativeDualExt_iff hA gA L hL
  suffices heq : pointsMap B S hS _ φ.hom ⁻¹'
      Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) = Oc by
    rw [heq]
    exact hOc
  ext z
  obtain ⟨T, hT, hz⟩ := exists_isFieldObject_mem_schemesOverPoints (Y := U) z
  have hx : pointsMap B S hS _ φ.hom z ∈ schemesOverPoints
      ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) φ).obj T) := by
    rw [schemesOverPoints_map]
    exact ⟨z, hz, rfl⟩
  rw [← schemesOverPoints_subset_iff hT hz Oc, hOcL T hT, ← hLK T, ← hW _ hT,
    testPoint_mem_iff_schemesOverPoints_subset]
  exact (schemesOverPoints_subset_iff (T := (CostructuredArrow.map
    (S := schemeSpaceFunctor B S hS) φ).obj T) hT hx _).symm

/-- **The open of Stacks 0DLC, part (1), is quasi-compact over the base.**  Let `f : X ⟶ Y` be
proper, flat and of finite presentation, `K` pseudo-coherent and `E` `Y`-perfect, and let `W ⊆ Y`
be an open subspace characterized by `y ∈ |W| ⟺ Ext^i(K_y, E_y) = 0` for `i < 0` at the points
`y` with values in a field.  Then the inclusion `W ⟶ Y` is quasi-compact.

It suffices that the preimage of `W` in every affine scheme `Z ⟶ Y` is quasi-compact
(`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine'`).  That preimage
is an open subspace of `Z`, whose points are those of `Z` mapping into `|W|`: on
`Spec(A) ≅ Z` they form a quasi-compact set, cut out by finitely many finitely generated
Fitting ideals of the cokernels of a finite free model of the `L` of Stacks 0DKY. -/
theorem isQuasiCompact_ι_of_isNegativeExtLocus (f : X ⟶ Y)
    (hp : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) (W : OpenSubspaces B S hS Y.1)
    (hW : IsNegativeExtLocus f K E W) :
    IsQuasiCompact B S hS W.1.ι := by
  refine isQuasiCompact_of_isQuasiCompactSpace_pullback_affine' B S hS W.1.ι W.2.1 Y.2
    fun Z g hZ => ?_
  let := pointTopology B S hS (yoneda.obj Z)
  have hpre : IsQuasiCompactSpace B S hS (W.1.preimage g).toFunctor := by
    refine isQuasiCompactSpace_of_isCompact_range B S hS (isAlgebraicSpace_yoneda B S hS Z)
      (isOpenSubspace_preimage B S hS g W.1 Y.2 (isAlgebraicSpace_yoneda B S hS Z) W.2) ?_
    rw [range_pointsMap_preimage_ι]
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj Z) := hZ
    let e := ((BigFppfOver.toScheme B S hS).obj Z).isoSpec
    have hA : B.Contains (Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤))) :=
      lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact e.inv) Z.left.2
    let gA : B.obj hA ⟶ B.obj hS := ObjectProperty.homMk e.inv ≫ Z.hom
    let eV : specFppfOver B S hS hA gA ≅ Z :=
      Over.isoMk (B.inclusion.preimageIso e.symm) (B.inclusion.map_injective (by
        rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
        rfl))
    let φ : schemeSpace (specFppfOver B S hS hA gA) ⟶ Y :=
      ObjectProperty.homMk (yoneda.map eV.hom ≫ g)
    have hc := isCompact_preimage_range_of_isNegativeExtLocus f hp hflat hfp K E hK hE W hW
      hA gA φ
    let h := pointsHomeomorphOfIso B S hS (yoneda.mapIso eV)
    have hφ : pointsMap B S hS _ φ.hom ⁻¹' Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) =
        h ⁻¹' (pointsMap B S hS _ g ⁻¹' Set.range (pointsMap B S hS W.1.toFunctor W.1.ι)) := by
      show pointsMap B S hS _ (yoneda.map eV.hom ≫ g) ⁻¹' _ = _
      rw [pointsMap_comp, Set.preimage_comp]
      rfl
    rw [hφ] at hc
    rw [← h.image_preimage (pointsMap B S hS _ g ⁻¹' _)]
    exact hc.image h.continuous
  exact IsQuasiCompactSpace.of_iso B S hS hpre (Subfunctor.isPullback_preimage g W.1).isoPullback

/-- The inclusion of an open of Stacks 0DLC, part (1), as a morphism of algebraic spaces, is
quasi-compact. -/
theorem isQuasiCompact_openSubspaceImmersion_of_isNegativeExtLocus (f : X ⟶ Y)
    (hp : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) (W : OpenSubspaces B S hS Y.1)
    (hW : IsNegativeExtLocus f K E W) :
    IsQuasiCompact B S hS (openSubspaceImmersion B S hS W).hom :=
  isQuasiCompact_ι_of_isNegativeExtLocus f hp hflat hfp K E hK hE W hW

/-! ### The inputs `hqc₁`, `hqc₂` of the corrected Stacks 0DPW -/

namespace ComplexesSituation

variable {D : ComplexesSituation B S hS} (A : ComplexesObject D)
  (E' : derivedModules B S hS (D.space A.T))

/-- The open of Stacks 0DLC, part (1), for the projection of a family of `Complexes_{X/Y}` over
`A.T` is quasi-compact for any pseudo-coherent `K` and relatively perfect `E`. -/
private theorem isQuasiCompact_openSubspaceImmersion_projection
    (K E : derivedModules B S hS (D.space A.T))
    (hK : (smallEtaleRingedSite B S hS (D.space A.T).1 (D.space A.T).2).IsPseudoCoherent K)
    (hE : ∀ (hflat : IsFlat B S hS (D.projection A.T).hom)
      (hfp : IsFinitePresentation B S hS (D.projection A.T).hom),
      IsPerfectRelativeToCanonical B S hS (D.projection A.T) hflat hfp.1 E)
    (W : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1)
    (hW : IsNegativeExtLocus (D.projection A.T) K E W) :
    IsQuasiCompact B S hS (openSubspaceImmersion B S hS W).hom := by
  have hfp := (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f A.T.hom) D.finitePresentation
  exact isQuasiCompact_openSubspaceImmersion_of_isNegativeExtLocus (D.projection A.T)
    ((isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f A.T.hom) D.proper)
    (D.projection_isFlat A.T) hfp K E hK (hE _ hfp) W hW

/-- **The open `W(E, E')` of Stacks 0DLC is quasi-compact over `T`**: for objects `(T, E)` and
`(T, E')` of `Complexes_{X/Y}` over the same test scheme, the inclusion into `T` of an open
subspace characterized by `y ∈ |W| ⟺ Ext^i(E_y, E'_y) = 0` for `i < 0` is quasi-compact.  This is
the hypothesis `hqc₁` of
`AlgebraicGeometry.Space.ComplexesSituation.complexesIsom_corrected_of_opens` at
`ι₁ = openSubspaceImmersion B S hS W`. -/
theorem isQuasiCompact_openSubspaceImmersion_negativeExtLocus
    (h₁ : D.IsRelativelyPerfect A.T E')
    (W : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1)
    (hW : IsNegativeExtLocus (D.projection A.T) A.E E' W) :
    IsQuasiCompact B S hS (openSubspaceImmersion B S hS W).hom :=
  isQuasiCompact_openSubspaceImmersion_projection A A.E E' A.relativelyPerfect.1
    (fun _ _ => h₁) W hW

/-- **The open `W(E', E)` of Stacks 0DLC is quasi-compact over `T`**: the hypothesis `hqc₂` of
`AlgebraicGeometry.Space.ComplexesSituation.complexesIsom_corrected_of_opens` at
`ι₂ = openSubspaceImmersion B S hS W`. -/
theorem isQuasiCompact_openSubspaceImmersion_negativeExtLocus_swap
    (h₁ : D.IsRelativelyPerfect A.T E')
    (W : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1)
    (hW : IsNegativeExtLocus (D.projection A.T) E' A.E W) :
    IsQuasiCompact B S hS (openSubspaceImmersion B S hS W).hom :=
  isQuasiCompact_openSubspaceImmersion_projection A E' A.E h₁.1
    (fun _ _ => A.relativelyPerfect) W hW

end ComplexesSituation

end Locus

end AlgebraicGeometry.Space

end
