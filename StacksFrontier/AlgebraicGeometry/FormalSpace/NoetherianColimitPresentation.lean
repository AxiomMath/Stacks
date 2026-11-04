module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical

/-!
# A Noetherian affine formal algebraic space as a colimit of finite-order thickenings

Let `A` be a Noetherian topological ring whose topology is adic and let `a ⊆ A` be its ideal of
topologically nilpotent elements. The formal spectrum `Spf A` is the colimit of the sequence
`Spec (A ⧸ a) → Spec (A ⧸ a ^ 2) → Spec (A ⧸ a ^ 3) → ⋯`: the powers of `a` are cofinal among
the weak ideals of definition of `A`, the quotient `A ⧸ a` is reduced, every `A ⧸ a ^ n` is
Noetherian, and `Spec (A ⧸ a ^ n)` is the `n`th infinitesimal neighbourhood of `Spec (A ⧸ a)`
inside `Spec (A ⧸ a ^ m)` for every `m ≥ n`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.powChain`: the sequence of powers of an adic ideal of
  definition, as a diagram in the weak ideals of definition ordered by reverse inclusion.

## Main results

* `AlgebraicGeometry.FormalSpace.final_powChain`: that sequence is cofinal, so it computes the
  same colimit as the full diagram of weak ideals of definition.
* `AlgebraicGeometry.FormalSpace.exists_finiteOrderThickening_presentation_formalSpectrum`:
  **Stacks 0GHM** for a Noetherian affine formal algebraic space.

## Implementation notes

The source states 0GHM for a locally Noetherian formal algebraic space, and its proof reduces
to the Noetherian affine case by working étale locally; it is that case which is proved here.
The étale-local step is not carried out here, so the tag is carried in the phrase form naming
the restricted input class. The reduction `X_red` that step uses is itself available, by
Stacks 0AIN —
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`.

The stages are indexed from zero, so the stage `n` of the sequence is the source's `X_{n+1}`
and the stage `0` is the reduction. That the stage `0` is reduced is the statement that `a` is
a radical ideal, `TopologicalRing.topologicalNilradical_isRadical`.

The infinitesimal-neighbourhood clause is stated as the equality of ideal sheaves
`(X_0 ⟶ X_m).ker ^ (n + 1) = (X_n ⟶ X_m).ker`, which with
`Stacks.Thickenings.nthOrderι_ker` identifies the stage `n` with the `n`th-order infinitesimal
neighbourhood of the stage `0` inside the stage `m`. Over an affine scheme it is the
ring-theoretic identity `(a ⧸ a ^ (m+1)) ^ (n+1) = a ^ (n+1) ⧸ a ^ (m+1)`, which is
`Ideal.map_pow`.

Cofinality is `CategoryTheory.Functor.final_of_exists_of_isFiltered`, whose second hypothesis
is vacuous here because the morphisms of a preorder category form a subsingleton.

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A]

/-! ### Quotient stages of an affine scheme -/

/-- The pullback of an ideal along a ring homomorphism with a two-sided inverse is the image of
that ideal along the inverse, hence commutes with powers. -/
private theorem comap_pow_of_ringHom_inverse {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂]
    {f : R₁ →+* R₂} {g : R₂ →+* R₁} (hfg : ∀ x, g (f x) = x) (hgf : ∀ y, f (g y) = y)
    (K : Ideal R₂) (n : ℕ) : K.comap f ^ n = (K ^ n).comap f := by
  have key : ∀ L : Ideal R₂, L.comap f = L.map g := fun L ↦ by
    refine le_antisymm (fun x hx ↦ (hfg x) ▸ Ideal.mem_map_of_mem g hx) ?_
    rw [Ideal.map_le_iff_le_comap]
    exact fun y hy ↦ by simpa [Ideal.mem_comap, hgf y] using hy
  rw [key, key, Ideal.map_pow]

/-- The pullback of an ideal along an isomorphism of commutative rings commutes with powers. -/
private theorem comap_pow_commRingCatIso {R₁ R₂ : CommRingCat.{u}} (e : R₁ ≅ R₂)
    (K : Ideal R₂) (n : ℕ) : K.comap e.hom.hom ^ n = (K ^ n).comap e.hom.hom := by
  refine comap_pow_of_ringHom_inverse (g := e.inv.hom) (fun x ↦ ?_) (fun y ↦ ?_) K n
  · exact congrArg (fun φ : R₁ ⟶ R₁ ↦ φ.hom x) e.hom_inv_id
  · exact congrArg (fun φ : R₂ ⟶ R₂ ↦ φ.hom y) e.inv_hom_id

/-- For `K ≤ J` the kernel of `A ⧸ K →+* A ⧸ J` is the image of `J`, so its `n`th power is the
kernel of `A ⧸ K →+* A ⧸ J ^ n`. -/
private theorem ker_factor_pow {R : Type*} [CommRing R] {K J : Ideal R}
    (hJ : K ≤ J) {n : ℕ} (hJn : K ≤ J ^ n) :
    RingHom.ker (Ideal.Quotient.factor hJ) ^ n = RingHom.ker (Ideal.Quotient.factor hJn) := by
  rw [Ideal.Quotient.factor_ker, Ideal.Quotient.factor_ker, ← Ideal.map_pow]

/-- The ideal sheaf cutting `Spec (R ⧸ J')` out of `Spec (R ⧸ K)` is the `n`th power of the one
cutting out `Spec (R ⧸ J)` when `J'` is the `n`th power of `J`. -/
private theorem ker_specMap_factor_pow {R : Type u} [CommRing R] {K J J' : Ideal R}
    (hJ : K ≤ J) {n : ℕ} (hJ' : J' = J ^ n) (hJn : K ≤ J') :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ))).ker ^ n =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJn))).ker := by
  subst hJ'
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply]
  show RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ))).appTop.hom ^ n =
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJn))).appTop.hom
  rw [Stacks.Smooth.ker_specMap_appTop, Stacks.Smooth.ker_specMap_appTop]
  simp only [CommRingCat.hom_ofHom]
  rw [← ker_factor_pow hJ hJn]
  exact comap_pow_commRingCatIso (Scheme.ΓSpecIso _) _ n

/-- If the `n`th power of `J` lies in `K ≤ J`, the closed immersion `Spec (R ⧸ J) ⟶ Spec (R ⧸ K)`
has `n`th power of its ideal sheaf equal to zero. -/
private theorem ker_specMap_factor_pow_eq_bot {R : Type u} [CommRing R] {K J : Ideal R}
    (hJ : K ≤ J) {n : ℕ} (hn : J ^ n ≤ K) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ))).ker ^ n = ⊥ := by
  refine (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine _ n).mpr
    (Stacks.Smooth.ker_specMap_appTop_pow_eq_bot _ ?_)
  simp only [CommRingCat.hom_ofHom]
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
  exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by simpa using hn)

/-! ### The cofinal chain of powers -/

section PowChain

variable {J : Ideal A} (hdef : TopologicalRing.IsIdealOfDefinition J)

variable [IsTopologicalRing A] (hadic : _root_.IsAdic J)

/-- The sequence `n ↦ J ^ (n + 1)` of weak ideals of definition attached to an adic ideal of
definition `J`, as a diagram in the weak ideals of definition ordered by reverse inclusion. -/
def powChain : ℕ ⥤ WeakIdeals A where
  obj n := OrderDual.toDual (TopologicalRing.CompletionOver.powIndex hdef hadic n)
  map {_n _m} f := homOfLE (OrderDual.toDual_le_toDual.mpr
    (Subtype.coe_le_coe.mp
      (TopologicalRing.CompletionOver.powIndex_le hdef hadic (leOfHom f))))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The `n`th term of `powChain` is the ideal `J ^ (n + 1)`. -/
@[simp]
theorem powChain_obj_coe (n : ℕ) : ((powChain hdef hadic).obj n).1 = J ^ (n + 1) := rfl

/-- The powers of an adic ideal of definition are cofinal among the weak ideals of definition,
so the sequence of their quotient stages is a final subdiagram of the diagram of all quotient
stages. -/
theorem final_powChain : (powChain hdef hadic).Final := by
  refine Functor.final_of_exists_of_isFiltered _ (fun K ↦ ?_)
    (fun _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  obtain ⟨n, hn, hle⟩ :=
    TopologicalRing.CompletionOver.exists_pow_le_of_isWeakIdealOfDefinition hdef
      (OrderDual.ofDual K).2
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact ⟨m, ⟨homOfLE (by exact hle)⟩⟩

end PowChain

/-! ### Stacks 0GHM in the Noetherian affine case -/

/-- **Stacks 0GHM**, for a Noetherian affine formal algebraic space. Let `A` be a Noetherian
topological ring whose topology is adic. Then the formal spectrum of `A` is the colimit of a
sequence `X_0 → X_1 → X_2 → ⋯` of affine schemes over `S` whose transition morphisms are
finite-order thickenings, whose terms are all locally Noetherian, whose first term `X_0` is
reduced, and in which `X_n` is the `n`th infinitesimal neighbourhood of `X_0` inside `X_m` for
every `m ≥ n` — the last clause in the form of the equality
`(X_0 ⟶ X_m).ker ^ (n + 1) = (X_n ⟶ X_m).ker` of ideal sheaves on `X_m`. -/
@[stacks 0GHM "Noetherian affine formal algebraic space"]
theorem exists_finiteOrderThickening_presentation_formalSpectrum
    [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    {I : Ideal A} (hI : _root_.IsAdic I) (D : QuotientSystem B S hS A) :
    ∃ E : ℕ ⥤ BigAffineFppf B S hS,
      IsReduced ((BigAffineFppf.toScheme B S hS).obj (E.obj 0)) ∧
      (∀ n, IsLocallyNoetherian ((BigAffineFppf.toScheme B S hS).obj (E.obj n))) ∧
      (∀ ⦃n m : ℕ⦄ (f : n ⟶ m), Stacks.Thickenings.IsFiniteOrderThickening
        ((BigAffineFppf.toScheme B S hS).map (E.map f))) ∧
      (∀ (n m : ℕ) (hnm : n ≤ m),
        ((BigAffineFppf.toScheme B S hS).map (E.map (homOfLE (Nat.zero_le m)))).ker ^ (n + 1) =
          ((BigAffineFppf.toScheme B S hS).map (E.map (homOfLE hnm))).ker) ∧
      Nonempty (formalSpectrum D ≅ colimit (E ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) := by
  set a : Ideal A := topologicalNilradical A with ha
  have hadic : _root_.IsAdic a := TopologicalRing.isAdic_topologicalNilradical hI
  have hdef : TopologicalRing.IsIdealOfDefinition a :=
    TopologicalRing.isIdealOfDefinition_of_isAdic hadic
  have hpow : ∀ {n m : ℕ}, n ≤ m → a ^ (m + 1) ≤ a ^ (n + 1) := fun h ↦
    Ideal.pow_le_pow_right (Nat.succ_le_succ h)
  refine ⟨powChain hdef hadic ⋙ D.diagram, ?_, ?_, ?_, ?_, ?_⟩
  · show IsReduced (Spec (.of (A ⧸ a ^ (0 + 1))))
    have : _root_.IsReduced (A ⧸ a ^ (0 + 1)) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp
        (by simpa using TopologicalRing.topologicalNilradical_isRadical (B := A))
    infer_instance
  · intro n
    show IsLocallyNoetherian (Spec (.of (A ⧸ a ^ (n + 1))))
    infer_instance
  · intro n m f
    have hle := hpow (leOfHom f)
    show Stacks.Thickenings.IsFiniteOrderThickening
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle)))
    refine ⟨IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective hle), m, ?_⟩
    refine ker_specMap_factor_pow_eq_bot hle ?_
    calc (a ^ (n + 1)) ^ (m + 1) = a ^ ((n + 1) * (m + 1)) := (pow_mul a (n + 1) (m + 1)).symm
      _ ≤ a ^ (m + 1) := Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left _ n.succ_pos)
  · intro n m hnm
    have hle0 := hpow (Nat.zero_le m)
    have hlen := hpow hnm
    show (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle0))).ker ^ (n + 1) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hlen))).ker
    exact ker_specMap_factor_pow hle0 (by rw [zero_add, pow_one]) hlen
  · have := final_powChain hdef hadic
    exact ⟨(Functor.Final.colimitIso (powChain hdef hadic) (formalSpectrumDiagram D)).symm⟩

end AlgebraicGeometry.FormalSpace

end
