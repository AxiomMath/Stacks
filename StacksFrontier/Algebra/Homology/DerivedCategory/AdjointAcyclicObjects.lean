module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Coproduct
public import StacksFrontier.Homology.CyclesShortComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The `Ext`-acyclic objects of an adjunction

Let `F ⊣ G` be an adjunction of additive functors between abelian categories, with `F` right
exact — which it is automatically, being a left adjoint — and let the target have enough
injectives. Call an object `X` of the source **`Ext`-acyclic for the adjunction** when

`Ext^n(X, G I) = 0` for every injective `I` and every `n ≥ 1`.

This file proves that those objects form a class adapted to `F` in the sense of the criterion of
Stacks 05T8, read in the variance of a *left* derived functor: for a short exact sequence whose
last two terms are `Ext`-acyclic the first one is too, **and the sequence stays short exact
after applying `F`**. The second half is the point. `F` is only right exact, so there is no
formal reason for `F` to preserve the injectivity of `S.f`; what makes it do so is the
vanishing of `Ext^1(S.X₃, G I)`, which turns every map `F S.X₁ ⟶ I` into one that factors
through `F S.f`, and a map out of which everything into an injective factors is a
monomorphism.

Consequently `F` carries every bounded above acyclic complex with `Ext`-acyclic terms to an
acyclic complex, which is the hypothesis that the criterion of Stacks 0794 leaves open — so
this file reduces that hypothesis to the *object-level* vanishing of `Ext^{≥1}(X, G I)`. In the
intended application `F` is the lower-shriek functor on abelian sheaves for a continuous and
cocontinuous functor of sites, `G` is restriction, and the vanishing at the generators
`j_{U!}ℤ_U` is Stacks 0D6X.

## Main definitions

* `CategoryTheory.Adjunction.extAcyclic`: the `Ext`-acyclic objects of an adjunction.

## Main results

* `CategoryTheory.mono_of_forall_factors_injective`: a morphism through which every map from its
  source to an injective object factors is a monomorphism.
* `CategoryTheory.Adjunction.extAcyclic_shortExact`: the two conditions of Stacks 05T8 for the
  `Ext`-acyclic class, in the variance of a left derived functor.
* `CategoryTheory.Adjunction.map_acyclic_of_extAcyclic`: `F` carries a bounded above acyclic
  complex with `Ext`-acyclic terms to an acyclic complex.
* `CategoryTheory.Adjunction.extAcyclic_coproduct`: the class is closed under arbitrary direct
  sums, so it suffices to check the generators.

## Implementation notes

The acyclicity of the image complex is not proved by hand: it is
`CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact`, which asks exactly that `F`
keep the cycles sequences `Z^i(K) ⟶ K^i ⟶ Z^{i+1}(K)` short exact, and that is what
`extAcyclic_shortExact` delivers once the cycles are known to be `Ext`-acyclic. The cycles are,
by downward induction from the bound: above it they are zero, and each step is the same short
exact sequence read in the other direction.

The companion file `StacksFrontier/Algebra/Homology/DerivedCategory/AcyclicObjects.lean` carries
the same criterion in the opposite variance — `RightAcyclicCriterion.map_quasiIso` and
`Functor.le_rightAcyclic_op`, Stacks 05T8 and 05T9 — and its private `map_acyclic` is the exact
twin of `map_acyclic_of_extAcyclic` for a bounded below complex. The statements here are not
obtained from those by passing to opposite categories: transporting `mapHomologicalComplex`
across `CochainComplex.opEquivalence` costs more than running the cycles engine
directly, and the engine is indifferent to variance.

Closure under direct sums is `Abelian.Ext.coproductAddEquiv`, which identifies `Ext` out of a
coproduct with the product of the `Ext`s and so needs no derived-category coproducts.

## References

* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory

/-- **A morphism out of which every map to an injective object factors is a monomorphism.**
Apply the hypothesis to the extension to the source of the embedding of the kernel into an
injective object: the resulting factorization through the morphism kills that embedding, which
is a monomorphism, so the kernel is zero. -/
theorem mono_of_forall_factors_injective {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] {X Y : A} (f : X ⟶ Y)
    (hf : ∀ I : A, Injective I → ∀ a : X ⟶ I, ∃ b : Y ⟶ I, f ≫ b = a) : Mono f := by
  refine Abelian.mono_of_kernel_ι_eq_zero f ?_
  obtain ⟨b, hb⟩ := hf (Injective.under (kernel f)) inferInstance
    (Injective.factorThru (Injective.ι (kernel f)) (kernel.ι f))
  have h0 : Injective.ι (kernel f) = 0 := by
    rw [← Injective.comp_factorThru (Injective.ι (kernel f)) (kernel.ι f), ← hb,
      ← Category.assoc, kernel.condition, zero_comp]
  have : Mono (0 : kernel f ⟶ Injective.under (kernel f)) := by
    rw [← h0]; infer_instance
  exact (IsZero.of_mono_zero (kernel f) (Injective.under (kernel f))).eq_of_src _ _

namespace Adjunction

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{w} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [EnoughInjectives B]
  {F : A ⥤ B} {G : B ⥤ A}

/-- The **`Ext`-acyclic objects** of an adjunction `F ⊣ G`: those `X` with
`Ext^n(X, G I) = 0` for every injective object `I` of the target and every `n ≥ 1`. This is the
class with which the criterion of Stacks 0794 is run for the left derived functor of `F`. -/
def extAcyclic (_adj : F ⊣ G) : ObjectProperty A := fun X =>
  ∀ I : B, Injective I → ∀ n : ℕ, 1 ≤ n → Subsingleton (Ext X (G.obj I) n)

omit [Abelian B] [EnoughInjectives B] in
/-- A zero object is `Ext`-acyclic: every `Ext` class out of it is the identity composed with
itself, and the identity of a zero object is zero. -/
lemma extAcyclic_of_isZero (adj : F ⊣ G) {X : A} (hX : IsZero X) : adj.extAcyclic X := by
  intro I _ n _
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.mk₀_id_comp x, hX.eq_of_src (𝟙 X) 0]
  simp

omit [Abelian B] [EnoughInjectives B] in
/-- **`Ext`-acyclicity transports along an isomorphism.** An `Ext` class out of the target
becomes, after precomposition with the isomorphism, a class out of the source, which vanishes;
precomposing back with the inverse recovers it. -/
lemma extAcyclic_of_iso (adj : F ⊣ G) {X Y : A} (e : X ≅ Y) (hX : adj.extAcyclic X) :
    adj.extAcyclic Y := by
  intro I hI n hn
  refine subsingleton_of_forall_eq 0 fun y => ?_
  have h0 : (Ext.mk₀ e.hom).comp y (zero_add n) = 0 :=
    @Subsingleton.elim _ (hX I hI n hn) _ _
  have : (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp y (zero_add n)) (zero_add n) = y := by
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id, Ext.mk₀_id_comp]
  rw [← this, h0]
  simp

omit [Abelian B] [EnoughInjectives B] in
/-- **The `Ext`-acyclic class is closed under arbitrary direct sums**, because `Ext` out of a
coproduct is the product of the `Ext`s (`Abelian.Ext.coproductAddEquiv`). So the generators of
the class are all that has to be checked. -/
lemma extAcyclic_coproduct (adj : F ⊣ G) [EnoughInjectives A] {ι : Type*} (X : ι → A)
    [HasCoproduct X] (hX : ∀ i, adj.extAcyclic (X i)) : adj.extAcyclic (∐ X) := by
  intro I hI n hn
  refine subsingleton_of_forall_eq 0 fun x => ?_
  refine (Ext.coproductAddEquiv X (G.obj I) n).injective ?_
  funext i
  exact @Subsingleton.elim _ (hX i I hI n hn) _ _

variable (adj : F ⊣ G) [F.Additive] [PreservesFiniteColimits F]

/-- **The two conditions of Stacks 05T8 for the `Ext`-acyclic class**, in the variance of a left
derived functor: given a short exact sequence whose last two terms are `Ext`-acyclic, the first
term is `Ext`-acyclic and the sequence stays short exact after applying `F`.

The first half is the contravariant long exact sequence of `Ext`: a class in
`Ext^n(S.X₁, G I)` with `n ≥ 1` dies in `Ext^{n+1}(S.X₃, G I) = 0`, hence comes from
`Ext^n(S.X₂, G I) = 0`.

The second half is where the right exactness of `F` is not enough. Exactness in the middle and
surjectivity on the right are formal, `F` preserving cokernels; injectivity on the left is the
same long exact sequence in degree zero: `Ext^1(S.X₃, G I) = 0` makes every map
`S.X₁ ⟶ G I` factor through `S.f`, which by adjunction makes every map `F S.X₁ ⟶ I` factor
through `F S.f`, and `mono_of_forall_factors_injective` concludes. -/
theorem extAcyclic_shortExact (S : ShortComplex A) (hS : S.ShortExact)
    (h₂ : adj.extAcyclic S.X₂) (h₃ : adj.extAcyclic S.X₃) :
    adj.extAcyclic S.X₁ ∧ (S.map F).ShortExact := by
  have key : ∀ I : B, Injective I → ∀ (n : ℕ) (x : Ext S.X₁ (G.obj I) n),
      ∃ x₂ : Ext S.X₂ (G.obj I) n, (Ext.mk₀ S.f).comp x₂ (zero_add n) = x := by
    intro I hI n x
    have := h₃ I hI (n + 1) n.succ_pos
    exact Ext.contravariant_sequence_exact₁ hS _ x (add_comm 1 n) (Subsingleton.elim _ _)
  constructor
  · intro I hI n hn
    refine subsingleton_of_forall_eq 0 fun x₁ => ?_
    obtain ⟨x₂, rfl⟩ := key I hI n x₁
    have := h₂ I hI n hn
    rw [Subsingleton.elim x₂ 0]
    simp
  · have hmono : Mono (F.map S.f) := by
      refine mono_of_forall_factors_injective _ fun I hI a => ?_
      obtain ⟨x₂, hx₂⟩ := key I hI 0 (Ext.mk₀ (adj.homEquiv S.X₁ I a))
      obtain ⟨b', rfl⟩ := (Ext.mk₀_bijective S.X₂ (G.obj I)).2 x₂
      have hb' : S.f ≫ b' = adj.homEquiv S.X₁ I a :=
        (Ext.mk₀_bijective S.X₁ (G.obj I)).1 (by rw [← hx₂, Ext.mk₀_comp_mk₀])
      refine ⟨(adj.homEquiv S.X₂ I).symm b', (adj.homEquiv S.X₁ I).injective ?_⟩
      rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply, hb']
    have := hS.epi_g
    exact { exact := hS.exact.map_of_epi_of_preservesCokernel F hS.epi_g inferInstance
            mono_f := hmono
            epi_g := (inferInstance : Epi (F.map S.g)) }

/-- **The cycles of a bounded above acyclic complex with `Ext`-acyclic terms are
`Ext`-acyclic.** Above the bound they are zero; each step down is the cycles sequence
`Z^{i}(K) ⟶ K^{i} ⟶ Z^{i+1}(K)`, whose last two terms are `Ext`-acyclic by induction. -/
lemma extAcyclic_cycles (K : CochainComplex A ℤ) (a : ℤ) [K.IsStrictlyLE a] (hK : K.Acyclic)
    (hPK : ∀ n, adj.extAcyclic (K.X n)) (n : ℤ) : adj.extAcyclic (K.cycles n) := by
  have hzero : ∀ m : ℤ, a < m → adj.extAcyclic (K.cycles m) := fun m hm =>
    adj.extAcyclic_of_isZero ((K.isZero_of_isStrictlyLE a m hm).of_mono (K.iCycles m))
  by_cases hn : a < n
  · exact hzero n hn
  · refine Int.leInductionDown (m := a + 1) (hzero (a + 1) (by omega)) ?_ n (by omega)
    intro m _ ih
    exact (adj.extAcyclic_shortExact _
      (K.cyclesShortComplex_shortExact (i := m - 1) (j := m) (by simp) (hK m))
      (hPK (m - 1)) ih).1

/-- **`F` carries a bounded above acyclic complex with `Ext`-acyclic terms to an acyclic
complex.** This is the hypothesis that the criterion of Stacks 0794 leaves open for the left
derived functor of `F`, reduced to the object-level vanishing of `Ext^{≥1}(-, G I)`.

The transfer is `CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact`: all it asks
is that `F` keep each cycles sequence of the complex short exact, and that is the second
conclusion of `extAcyclic_shortExact` applied to the cycles sequence, whose middle term is a
term of the complex and whose last term is a group of cycles. -/
theorem map_acyclic_of_extAcyclic (K : CochainComplex A ℤ) (a : ℤ) [K.IsStrictlyLE a]
    (hK : K.Acyclic) (hPK : ∀ n, adj.extAcyclic (K.X n)) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic :=
  CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact F K fun i j hij =>
    (adj.extAcyclic_shortExact _ (K.cyclesShortComplex_shortExact hij (hK j)) (hPK i)
      (adj.extAcyclic_cycles K a hK hPK j)).2

end Adjunction

end CategoryTheory

end
