module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The two short exact sequences attached to a composite of monomorphisms

Let `i : F ⟶ A` and `j : A ⟶ B` be monomorphisms in an abelian category and put
`Q = coker (i ≫ j)`. Then

* `0 ⟶ F ⟶ B ⟶ Q ⟶ 0` is short exact, with maps `i ≫ j` and the cokernel projection;
* `0 ⟶ coker i ⟶ Q ⟶ coker j ⟶ 0` is short exact, with the maps induced by `j` and by `𝟙 B`.

These are the two sequences of the inductive step of Stacks Tag 02UI. The second is the tail of
Mathlib's six-term sequence `CategoryTheory.kernelCokernelCompSequence`, whose term `ker j`
vanishes because `j` is a monomorphism.

The same is then stated for two given short exact sequences `0 ⟶ F ⟶ A ⟶ L ⟶ 0` and
`0 ⟶ A ⟶ B ⟶ C ⟶ 0`, with `L` and `C` in place of the two cokernels: the sequence
`0 ⟶ L ⟶ Q ⟶ C ⟶ 0` is short exact, and the evident squares commute.

## Main results

* `Stacks.Chow.GenuineChern.shortExact_compCokernelSequence`
* `Stacks.Chow.GenuineChern.shortExact_cokernelCompSequence`
* `Stacks.Chow.GenuineChern.shortExact_compQuotient`
* `Stacks.Chow.GenuineChern.exists_shortExact_pair_abelian`: the same in existential form, with
  the second sequence's first term identified with the first sequence's middle term by an
  isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Chow.GenuineChern

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

section Monos

variable {F A B : 𝒜} (i : F ⟶ A) (j : A ⟶ B)

/-- The short complex `F ⟶ B ⟶ coker (i ≫ j)`. -/
abbrev compCokernelSequence : ShortComplex 𝒜 :=
  ShortComplex.mk (i ≫ j) (cokernel.π (i ≫ j)) (cokernel.condition _)

/-- `0 ⟶ F ⟶ B ⟶ coker (i ≫ j) ⟶ 0` is short exact when `i` and `j` are monomorphisms. -/
theorem shortExact_compCokernelSequence [Mono i] [Mono j] :
    (compCokernelSequence i j).ShortExact :=
  { exact := ShortComplex.exact_cokernel (i ≫ j) }

/-- The short complex `coker i ⟶ coker (i ≫ j) ⟶ coker j` of the maps induced by `j` and by
`𝟙 B`. -/
abbrev cokernelCompSequence : ShortComplex 𝒜 :=
  ShortComplex.mk (cokernel.map i (i ≫ j) (𝟙 F) j (by simp))
    (cokernel.map (i ≫ j) j i (𝟙 B) (by simp)) (by ext; simp)

/-- The two maps of `Stacks.Chow.GenuineChern.cokernelCompSequence` compose to zero. -/
@[reassoc (attr := simp)]
theorem cokernel_map_comp_map :
    cokernel.map i (i ≫ j) (𝟙 F) j (by simp) ≫ cokernel.map (i ≫ j) j i (𝟙 B) (by simp) = 0 :=
  (cokernelCompSequence i j).zero

/-- `0 ⟶ coker i ⟶ coker (i ≫ j) ⟶ coker j ⟶ 0` is short exact when `j` is a monomorphism. -/
theorem shortExact_cokernelCompSequence [Mono j] : (cokernelCompSequence i j).ShortExact :=
  ShortComplex.ShortExact.mk' (kernelCokernelCompSequence.snakeInput i j).L₃_exact
    ((kernelCokernelCompSequence.snakeInput i j).L₂'_exact.mono_g
      ((isZero_kernel_of_mono j).eq_of_src _ _))
    (by dsimp; infer_instance)

end Monos

section ShortExact

variable {F A B L C : 𝒜} {i : F ⟶ A} {p : A ⟶ L} {w₁ : i ≫ p = 0}
  {j : A ⟶ B} {q : B ⟶ C} {w₂ : j ≫ q = 0}
  (hS₁ : (ShortComplex.mk i p w₁).ShortExact) (hS₂ : (ShortComplex.mk j q w₂).ShortExact)

/-- The identification of the cokernel of `i` with the third term `L` of a short exact sequence
`0 ⟶ F ⟶ A ⟶ L ⟶ 0`. -/
def cokernelIsoOfShortExact {F A L : 𝒜} {i : F ⟶ A} {p : A ⟶ L} {w : i ≫ p = 0}
    (hS : (ShortComplex.mk i p w).ShortExact) : cokernel i ≅ L :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel i) hS.gIsCokernel

/-- The identification `coker i ≅ L` carries the cokernel projection `A ⟶ coker i` to `p`. -/
@[reassoc (attr := simp)]
theorem π_cokernelIsoOfShortExact_hom {F A L : 𝒜} {i : F ⟶ A} {p : A ⟶ L} {w : i ≫ p = 0}
    (hS : (ShortComplex.mk i p w).ShortExact) :
    cokernel.π i ≫ (cokernelIsoOfShortExact hS).hom = p :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel i) hS.gIsCokernel
    WalkingParallelPair.one

/-- The identification `L ≅ coker i` carries `p` to the cokernel projection `A ⟶ coker i`. -/
@[reassoc (attr := simp)]
theorem comp_cokernelIsoOfShortExact_inv {F A L : 𝒜} {i : F ⟶ A} {p : A ⟶ L} {w : i ≫ p = 0}
    (hS : (ShortComplex.mk i p w).ShortExact) :
    p ≫ (cokernelIsoOfShortExact hS).inv = cokernel.π i :=
  IsColimit.comp_coconePointUniqueUpToIso_inv (cokernelIsCokernel i) hS.gIsCokernel
    WalkingParallelPair.one

include hS₁ in
/-- The map `L ⟶ coker (i ≫ j)` induced by `j`. -/
def compQuotientι : L ⟶ cokernel (i ≫ j) :=
  (cokernelIsoOfShortExact hS₁).inv ≫ cokernel.map i (i ≫ j) (𝟙 F) j (by simp)

include hS₂ in
/-- The map `coker (i ≫ j) ⟶ C` induced by `q`. -/
def compQuotientπ : cokernel (i ≫ j) ⟶ C :=
  cokernel.map (i ≫ j) j i (𝟙 B) (by simp) ≫ (cokernelIsoOfShortExact hS₂).hom

/-- The square `A ⟶ L ⟶ coker (i ≫ j)` = `A ⟶ B ⟶ coker (i ≫ j)` commutes. -/
@[reassoc (attr := simp)]
theorem comp_compQuotientι : p ≫ compQuotientι hS₁ (j := j) = j ≫ cokernel.π (i ≫ j) := by
  simp [compQuotientι]

/-- The square `B ⟶ coker (i ≫ j) ⟶ C` = `B ⟶ C` commutes. -/
@[reassoc (attr := simp)]
theorem π_compQuotientπ : cokernel.π (i ≫ j) ≫ compQuotientπ hS₂ (i := i) = q := by
  simp [compQuotientπ]

/-- The short complex `L ⟶ coker (i ≫ j) ⟶ C`. -/
abbrev compQuotientSequence : ShortComplex 𝒜 :=
  ShortComplex.mk (compQuotientι hS₁ (j := j)) (compQuotientπ hS₂ (i := i)) (by
    simp [compQuotientι, compQuotientπ])

/-- **The two short exact sequences of the 02UI step.** Given short exact sequences
`0 ⟶ F ⟶ A ⟶ L ⟶ 0` and `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, with `Q = coker (i ≫ j)` both
`0 ⟶ F ⟶ B ⟶ Q ⟶ 0` and `0 ⟶ L ⟶ Q ⟶ C ⟶ 0` are short exact. -/
theorem shortExact_compQuotient :
    (compCokernelSequence i j).ShortExact ∧ (compQuotientSequence hS₁ hS₂).ShortExact := by
  have := hS₁.mono_f
  have := hS₂.mono_f
  refine ⟨shortExact_compCokernelSequence i j, ?_⟩
  refine ShortComplex.shortExact_of_iso ?_ (shortExact_cokernelCompSequence i j)
  exact ShortComplex.isoMk (cokernelIsoOfShortExact hS₁) (Iso.refl _)
    (cokernelIsoOfShortExact hS₂) (by simp [compQuotientι]) (by simp [compQuotientπ])

/-- **The two short exact sequences of the 02UI step, in existential form.** Given short exact
sequences `S₁ : 0 ⟶ F ⟶ A ⟶ L ⟶ 0` and `S₂ : 0 ⟶ A' ⟶ B ⟶ C ⟶ 0` and an isomorphism
`A ≅ A'`, there are short exact sequences `T₂ : 0 ⟶ F ⟶ B ⟶ Q ⟶ 0` and
`T₃ : 0 ⟶ L ⟶ Q ⟶ C ⟶ 0` (with `Q = coker (F ⟶ B)`). -/
theorem exists_shortExact_pair_abelian (S₁ S₂ : ShortComplex 𝒜) (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (e : S₁.X₂ ≅ S₂.X₁) :
    ∃ T₂ T₃ : ShortComplex 𝒜, T₂.ShortExact ∧ T₃.ShortExact ∧ Nonempty (T₂.X₁ ≅ S₁.X₁) ∧
      Nonempty (T₂.X₂ ≅ S₂.X₂) ∧ Nonempty (T₂.X₃ ≅ T₃.X₂) ∧ Nonempty (T₃.X₁ ≅ S₁.X₃) ∧
      Nonempty (T₃.X₃ ≅ S₂.X₃) := by
  let e' : S₁ ≅ ShortComplex.mk (S₁.f ≫ e.hom) (e.inv ≫ S₁.g) (by simp) :=
    ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) (by simp) (by simp)
  have h₁' : (ShortComplex.mk (S₁.f ≫ e.hom) (e.inv ≫ S₁.g) (by simp)).ShortExact :=
    ShortComplex.shortExact_of_iso e' h₁
  have h₂' : (ShortComplex.mk S₂.f S₂.g S₂.zero).ShortExact := h₂
  obtain ⟨hT₂, hT₃⟩ := shortExact_compQuotient h₁' h₂'
  exact ⟨_, _, hT₂, hT₃, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

end ShortExact

end Stacks.Chow.GenuineChern
