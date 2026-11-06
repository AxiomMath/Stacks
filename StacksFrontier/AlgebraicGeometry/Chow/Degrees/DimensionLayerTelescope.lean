module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass

/-!
# The telescope of a locally finite filtration in a dimension layer

Let `(S, δ)` be a base situation with a dimension function, let `X` be a scheme locally of finite
type over `S`, and let `k ∈ ℤ`. A coherent `𝒪_X`-module on a *Noetherian* scheme carries a finite
dévissage filtration, and that is how
`Stacks.Chow.dimensionLayerClassMemRange_of_isCoherent` computes its class in
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`. On a scheme that is merely locally of finite type over the base
no finite filtration is available — the multiplicities of the cycle of a coherent module are
bounded on every quasi-compact open and unbounded on `X` — and the source of Tag 02S9 replaces it
by an **infinite** filtration `F = F⁰ ⊇ F¹ ⊇ …` which dies on every quasi-compact open, so that
the direct sum `⨁_{p ≥ 0} F^p` is again coherent.

This module proves the identity in `K₀` that such a filtration is used for. Writing
`P = ⨁_{p ≥ 0} F^p`, the two short exact sequences

`0 ⟶ ⨁_{p ≥ 0} F^{p+1} ⟶ P ⟶ ⨁_{p ≥ 0} F^p/F^{p+1} ⟶ 0`  (termwise inclusion)

`0 ⟶ ⨁_{p ≥ 0} F^{p+1} ⟶ P ⟶ F⁰ ⟶ 0`  (inclusion of the summands of positive index)

have the same first two terms, so their third terms have the same class:

`[F⁰] = [⨁_{p ≥ 0} F^p/F^{p+1}]` in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`.

That is `Stacks.Chow.of_eq_natCoproduct_cokernel_of_filtration`. No Noetherian hypothesis is used:
local finiteness of the family of supports is what replaces it, and it is exactly what makes the
direct sums coherent.

## Main definitions

* `Stacks.Chow.natCoproduct` — the direct sum `⨁_{p ≥ 0} A p` of a sequence of `𝒪_X`-modules,
  together with `Stacks.Chow.natCoproduct.ι`, `Stacks.Chow.natCoproduct.desc` and
  `Stacks.Chow.natCoproduct.map`, its inclusions, the maps out of it, and the direct sum of a
  sequence of morphisms.
* `Stacks.Chow.natCoproduct.proj`, `Stacks.Chow.natCoproduct.shift` and
  `Stacks.Chow.natCoproduct.retr` — the projection onto the zeroth summand, the inclusion of the
  summands of positive index, and the retraction onto them.
* `Stacks.Chow.natCoproduct.shiftSplitting` — the splitting of
  `0 ⟶ ⨁_{p ≥ 0} A (p+1) ⟶ ⨁_{p ≥ 0} A p ⟶ A 0 ⟶ 0` exhibiting it as a short exact sequence.

## Main results

* `Stacks.Chow.natCoproduct.isColimitCokernelCofork` and
  `Stacks.Chow.natCoproduct.shortExact_map` — the direct sum of a sequence of monomorphisms is a
  monomorphism whose cokernel is the direct sum of the cokernels.
* `Stacks.Chow.natCoproduct.shiftShortExact` — the other short exact sequence, split.
* `Stacks.Chow.isCoherent_natCoproduct` and `Stacks.Chow.supp_natCoproduct_subset` — a direct sum
  of coherent modules with locally finite supports is coherent, and its support is contained in
  the union of the supports.
* `Stacks.Chow.of_eq_natCoproduct_cokernel_of_filtration` — **the telescope**: for a decreasing
  sequence of coherent `𝒪_X`-modules with locally finite supports of delta-dimension at most `k`,
  the class of the zeroth term in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is the class of the direct sum
  of the successive quotients.

## Implementation notes

The index type of a coproduct in `X.Modules` must live in the universe `u` of the scheme, so the
sequences are indexed by `ℕ` and the coproducts by `ULift.{u} ℕ`; `Stacks.Chow.natCoproduct.ι` and
`Stacks.Chow.natCoproduct.hom_ext` hide the lift from everything downstream. The `ext` attribute is
*not* put on `hom_ext`: the `ext` tactic would then still prefer the ambient extensionality of a
morphism of sheaves of modules and reduce a goal about the coproduct to one about sections.

The two maps `⨁_{p ≥ 0} A (p+1) ⟶ ⨁_{p ≥ 0} A p` used here are different — the termwise inclusion
and the shift — and neither is needed to be the other: a short exact sequence contributes to the
Grothendieck group through its three *objects*, so the two sequences cancel their common first two
terms whatever their maps are.

Monomorphy of a direct sum of monomorphisms is the only place where exactness of coproducts enters,
and it is available as an instance for the monomorphisms of any category where coproducts are
stable under them. The cokernel is identified by hand, from the universal property: a map out of
`⨁ A p` killing the termwise inclusion is a sequence of maps out of `A p` killing `u p`, which is a
sequence of maps out of `cokernel (u p)`.

## References

* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Direct sums indexed by the natural numbers -/

/-- The direct sum `⨁_{p ≥ 0} A p` of a sequence of `𝒪_X`-modules. The index type of a coproduct
in `X.Modules` lives in the universe of the scheme, so the sum is taken over `ULift ℕ`. -/
def natCoproduct (A : ℕ → X.Modules) : X.Modules :=
  ∐ fun p : ULift.{u} ℕ ↦ A p.down

namespace natCoproduct

/-- The inclusion of the `p`-th summand into `⨁_{q ≥ 0} A q`. -/
def ι (A : ℕ → X.Modules) (p : ℕ) : A p ⟶ natCoproduct A :=
  Sigma.ι (fun q : ULift.{u} ℕ ↦ A q.down) ⟨p⟩

/-- Two morphisms out of `⨁_{p ≥ 0} A p` agreeing on every summand are equal. -/
theorem hom_ext {A : ℕ → X.Modules} {W : X.Modules} {g h : natCoproduct A ⟶ W}
    (hgh : ∀ p, ι A p ≫ g = ι A p ≫ h) : g = h :=
  Sigma.hom_ext _ _ fun p ↦ hgh p.down

/-- The morphism out of `⨁_{p ≥ 0} A p` determined by a morphism out of each summand. -/
def desc {A : ℕ → X.Modules} {W : X.Modules} (g : ∀ p, A p ⟶ W) : natCoproduct A ⟶ W :=
  Sigma.desc fun p ↦ g p.down

/-- The morphism `desc g` restricts to `g p` on the `p`-th summand. -/
@[reassoc (attr := simp)]
theorem ι_desc {A : ℕ → X.Modules} {W : X.Modules} (g : ∀ p, A p ⟶ W) (p : ℕ) :
    ι A p ≫ desc g = g p :=
  Sigma.ι_desc _ _

/-- The direct sum of a sequence of morphisms. -/
def map {A B : ℕ → X.Modules} (u : ∀ p, A p ⟶ B p) : natCoproduct A ⟶ natCoproduct B :=
  Limits.Sigma.map fun p : ULift.{u} ℕ ↦ u p.down

/-- The direct sum `map u` restricts to `u p` on the `p`-th summand. -/
@[reassoc (attr := simp)]
theorem ι_map {A B : ℕ → X.Modules} (u : ∀ p, A p ⟶ B p) (p : ℕ) :
    ι A p ≫ map u = u p ≫ ι B p :=
  Sigma.ι_map _ _

/-- **The direct sum of a sequence of monomorphisms is a monomorphism.** -/
theorem mono_map {A B : ℕ → X.Modules} (u : ∀ p, A p ⟶ B p) (hu : ∀ p, Mono (u p)) :
    Mono (map u) :=
  have : ∀ p : ULift.{u} ℕ, Mono (u p.down) := fun p ↦ hu p.down
  MorphismProperty.instMonoMapOfIsStableUnderCoproductsOfShapeMonomorphisms (ULift.{u, 0} ℕ)
    fun p ↦ u p.down

/-- **The direct sum of a sequence of epimorphisms is an epimorphism.** -/
theorem epi_map {A B : ℕ → X.Modules} (u : ∀ p, A p ⟶ B p) (hu : ∀ p, Epi (u p)) :
    Epi (map u) :=
  ⟨fun {_} g h hgh ↦ hom_ext fun p ↦ by
    have := hu p
    refine (cancel_epi (u p)).1 ?_
    have h₁ := congrArg (fun φ ↦ ι A p ≫ φ) hgh
    simpa using h₁⟩

/-! ### The split sequence of the shift -/

/-- The projection of `⨁_{p ≥ 0} A p` onto its zeroth summand. -/
def proj (A : ℕ → X.Modules) : natCoproduct A ⟶ A 0 :=
  desc fun p ↦ Nat.rec (motive := fun q ↦ A q ⟶ A 0) (𝟙 (A 0)) (fun _ _ ↦ 0) p

/-- The projection onto the zeroth summand is the identity on that summand. -/
@[reassoc (attr := simp)]
theorem ι_proj_zero (A : ℕ → X.Modules) : ι A 0 ≫ proj A = 𝟙 (A 0) := by
  simp [proj]

/-- The projection onto the zeroth summand vanishes on the summands of positive index. -/
@[reassoc (attr := simp)]
theorem ι_proj_succ (A : ℕ → X.Modules) (p : ℕ) : ι A (p + 1) ≫ proj A = 0 := by
  simp [proj]

/-- The inclusion of the summands of positive index, `⨁_{p ≥ 0} A (p+1) ⟶ ⨁_{p ≥ 0} A p`. -/
def shift (A : ℕ → X.Modules) : natCoproduct (fun p ↦ A (p + 1)) ⟶ natCoproduct A :=
  desc fun p ↦ ι A (p + 1)

/-- The retraction of `⨁_{p ≥ 0} A p` onto the summands of positive index. -/
def retr (A : ℕ → X.Modules) : natCoproduct A ⟶ natCoproduct (fun p ↦ A (p + 1)) :=
  desc fun p ↦ Nat.rec (motive := fun q ↦ A q ⟶ natCoproduct fun r ↦ A (r + 1))
    0 (fun n _ ↦ ι (fun r ↦ A (r + 1)) n) p

/-- The retraction onto the summands of positive index vanishes on the zeroth summand. -/
@[reassoc (attr := simp)]
theorem ι_retr_zero (A : ℕ → X.Modules) : ι A 0 ≫ retr A = 0 := by
  simp [retr]

/-- The retraction sends the summand `A (p + 1)` identically to the `p`-th summand of
`⨁_{q ≥ 0} A (q+1)`. -/
@[reassoc (attr := simp)]
theorem ι_retr_succ (A : ℕ → X.Modules) (p : ℕ) :
    ι A (p + 1) ≫ retr A = ι (fun r ↦ A (r + 1)) p := by
  simp [retr]

/-- The inclusion of the summands of positive index composed with the projection onto the
zeroth summand is zero. -/
theorem shift_comp_proj (A : ℕ → X.Modules) : shift A ≫ proj A = 0 :=
  hom_ext fun p ↦ by simp [shift]

/-- The sequence `0 ⟶ ⨁_{p ≥ 0} A (p+1) ⟶ ⨁_{p ≥ 0} A p ⟶ A 0 ⟶ 0`, the first map the inclusion
of the summands of positive index and the second the projection onto the zeroth summand. -/
def shiftShortComplex (A : ℕ → X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (shift A) (proj A) (shift_comp_proj A)

/-- The decomposition of `⨁_{p ≥ 0} A p` into its zeroth summand and the summands of positive
index, read as a splitting of `Stacks.Chow.natCoproduct.shiftShortComplex`. -/
def shiftSplitting (A : ℕ → X.Modules) : (shiftShortComplex A).Splitting where
  r := retr A
  s := ι A 0
  f_r := by
    change shift A ≫ retr A = 𝟙 _
    exact hom_ext fun p ↦ by simp [shift]
  s_g := by
    change ι A 0 ≫ proj A = 𝟙 _
    simp
  id := by
    change retr A ≫ shift A + proj A ≫ ι A 0 = 𝟙 _
    refine hom_ext fun p ↦ ?_
    cases p with
    | zero => simp [Preadditive.comp_add, shift]
    | succ n => simp [Preadditive.comp_add, shift]

/-- **The shift is a split monomorphism with cokernel the zeroth summand.** -/
theorem shiftShortExact (A : ℕ → X.Modules) : (shiftShortComplex A).ShortExact :=
  (shiftSplitting A).shortExact

/-! ### The termwise sequence -/

/-- The direct sum of the `u p` composed with the direct sum of the quotient maps
`B p ⟶ cokernel (u p)` is zero. -/
theorem map_comp_map_cokernelπ {A B : ℕ → X.Modules} (u : ∀ p, A p ⟶ B p) :
    map u ≫ map (fun p ↦ cokernel.π (u p)) = 0 :=
  hom_ext fun p ↦ by simp

/-- **The direct sum of the quotient maps is a cokernel of the direct sum of the maps.** A
morphism out of `⨁_{p ≥ 0} B p` killing the direct sum of the `u p` is a sequence of morphisms out
of `B p` killing `u p`, hence a sequence of morphisms out of `cokernel (u p)`. -/
def isColimitCokernelCofork {A B : ℕ → X.Modules} (u : ∀ p, A p ⟶ B p) :
    IsColimit (CokernelCofork.ofπ (map fun p ↦ cokernel.π (u p)) (map_comp_map_cokernelπ u)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {_} g' hg' ↦ desc fun p ↦ cokernel.desc (u p) (ι B p ≫ g') (by
      have := congrArg (fun φ ↦ ι A p ≫ φ) hg'
      simpa using this))
    (fun {_} g' hg' ↦ hom_ext fun p ↦ by simp)
    (fun {_} g' hg' m hm ↦ hom_ext fun p ↦ by
      refine (cancel_epi (cokernel.π (u p))).1 ?_
      have h₁ := congrArg (fun φ ↦ ι B p ≫ φ) hm
      simpa using h₁)

/-- **The termwise short exact sequence.** A sequence of monomorphisms `A p ⟶ B p` gives the short
exact sequence `0 ⟶ ⨁ A p ⟶ ⨁ B p ⟶ ⨁ cokernel (u p) ⟶ 0`. -/
theorem shortExact_map {A B : ℕ → X.Modules} (u : ∀ p, A p ⟶ B p) (hu : ∀ p, Mono (u p)) :
    (ShortComplex.mk (map u) (map fun p ↦ cokernel.π (u p)) (map_comp_map_cokernelπ u)).ShortExact
    where
  mono_f := mono_map u hu
  epi_g := epi_map _ fun p ↦ have := hu p; (Stacks.Chow.shortExact_mk_cokernel (u p)).epi_g
  exact := ShortComplex.exact_of_g_is_cokernel _ (isColimitCokernelCofork u)

end natCoproduct

/-! ### Coherence and support of a locally finite direct sum -/

/-- **A direct sum of coherent `𝒪_X`-modules with locally finite supports is coherent.** -/
theorem isCoherent_natCoproduct (A : ℕ → X.Modules) (hc : ∀ p, (A p).IsCoherent)
    (hLF : LocallyFinite fun p : ULift.{u} ℕ ↦ SheafOfModules.supp (A p.down)) :
    (natCoproduct A).IsCoherent :=
  isCoherent_coproduct_of_locallyFinite _ (fun p ↦ hc p.down) hLF

/-- The support of `⨁_{p ≥ 0} A p` is contained in the union of the supports of the summands. -/
theorem supp_natCoproduct_subset (A : ℕ → X.Modules) :
    SheafOfModules.supp (natCoproduct A) ⊆ ⋃ p, SheafOfModules.supp (A p) := by
  intro x hx
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (supp_sigma_subset_iUnion_supp _ hx)
  exact Set.mem_iUnion.2 ⟨p.down, hp⟩

/-! ### The telescope -/

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-- **The telescope of a locally finite filtration.** Let `A 0 ⊇ A 1 ⊇ …` be a decreasing sequence
of coherent `𝒪_X`-modules whose supports form a locally finite family and have delta-dimension at
most `k`. Then in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` the class of `A 0` is the class of the direct sum
`⨁_{p ≥ 0} A p / A (p+1)` of the successive quotients.

Both sequences `0 ⟶ ⨁ A (p+1) ⟶ ⨁ A p ⟶ ? ⟶ 0` — the termwise inclusion and the inclusion of the
summands of positive index — have the same first two terms, so their third terms, `⨁ A p/A (p+1)`
and `A 0`, have the same class. No Noetherian hypothesis is needed: local finiteness of the family
of supports is what makes the direct sums coherent. -/
theorem of_eq_natCoproduct_cokernel_of_filtration (A : ℕ → X.Modules) (u : ∀ p, A (p + 1) ⟶ A p)
    (hu : ∀ p, Mono (u p)) (hc : ∀ p, (A p).IsCoherent)
    (hLF : LocallyFinite fun p : ULift.{u} ℕ ↦ SheafOfModules.supp (A p.down))
    (hdim : ∀ p, ∀ x ∈ SheafOfModules.supp (A p),
      relativeDimension C.dimensionFunction f x ≤ k)
    (F G : CoherentModulesDimLE C f k) (hF : F.obj.obj = A 0)
    (hG : G.obj.obj = natCoproduct fun p ↦ cokernel (u p)) :
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj G) := by
  have hLFS : LocallyFinite fun p : ULift.{u} ℕ ↦ SheafOfModules.supp (A (p.down + 1)) :=
    hLF.comp_injOn (g := fun p : ULift.{u} ℕ ↦ (⟨p.down + 1⟩ : ULift.{u} ℕ))
      (fun a _ b _ hab ↦ ULift.ext (by
        have : a.down + 1 = b.down + 1 := congrArg ULift.down hab
        omega))
  have hepi : ∀ p, Epi (cokernel.π (u p)) := fun p ↦
    have := hu p; (shortExact_mk_cokernel (u p)).epi_g
  have hsuppC : ∀ p, SheafOfModules.supp (cokernel (u p)) ⊆ SheafOfModules.supp (A p) :=
    fun p ↦ @supp_subset_of_epi X _ _ (cokernel.π (u p)) (hepi p)
  have hLFC : LocallyFinite fun p : ULift.{u} ℕ ↦
      SheafOfModules.supp (cokernel (u p.down)) :=
    hLF.subset fun p ↦ hsuppC p.down
  have hcP : (natCoproduct A).IsCoherent := isCoherent_natCoproduct A hc hLF
  have hcQ : (natCoproduct fun p ↦ A (p + 1)).IsCoherent :=
    isCoherent_natCoproduct _ (fun p ↦ hc (p + 1)) hLFS
  have hcC : ∀ p, (cokernel (u p)).IsCoherent := fun p ↦
    have := hc (p + 1); have := hc p
    AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel (u p)
  have hcB : (natCoproduct fun p ↦ cokernel (u p)).IsCoherent :=
    isCoherent_natCoproduct _ hcC hLFC
  have hd : ∀ B : ℕ → X.Modules, (∀ p, ∀ x ∈ SheafOfModules.supp (B p),
      relativeDimension C.dimensionFunction f x ≤ k) →
      ∀ x ∈ SheafOfModules.supp (natCoproduct B), relativeDimension C.dimensionFunction f x ≤ k :=
    fun B hB x hx ↦ by
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (supp_natCoproduct_subset B hx)
      exact hB p x hp
  have hdP := hd A hdim
  have hdQ := hd (fun p ↦ A (p + 1)) fun p ↦ hdim (p + 1)
  have hdB := hd (fun p ↦ cokernel (u p)) fun p x hx ↦ hdim p x (hsuppC p hx)
  have h₁ := of_add_of_shortExact C f k
    (dimLEObj C f k _ hcQ hdQ) (dimLEObj C f k _ hcP hdP) (dimLEObj C f k _ (hc 0) (hdim 0))
    (natCoproduct.shift A) (natCoproduct.proj A) (natCoproduct.shift_comp_proj A)
    (natCoproduct.shiftShortExact A)
  have h₂ := of_add_of_shortExact C f k
    (dimLEObj C f k _ hcQ hdQ) (dimLEObj C f k _ hcP hdP) (dimLEObj C f k _ hcB hdB)
    (natCoproduct.map u) (natCoproduct.map fun p ↦ cokernel.π (u p))
    (natCoproduct.map_comp_map_cokernelπ u) (natCoproduct.shortExact_map u hu)
  have hFF : F = dimLEObj C f k _ (hc 0) (hdim 0) := dimLE_ext C f k hF
  have hGG : G = dimLEObj C f k _ hcB hdB := dimLE_ext C f k hG
  rw [hFF, hGG]
  exact add_left_cancel (h₁.symm.trans h₂)

end Stacks.Chow

end
