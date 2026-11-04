module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.RingTheory.Flat.Equalizer
public import StacksFrontier.Algebra.Homology.KFlat
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

-- Needed for the graded-object defeq `(L ⊗ K).X n = tensorObj L.X K.X n`, on which the
-- `ι_tensorObjDesc` / `tensorObj_ext` rewrites and the cofan-level `rw`s below rely.
set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Throughout, `R` is a commutative unital ring and all complexes are cochain
complexes of `R`-modules indexed by `ℤ` (differentials raise degree by `1`).

For complexes `A` and `B`, the *total tensor product complex*
`Tot(A ⊗_R B)` is the complex with degree-`n` term
`⊕_{p + q = n} A^p ⊗_R B^q` and the usual Koszul sign convention for the
differential `d(a ⊗ b) = d_A a ⊗ b + (-1)^p a ⊗ d_B b` for `a ∈ A^p`.

In Lean/Mathlib this total tensor product complex is exactly the monoidal
product `A ⊗ B` of the monoidal category
`HomologicalComplex (ModuleCat R) (ComplexShape.up ℤ)`
(`HomologicalComplex.monoidalCategory`), whose underlying graded object is the
direct sum `⊕_{p + q = n} A^p ⊗_R B^q` with the standard Koszul signs in the
differential.

## Main Definitions

- Definition 1 (Acyclic complex). A complex `L` is *acyclic* if `H^n(L) = 0`
  for all `n`, i.e. it is exact at every degree.  This is Mathlib's
  `HomologicalComplex.Acyclic`, namely `∀ n, L.ExactAt n`.

- Definition 2 (K-flat complex). A complex `K` is *K-flat* if for every acyclic
  complex `L`, the total complex `Tot(L ⊗_R K)` is acyclic.
  (Stacks Definition 15.60.1.)  This is `CochainComplex.KFlat`.

- Definition 3 (Short exact sequence of complexes). A sequence
  `0 → K₁ → K₂ → K₃ → 0` of complexes is short exact if `f`, `g` are chain maps
  and the termwise sequences `0 → K₁^n → K₂^n → K₃^n → 0` are exact for all `n`.
  Formalized via `CategoryTheory.ShortComplex.ShortExact` in the category of
  complexes.

## Main Statement

Theorem (Stacks Tag 0BYH, Lemma 15.60.6). Let `R` be a ring and let
`0 → K₁ → K₂ → K₃ → 0` be a short exact sequence of complexes of `R`-modules.
Assume `K₃^n` is a flat `R`-module for every `n`. If two out of the three
complexes `K₁, K₂, K₃` are K-flat, then so is the third.

## Universes

`R` ranges over an arbitrary universe `u`, as in Stacks. Mathlib's
`MonoidalCategory (ModuleCat.{u} R)` instance requires the module universe to
agree with the universe of `R`, so `ModuleCat R` below means `ModuleCat.{u} R`;
this matches `StacksFrontier.Algebra.Homology.KFlat`. The index types of the
coproduct decompositions (`ι`, `β`) stay in `Type`, since they are only ever
instantiated at `{p : ℤ × ℤ // p.1 + p.2 = n}`, and `ModuleCat.coprodIsoDirectSum`
accepts an index type in any universe no larger than the module universe.
-/

open CategoryTheory MonoidalCategory Limits

universe u

namespace KFlatTwoOutOfThree

/-- Abbreviation for cochain complexes of `R`-modules indexed by `ℤ`
(differentials raise degree by `1`).  This category carries the monoidal
structure given by the total tensor product complex. -/
@[sga "4½ Etat_0 1.2.1" "C(A) for A = ModuleCat R"]
abbrev Cx (R : Type u) [CommRing R] :=
  HomologicalComplex (ModuleCat.{u} R) (ComplexShape.up ℤ)

variable {R : Type u} [CommRing R]
variable (L : CochainComplex (ModuleCat.{u} R) ℤ)
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))

/- Definitions 1 and 2 are `HomologicalComplex.Acyclic` (exactness in every
degree) and `CochainComplex.KFlat` (acyclicity of `L ⊗ K` for every acyclic `L`).

Definition 3 (Short exact sequence of complexes) is realized below by a
`CategoryTheory.ShortComplex (CochainComplex (ModuleCat R) ℤ)` together with the
predicate `ShortComplex.ShortExact`, which packages: `f, g` are chain maps with
`g ∘ f = 0`, and the termwise sequences are short exact. -/

/-! ## Auxiliary lemmas (the proof sketch)

The mathematics reduces all three directional lemmas to
a single engine:

  (SG-B) **`tensor_shortExact`** — tensoring the SES of complexes by an arbitrary
         complex `L` gives a SES of (total tensor product) complexes, using
         flatness of every `K₃ⁿ`;
  (SG-C) **`acyclic_X₁_of_acyclic_X₂_X₃` /
         `acyclic_X₃_of_acyclic_X₁_X₂`** (and Mathlib's
         `ShortComplex.ShortExact.acyclic_X₂`) — two-out-of-three for acyclicity
         of a SES of complexes, via the long exact homology sequence.

Each directional lemma then takes an arbitrary acyclic `L`, forms the SES
`0 → L⊗K₁ → L⊗K₂ → L⊗K₃ → 0` (SG-B), and transfers acyclicity from two of the
three total complexes to the third (SG-C). -/

/- **(SG-B, the analytic heart.)** For any complex `L`, tensoring the short
exact sequence of complexes `S = (0 → K₁ → K₂ → K₃ → 0)` by `L` (applying the
functor `tensorLeft L`, i.e. forming `L ⊗ -`) yields again a short exact
sequence of complexes
`0 → Tot(L ⊗ K₁) → Tot(L ⊗ K₂) → Tot(L ⊗ K₃) → 0`,
PROVIDED every term `K₃ᵐ` is a flat `R`-module.

**Rigorous argument.**
By `HomologicalComplex.shortExact_of_degreewise_shortExact` it suffices, for each
degree `n : ℤ`, to show that the short complex obtained by evaluating
`S.map (tensorLeft L)` in degree `n` — i.e.
`((S.map (tensorLeft L)).map (eval (ModuleCat R) (up ℤ) n))` — is a short exact
sequence of `R`-modules.

Now `(L ⊗ Kᵢ).X n = ⊕_{p+q=n} (Lᵖ ⊗ Kᵢᵠ)` (the degree-`n` term of the total
tensor product complex; in Mathlib `(L ⊗ K).X n` is definitionally
`GradedObject.Monoidal.tensorObj L.X K.X n`, the coproduct over `p+q=n`). The two
evaluated maps are, on the summand `p+q=n`, the maps `Lᵖ ⊗ fᵠ` and `Lᵖ ⊗ gᵠ`
where `f = S.f`, `g = S.g` are the chain maps and `fᵠ, gᵠ` their degree-`q`
components. Since a short exact sequence of `R`-modules is exact iff it is exact
in each summand of a direct sum, and finite/arbitrary direct sums of short exact
sequences are short exact, it suffices to fix `p, q` with `p+q=n` and show that
`0 → Lᵖ ⊗ K₁ᵠ → Lᵖ ⊗ K₂ᵠ → Lᵖ ⊗ K₃ᵠ → 0`
is short exact, i.e. that applying `Lᵖ ⊗ -` to the termwise SES
`0 → K₁ᵠ → K₂ᵠ → K₃ᵠ → 0` (which is short exact by `hse` evaluated in degree `q`,
via `HomologicalComplex.shortExact` / `S.map (eval _ _ q)`) keeps it short exact.

This is precisely the universal-exactness property of a short exact sequence with
flat right term: because `K₃ᵠ` is flat, the sequence stays exact after tensoring
by the ARBITRARY module `Lᵖ`. Concretely:
  • right-exactness (surjectivity of `Lᵖ⊗g` and exactness in the middle) needs no
    flatness — `lTensor_exact` and `LinearMap.lTensor_surjective`;
  • left-exactness (injectivity of `Lᵖ⊗f`) is exactly
    `LinearMap.lTensor_injective_of_exact_of_flat`, whose hypothesis is that the
    END term (`K₃ᵠ`) is flat and which holds for the arbitrary tensoring module
    `Lᵖ`. (This is the only place the flatness hypothesis on `K₃` is used; cf.
    Stacks Algebra 10.39.12 / the purity of SES with flat quotient.)

Assembling these per-summand short exact sequences over `p+q=n` (direct sum of
short exact sequences is short exact) gives the degreewise SES, hence by
`shortExact_of_degreewise_shortExact` the SES of complexes.
 -/
/-- A map between coproduct cofans that is given summandwise by `ψ` factors, through the
canonical identifications with `∐`, as `Sigma.map ψ`. -/
theorem cofanMap_eq_sigmaMap {C : Type*} [Category C] {β : Type*} {A B : β → C}
    [Limits.HasCoproduct A] [Limits.HasCoproduct B]
    (c₁ : Limits.Cofan A) (c₂ : Limits.Cofan B) (hc₁ : Limits.IsColimit c₁)
    (hc₂ : Limits.IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt) (ψ : ∀ b, A b ⟶ B b)
    (hcomm : ∀ b, c₁.inj b ≫ φ = ψ b ≫ c₂.inj b) :
    φ = (hc₁.coconePointUniqueUpToIso (Limits.coproductIsCoproduct A)).hom ≫
      Limits.Sigma.map ψ ≫ (hc₂.coconePointUniqueUpToIso (Limits.coproductIsCoproduct B)).inv := by
  refine Limits.Cofan.IsColimit.hom_ext hc₁ _ _ fun b => ?_
  have hinj₁ : c₁.inj b ≫ _ = Limits.Sigma.ι A b :=
    hc₁.comp_coconePointUniqueUpToIso_hom (Limits.coproductIsCoproduct A) ⟨b⟩
  have hinj₂ : c₂.inj b ≫ _ = Limits.Sigma.ι B b :=
    hc₂.comp_coconePointUniqueUpToIso_hom (Limits.coproductIsCoproduct B) ⟨b⟩
  rw [hcomm b, ← Category.assoc, hinj₁, ← Category.assoc, Iso.eq_comp_inv, Category.assoc, hinj₂]
  simp [Limits.Sigma.map]

/-- A map between coproduct cofans that is given summandwise by monomorphisms is itself a
monomorphism. -/
theorem cofanMap_mono {C : Type*} [Category C] {β : Type*} {A B : β → C}
    [Limits.HasCoproduct A] [Limits.HasCoproduct B]
    (c₁ : Limits.Cofan A) (c₂ : Limits.Cofan B) (hc₁ : Limits.IsColimit c₁)
    (hc₂ : Limits.IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt) (ψ : ∀ b, A b ⟶ B b)
    (hsig : Mono (Limits.Sigma.map ψ))
    (hcomm : ∀ b, c₁.inj b ≫ φ = ψ b ≫ c₂.inj b) : Mono φ := by
  rw [cofanMap_eq_sigmaMap c₁ c₂ hc₁ hc₂ φ ψ hcomm]
  exact mono_comp _ _

/-- The family `Lᵖ ⊗ Yᵠ` (over `p + q = n`) whose coproduct is the degree-`n` part of the total
tensor product complex. -/
abbrev tensorObjFamily (X Y : GradedObject ℤ (ModuleCat.{u} R)) (n : ℤ) :
    {p : ℤ × ℤ // p.1 + p.2 = n} → ModuleCat R := fun ⟨⟨p, q⟩, _⟩ => X p ⊗ Y q

/-- The coproduct cofan exhibiting `tensorObj X Y n` as the direct sum `⊕_{p+q=n} Xᵖ ⊗ Yᵠ`. -/
noncomputable def tensorObjCofan (X Y : GradedObject ℤ (ModuleCat.{u} R))
    [X.HasTensor Y] (n : ℤ) : Limits.Cofan (tensorObjFamily X Y n) :=
  Limits.Cofan.mk (GradedObject.Monoidal.tensorObj X Y n)
    (fun ⟨⟨p, q⟩, hpq⟩ => GradedObject.Monoidal.ιTensorObj X Y p q n hpq)

/-- The inclusions of `tensorObjCofan` are the inclusions of the summands `Xᵖ ⊗ Yᵠ`. -/
@[simp] lemma tensorObjCofan_inj (X Y : GradedObject ℤ (ModuleCat.{u} R))
    [X.HasTensor Y] (n p q : ℤ) (hpq : p + q = n) :
    (tensorObjCofan X Y n).inj ⟨(p, q), hpq⟩
      = GradedObject.Monoidal.ιTensorObj X Y p q n hpq := rfl

/-- `tensorObjCofan` is a colimit cofan. -/
noncomputable def tensorObjCofanIsColimit (X Y : GradedObject ℤ (ModuleCat.{u} R))
    [X.HasTensor Y] (n : ℤ) : Limits.IsColimit (tensorObjCofan X Y n) :=
  Limits.Cofan.IsColimit.mk _
    (fun s => GradedObject.Monoidal.tensorObjDesc (fun i₁ i₂ hi => s.inj ⟨(i₁, i₂), hi⟩))
    (fun _ ⟨⟨_, _⟩, _⟩ => by rw [tensorObjCofan_inj, GradedObject.Monoidal.ι_tensorObjDesc])
    (fun s m hm => by
      apply GradedObject.Monoidal.tensorObj_ext
      intro i₁ i₂ hi
      rw [GradedObject.Monoidal.ι_tensorObjDesc]
      have := hm ⟨(i₁, i₂), hi⟩
      rwa [tensorObjCofan_inj] at this)

/-- The summandwise components `Lᵖ ◁ φᵠ` of `L ◁ φ` on the coproduct `⊕_{p+q=n}`. -/
abbrev whiskerFamily {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (φ : X ⟶ Y) (n : ℤ) :
    ∀ b : {p : ℤ × ℤ // p.1 + p.2 = n},
      tensorObjFamily L.X X.X n b ⟶ tensorObjFamily L.X Y.X n b :=
  fun ⟨⟨p, q⟩, _⟩ => (L.X p) ◁ (φ.f q)

/-- `(L ◁ φ).f n` acts on the summand indexed by `b` through `whiskerFamily L φ n b`. -/
theorem inj_comp_whiskerLeft {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (φ : X ⟶ Y) (n : ℤ)
    (b : {p : ℤ × ℤ // p.1 + p.2 = n}) :
    (tensorObjCofan L.X X.X n).inj b ≫ (L ◁ φ).f n
      = whiskerFamily L φ n b ≫ (tensorObjCofan L.X Y.X n).inj b := by
  obtain ⟨⟨p, q⟩, hpq⟩ := b
  rw [tensorObjCofan_inj, tensorObjCofan_inj]
  exact GradedObject.Monoidal.ι_tensorHom (𝟙 L.X) φ.f p q n hpq

/-- Applying `M ⊗ -` to the injection of a short exact sequence of modules keeps it mono, using
flatness of the right-hand term (Stacks Algebra 10.39.12). -/
theorem mono_whiskerLeft_of_flat (M : ModuleCat.{u} R) (T : ShortComplex (ModuleCat.{u} R))
    (hT : T.ShortExact) (hflat : Module.Flat R T.X₃) : Mono (M ◁ T.f) := by
  rw [ModuleCat.MonoidalCategory.whiskerLeft_def, ModuleCat.mono_iff_injective]
  have hf : Function.Injective T.f.hom := (ModuleCat.mono_iff_injective _).mp hT.mono_f
  have hg : Function.Surjective T.g.hom := (ModuleCat.epi_iff_surjective _).mp hT.epi_g
  have hexact : Function.Exact T.f.hom T.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact
  have : Module.Flat R T.X₃ := hflat
  exact LinearMap.lTensor_injective_of_exact_of_flat T.g.hom hg T.f.hom hf hexact M

/-- Degreewise monomorphism of the tensored injection `L ⊗ S.f`: assembling the summandwise
monos `Lᵖ ⊗ S.fᵠ` over the coproduct `⊕_{p+q=n}`. -/
@[ega "0 6.1.2" "partial",
  ega "0 6.7.4" "partial",
  ega "IV 2.1.8" "(i)",
  sga "1 IV 1.1" "(i)",
  sga "4 XVII 4.1.1" "(ii)"]
theorem tensor_f_mono (hse : S.ShortExact) (hflat : ∀ n : ℤ, Module.Flat R (S.X₃.X n)) (n : ℤ) :
    Mono ((L ◁ S.f).f n) := by
  have : ∀ b, Mono (whiskerFamily L S.f n b) := fun ⟨⟨p, q⟩, _⟩ =>
    mono_whiskerLeft_of_flat (L.X p)
      (S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q))
      (hse.map_of_exact _) (hflat q)
  exact cofanMap_mono (tensorObjCofan L.X S.X₁.X n) (tensorObjCofan L.X S.X₂.X n)
    (tensorObjCofanIsColimit L.X S.X₁.X n) (tensorObjCofanIsColimit L.X S.X₂.X n)
    ((L ◁ S.f).f n) (whiskerFamily L S.f n) inferInstance (inj_comp_whiskerLeft L S.f n)

/-! ### Degreewise assembly of the tensored short exact sequence

The complex-level route (using that `tensorLeft L` preserves finite colimits) is unavailable: the
`PreservesFiniteColimits (tensorLeft L)` instance in this environment is `sorryAx`-tainted. We
therefore prove `tensor_shortExact` through
`HomologicalComplex.shortExact_of_degreewise_shortExact`, assembling each degree from
coproduct-of-summand facts that stay inside `ModuleCat R`. -/

/-- Applying `M ⊗ -` to a surjection of modules keeps it epi (no flatness needed). -/
theorem epi_whiskerLeft {X Y : ModuleCat.{u} R} (M : ModuleCat.{u} R) (g : X ⟶ Y) [Epi g] :
    Epi (M ◁ g) := by
  rw [ModuleCat.MonoidalCategory.whiskerLeft_def, ModuleCat.epi_iff_surjective]
  exact LinearMap.lTensor_surjective M ((ModuleCat.epi_iff_surjective g).mp ‹Epi g›)

/-- A map between coproduct cofans given summandwise by epis is epi
(companion to `cofanMap_mono`). -/
theorem cofanMap_epi {C : Type*} [Category C] {β : Type*} {A B : β → C}
    [Limits.HasCoproduct A] [Limits.HasCoproduct B]
    (c₁ : Limits.Cofan A) (c₂ : Limits.Cofan B) (hc₁ : Limits.IsColimit c₁)
    (hc₂ : Limits.IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt) (ψ : ∀ b, A b ⟶ B b)
    (hsig : Epi (Limits.Sigma.map ψ))
    (hcomm : ∀ b, c₁.inj b ≫ φ = ψ b ≫ c₂.inj b) : Epi φ := by
  rw [cofanMap_eq_sigmaMap c₁ c₂ hc₁ hc₂ φ ψ hcomm]
  exact epi_comp _ _

/-- Degreewise epimorphism of the tensored surjection `L ⊗ S.g`, assembling `epi_whiskerLeft`
over the coproduct `⊕_{p+q=n}` (mirror of `tensor_f_mono`, using `cofanMap_epi` and the same
`ι_tensorHom` compatibility). -/
theorem tensor_g_epi (hse : S.ShortExact) (n : ℤ) :
    Epi ((L ◁ S.g).f n) := by
  have : ∀ b, Epi (whiskerFamily L S.g n b) := fun ⟨⟨p, q⟩, _⟩ =>
    have : Epi (S.g.f q) := (hse.map_of_exact
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q)).epi_g
    epi_whiskerLeft (L.X p) (S.g.f q)
  exact cofanMap_epi (tensorObjCofan L.X S.X₂.X n) (tensorObjCofan L.X S.X₃.X n)
    (tensorObjCofanIsColimit L.X S.X₂.X n) (tensorObjCofanIsColimit L.X S.X₃.X n)
    ((L ◁ S.g).f n) (whiskerFamily L S.g n) (Limits.Sigma.map_epi _)
    (inj_comp_whiskerLeft L S.g n)

/-- A family of exact sequences of modules induces an exact sequence of their direct sums. -/
theorem _root_.DirectSum.lmap_exact {R : Type*} [Ring R] {ι : Type*} {A B C : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
    [∀ i, Module R (A i)] [∀ i, Module R (B i)] [∀ i, Module R (C i)]
    (f : ∀ i, A i →ₗ[R] B i) (g : ∀ i, B i →ₗ[R] C i)
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  have hker : (fun i => LinearMap.ker (g i)) = fun i => LinearMap.range (f i) :=
    funext fun i => LinearMap.exact_iff.mp (h i)
  rw [LinearMap.exact_iff, DirectSum.ker_lmap, DirectSum.range_lmap, hker]

/-- A short complex of `ModuleCat R` whose three objects are colimit cofans, and whose two maps
act summandwise by `ψf, ψg` which are exact per summand, is exact. -/
theorem cofanMap_exact {β : Type} {A B C : β → ModuleCat.{u} R}
    (c₁ : Limits.Cofan A) (c₂ : Limits.Cofan B) (c₃ : Limits.Cofan C)
    (hc₁ : Limits.IsColimit c₁) (hc₂ : Limits.IsColimit c₂) (hc₃ : Limits.IsColimit c₃)
    (φf : c₁.pt ⟶ c₂.pt) (φg : c₂.pt ⟶ c₃.pt) (hfg : φf ≫ φg = 0)
    (ψf : ∀ b, A b ⟶ B b) (ψg : ∀ b, B b ⟶ C b)
    (hcommf : ∀ b, c₁.inj b ≫ φf = ψf b ≫ c₂.inj b)
    (hcommg : ∀ b, c₂.inj b ≫ φg = ψg b ≫ c₃.inj b)
    (hexact : ∀ b, Function.Exact (ψf b).hom (ψg b).hom) :
    (ShortComplex.mk φf φg hfg).Exact := by
  classical
  -- the DirectSum short complex
  have hzD : (ModuleCat.ofHom (DirectSum.lmap (fun b => (ψf b).hom))) ≫
      (ModuleCat.ofHom (DirectSum.lmap (fun b => (ψg b).hom))) = 0 := by
    have hcz : ∀ i, (ψg i).hom ∘ₗ (ψf i).hom = 0 := by
      intro i
      ext z
      simp only [LinearMap.comp_apply, LinearMap.zero_apply]
      have hmem : (ψf i).hom z ∈ LinearMap.range (ψf i).hom := ⟨z, rfl⟩
      rw [← (LinearMap.exact_iff.mp (hexact i))] at hmem
      rw [LinearMap.mem_ker] at hmem
      simpa using hmem
    rw [← ModuleCat.ofHom_comp]
    rw [show (DirectSum.lmap (fun b => (ψg b).hom)) ∘ₗ (DirectSum.lmap (fun b => (ψf b).hom))
        = DirectSum.lmap (fun i => (ψg i).hom ∘ₗ (ψf i).hom) from
      (DirectSum.lmap_comp (fun b => (ψf b).hom) (fun b => (ψg b).hom)).symm]
    rw [show (fun i => (ψg i).hom ∘ₗ (ψf i).hom) = (fun _ => (0 : _ →ₗ[R] _)) from funext hcz]
    ext x
    simp
  set D : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (ModuleCat.ofHom (DirectSum.lmap (fun b => (ψf b).hom)))
      (ModuleCat.ofHom (DirectSum.lmap (fun b => (ψg b).hom))) hzD
  have hDexact : D.Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    change Function.Exact (DirectSum.lmap (fun b => (ψf b).hom)) (DirectSum.lmap (fun b => (ψg
        b).hom))
    exact DirectSum.lmap_exact (fun b => (ψf b).hom) (fun b => (ψg b).hom) hexact
  -- the canonical iso `c.pt ≅ ⨁ B` commutes with the summandwise maps
  have sq : ∀ {A B : β → ModuleCat.{u} R} (c₁ : Limits.Cofan A) (c₂ : Limits.Cofan B)
      (hc₁ : Limits.IsColimit c₁) (hc₂ : Limits.IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt)
      (ψ : ∀ b, A b ⟶ B b) (hcomm : ∀ b, c₁.inj b ≫ φ = ψ b ≫ c₂.inj b),
      ((hc₁.coconePointUniqueUpToIso (Limits.coproductIsCoproduct A)) ≪≫
        (ModuleCat.coprodIsoDirectSum A)).hom ≫ ModuleCat.ofHom (DirectSum.lmap fun b => (ψ b).hom)
      = φ ≫ ((hc₂.coconePointUniqueUpToIso (Limits.coproductIsCoproduct B)) ≪≫
        (ModuleCat.coprodIsoDirectSum B)).hom := by
    intro A B c₁ c₂ hc₁ hc₂ φ ψ hcomm
    have key : ∀ {A : β → ModuleCat.{u} R} (c : Limits.Cofan A) (hc : Limits.IsColimit c) (b : β),
        c.inj b ≫ ((hc.coconePointUniqueUpToIso (Limits.coproductIsCoproduct A)) ≪≫
          (ModuleCat.coprodIsoDirectSum A)).hom
        = ModuleCat.ofHom (DirectSum.lof R β (fun i => ↥(A i)) b) := by
      intro A c hc b
      change c.inj b ≫ ((hc.coconePointUniqueUpToIso _).hom ≫ _) = _
      rw [← Category.assoc, show c.inj b ≫ _ = Limits.Sigma.ι A b from
        hc.comp_coconePointUniqueUpToIso_hom (Limits.coproductIsCoproduct A) ⟨b⟩,
        ModuleCat.ι_coprodIsoDirectSum_hom A b]
    refine Limits.Cofan.IsColimit.hom_ext hc₁ _ _ fun b => ?_
    rw [← Category.assoc, key c₁ hc₁ b, ← Category.assoc, hcomm b, Category.assoc, key c₂ hc₂ b,
      ← ModuleCat.ofHom_comp]
    ext z
    simp [DirectSum.lof_eq_of]
  -- assemble iso of short complexes
  have e : (ShortComplex.mk φf φg hfg) ≅ D :=
    ShortComplex.isoMk
      ((hc₁.coconePointUniqueUpToIso (Limits.coproductIsCoproduct A)) ≪≫
        (ModuleCat.coprodIsoDirectSum A))
      ((hc₂.coconePointUniqueUpToIso (Limits.coproductIsCoproduct B)) ≪≫
        (ModuleCat.coprodIsoDirectSum B))
      ((hc₃.coconePointUniqueUpToIso (Limits.coproductIsCoproduct C)) ≪≫
        (ModuleCat.coprodIsoDirectSum C))
      (sq c₁ c₂ hc₁ hc₂ φf ψf hcommf) (sq c₂ c₃ hc₂ hc₃ φg ψg hcommg)
  exact ShortComplex.exact_of_iso e.symm hDexact

/-- The composite of the two summand whiskerings vanishes (degreewise `g ∘ f = 0`). -/
theorem summand_comp_zero (p q : ℤ) :
    ((L.X p) ◁ (S.f.f q)) ≫ ((L.X p) ◁ (S.g.f q)) = 0 := by
  have hsg : S.f.f q ≫ S.g.f q = 0 := by
    rw [← HomologicalComplex.comp_f, S.zero, HomologicalComplex.zero_f]
  rw [← MonoidalCategory.whiskerLeft_comp, hsg]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_whiskerLeft, ModuleCat.hom_zero, LinearMap.lTensor_zero, ModuleCat.hom_zero]

/-- The whiskering `L ◁ -` sends the zero chain map to zero (proved degreewise inside `ModuleCat`,
avoiding the `sorryAx`-tainted complex-level `PreservesZeroMorphisms` instance). -/
theorem whiskerLeft_zero_cochainComplex (X Y : CochainComplex (ModuleCat.{u} R) ℤ) :
    (L ◁ (0 : X ⟶ Y)) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Limits.Cofan.IsColimit.hom_ext (tensorObjCofanIsColimit L.X X.X n)
  rintro ⟨⟨p, q⟩, hpq⟩
  rw [HomologicalComplex.zero_f, Limits.comp_zero,
    inj_comp_whiskerLeft L (0 : X ⟶ Y) n ⟨(p, q), hpq⟩,
    show whiskerFamily L (0 : X ⟶ Y) n ⟨(p, q), hpq⟩ = 0 from by simp [whiskerFamily],
    Limits.zero_comp]

/-- A clean `PreservesZeroMorphisms` instance for `tensorLeft L`, given high priority so it
overrides the `sorryAx`-tainted environment instance when elaborating `S.map (tensorLeft L)`. -/
instance (priority := 10000) tensorLeftPreservesZeroMorphisms :
    (MonoidalCategory.tensorLeft L).PreservesZeroMorphisms where
  map_zero X Y := whiskerLeft_zero_cochainComplex L X Y

/-- Degreewise exactness in the middle of the evaluated tensored short complex: single-summand
exactness from right-exactness of tensoring (no flatness needed), assembled over the coproduct
`⊕_{p+q=n}`. -/
@[sga "7 VII 3.7.6" "partial"]
theorem tensor_exact_at (hse : S.ShortExact) (n : ℤ) :
    ((S.map (MonoidalCategory.tensorLeft L)).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).Exact := by
  -- per-summand exactness via right-exactness of tensoring (no flatness)
  have hexact : ∀ b, Function.Exact (whiskerFamily L S.f n b).hom
      (whiskerFamily L S.g n b).hom := by
    rintro ⟨⟨p, q⟩, hpq⟩
    have hSESq :
        (S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q)).ShortExact :=
      hse.map_of_exact _
    have hg : Function.Surjective (S.g.f q).hom :=
      (ModuleCat.epi_iff_surjective _).mp hSESq.epi_g
    have hExFun : Function.Exact (S.f.f q).hom (S.g.f q).hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q))).mp hSESq.exact
    have hlt : Function.Exact ((S.f.f q).hom.lTensor (L.X p))
        ((S.g.f q).hom.lTensor (L.X p)) := lTensor_exact (L.X p) hExFun hg
    rwa [ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerLeft]
  -- the zero condition, proved summandwise (avoiding the sorryAx-tainted complex-level instance)
  have hfg : (L ◁ S.f).f n ≫ (L ◁ S.g).f n = 0 := by
    apply Limits.Cofan.IsColimit.hom_ext (tensorObjCofanIsColimit L.X S.X₁.X n)
    rintro ⟨⟨p, q⟩, hpq⟩
    rw [Limits.comp_zero, ← Category.assoc, inj_comp_whiskerLeft L S.f n, Category.assoc,
      inj_comp_whiskerLeft L S.g n, ← Category.assoc, summand_comp_zero L S p q,
      Limits.zero_comp]
  exact cofanMap_exact (tensorObjCofan L.X S.X₁.X n) (tensorObjCofan L.X S.X₂.X n)
    (tensorObjCofan L.X S.X₃.X n) (tensorObjCofanIsColimit L.X S.X₁.X n)
    (tensorObjCofanIsColimit L.X S.X₂.X n) (tensorObjCofanIsColimit L.X S.X₃.X n)
    ((L ◁ S.f).f n) ((L ◁ S.g).f n) hfg (whiskerFamily L S.f n) (whiskerFamily L S.g n)
    (inj_comp_whiskerLeft L S.f n) (inj_comp_whiskerLeft L S.g n) hexact

/-- The degree-`n` evaluated short complex of `S.map (tensorLeft L)` is short exact, packaged from
the mono/epi/exact pieces via `ShortComplex.ShortExact.mk`. -/
@[ega "0 6.7.4" "partial, special case",
  ega "IV 2.1.8" "(i), special case",
  sga "1 IV 1.1" "more general",
  sga "4 XVII 4.1.1" "(ii), special case"]
theorem degreewise_shortExact (hse : S.ShortExact)
    (hflat : ∀ n : ℤ, Module.Flat R (S.X₃.X n)) (n : ℤ) :
    ((S.map (MonoidalCategory.tensorLeft L)).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).ShortExact := by
  have : Mono ((S.map (MonoidalCategory.tensorLeft L)).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).f := by
    change Mono ((L ◁ S.f).f n)
    exact tensor_f_mono L S hse hflat n
  have : Epi ((S.map (MonoidalCategory.tensorLeft L)).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).g := by
    change Epi ((L ◁ S.g).f n)
    exact tensor_g_epi L S hse n
  exact ShortComplex.ShortExact.mk (tensor_exact_at L S hse n)

/-- If `0 → X₁ → X₂ → X₃ → 0` is a short exact sequence of complexes of `R`-modules with `X₃`
termwise flat, then tensoring on the left with any complex `L` gives a short exact sequence. -/
@[ega "0 6.1.2" "more general", ega "IV 2.1.8" "(i), special case", sga "1 IV 1.1" "more general"]
theorem tensor_shortExact (hse : S.ShortExact) (hflat : ∀ n : ℤ, Module.Flat R (S.X₃.X n)) :
    (S.map (MonoidalCategory.tensorLeft L)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (degreewise_shortExact L S hse hflat)

/-- **(SG-C, "X₁ from X₂, X₃".)** In a short exact sequence of complexes
`0 → A → B → C → 0`, if `B` and `C` are acyclic then so is `A`.
Proof: long exact homology sequence — `homology_exact₁` at the predecessor degree
`j-1 → j` gives exactness `H^{j-1}(C) → H^j(A) → H^j(B)`; both ends vanish, so
`H^j(A) = 0` by `ShortComplex.Exact.isZero_X₂`. -/
theorem acyclic_X₁_of_acyclic_X₂_X₃ (T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hT : T.ShortExact) (h2 : T.X₂.Acyclic) (h3 : T.X₃.Acyclic) : T.X₁.Acyclic := by
  intro j
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hij : (ComplexShape.up ℤ).Rel (j - 1) j := by simp [ComplexShape.up_Rel]
  exact (hT.homology_exact₁ (j - 1) j hij).isZero_X₂
    ((h3 (j - 1)).isZero_homology.eq_of_src _ _) ((h2 j).isZero_homology.eq_of_tgt _ _)

/-- **(SG-C, "X₃ from X₁, X₂".)** In a short exact sequence of complexes
`0 → A → B → C → 0`, if `A` and `B` are acyclic then so is `C`.
Proof: `homology_exact₃` at degree `i → i+1` gives exactness
`H^i(B) → H^i(C) → H^{i+1}(A)`; both ends vanish, so `H^i(C) = 0`. -/
theorem acyclic_X₃_of_acyclic_X₁_X₂ (T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hT : T.ShortExact) (h1 : T.X₁.Acyclic) (h2 : T.X₂.Acyclic) : T.X₃.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hij : (ComplexShape.up ℤ).Rel i (i + 1) := by simp [ComplexShape.up_Rel]
  exact (hT.homology_exact₃ i (i + 1) hij).isZero_X₂
    ((h2 i).isZero_homology.eq_of_src _ _) ((h1 (i + 1)).isZero_homology.eq_of_tgt _ _)

/-! ### Main statements -/

/-- (1) If `K₁ = S.X₁` and `K₂ = S.X₂` are K-flat, then `K₃ = S.X₃` is K-flat.

Take arbitrary acyclic `L`. Form `T := S.map (tensorLeft L)`, the SES of total
complexes `0 → L⊗K₁ → L⊗K₂ → L⊗K₃ → 0` (`tensor_shortExact`). Its `X₁ = L⊗K₁` and
`X₂ = L⊗K₂` are acyclic by K-flatness of `K₁, K₂`. By
`acyclic_X₃_of_acyclic_X₁_X₂`, `X₃ = L⊗K₃` is acyclic; i.e. `K₃` is K-flat. -/
theorem kFlat_X₃ (hse : S.ShortExact)
    (hflat : ∀ n : ℤ, Module.Flat R (S.X₃.X n)) (h1 : CochainComplex.KFlat S.X₁)
    (h2 : CochainComplex.KFlat S.X₂) : CochainComplex.KFlat S.X₃ := by
  intro L hL
  exact acyclic_X₃_of_acyclic_X₁_X₂ (S.map (MonoidalCategory.tensorLeft L))
    (tensor_shortExact L S hse hflat) (h1 L hL) (h2 L hL)

/-- (2) If `K₁ = S.X₁` and `K₃ = S.X₃` are K-flat, then `K₂ = S.X₂` is K-flat.

As above, with Mathlib's `ShortComplex.ShortExact.acyclic_X₂`: `X₁ = L⊗K₁`,
`X₃ = L⊗K₃` acyclic ⟹ `X₂ = L⊗K₂` acyclic. -/
theorem kFlat_X₂ (hse : S.ShortExact)
    (hflat : ∀ n : ℤ, Module.Flat R (S.X₃.X n)) (h1 : CochainComplex.KFlat S.X₁)
    (h3 : CochainComplex.KFlat S.X₃) : CochainComplex.KFlat S.X₂ := by
  intro L hL
  exact (tensor_shortExact L S hse hflat).acyclic_X₂ (h1 L hL) (h3 L hL)

/-- (3) If `K₂ = S.X₂` and `K₃ = S.X₃` are K-flat, then `K₁ = S.X₁` is K-flat.

As above, with `acyclic_X₁_of_acyclic_X₂_X₃`: `X₂ = L⊗K₂`, `X₃ = L⊗K₃`
acyclic ⟹ `X₁ = L⊗K₁` acyclic. -/
theorem kFlat_X₁ (hse : S.ShortExact)
    (hflat : ∀ n : ℤ, Module.Flat R (S.X₃.X n)) (h2 : CochainComplex.KFlat S.X₂)
    (h3 : CochainComplex.KFlat S.X₃) : CochainComplex.KFlat S.X₁ := by
  intro L hL
  exact acyclic_X₁_of_acyclic_X₂_X₃ (S.map (MonoidalCategory.tensorLeft L))
    (tensor_shortExact L S hse hflat) (h2 L hL) (h3 L hL)

/-- Two-out-of-three for K-flatness (Stacks Tag 0BYH, Lemma 15.60.6).
Given a short exact sequence of complexes `0 → K₁ → K₂ → K₃ → 0` with every
`K₃^n` flat, if at least two of `K₁, K₂, K₃` are K-flat, then all three are.

Case analysis on the disjunction `h`, completing the missing third K-flatness via
the corresponding directional lemma. -/
@[stacks 0BYH]
theorem kFlat_two_out_of_three {R : Type u} [CommRing R] (S : ShortComplex (Cx R))
    (hse : S.ShortExact) (hflat : ∀ n : ℤ, Module.Flat R (S.X₃.X n))
    (h : (CochainComplex.KFlat S.X₁ ∧ CochainComplex.KFlat S.X₂) ∨
          (CochainComplex.KFlat S.X₁ ∧ CochainComplex.KFlat S.X₃) ∨
          (CochainComplex.KFlat S.X₂ ∧ CochainComplex.KFlat S.X₃)) :
    CochainComplex.KFlat S.X₁ ∧ CochainComplex.KFlat S.X₂ ∧ CochainComplex.KFlat S.X₃ := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩
  · exact ⟨h1, h2, kFlat_X₃ S hse hflat h1 h2⟩
  · exact ⟨h1, kFlat_X₂ S hse hflat h1 h3, h3⟩
  · exact ⟨kFlat_X₁ S hse hflat h2 h3, h2, h3⟩

end KFlatTwoOutOfThree

-- ===== merged from StacksDraft.Sec59.Tag0795 =====


/-
# Problem Description

Fix a commutative ring `R`. All complexes are cochain complexes of `R`-modules,
indexed by `ℤ`, with differentials raising degree by `1`.

We work with the following notions:

* (Definition 1, Tensor product double complex) For complexes `X`, `Y` of
  `R`-modules, their tensor product double complex has `K^{p,q} = X^p ⊗_R Y^q`,
  horizontal differential `d_X ⊗ id` and vertical differential `id ⊗ d_Y`.
  (Stacks Homology, Example 12.18.2, tag 0A5J.)

* (Definition 2, Total complex `Tot`) For a double complex `A^{•,•}` the
  associated total complex has `Totⁿ = ⨁_{p+q=n} A^{p,q}` and differential
  `dⁿ = Σ_{p+q=n} (d₁^{p,q} + (-1)^p d₂^{p,q})`.
  (Stacks Homology, Definition 12.18.3, tag 012Z.)

  We write `Tot(X ⊗_R Y)` for the total complex of the tensor product double
  complex of `X` and `Y`. Concretely
  `Totⁿ(X ⊗_R Y) = ⨁_{p+q=n} X^p ⊗_R Y^q`, with differential on the summand
  `X^p ⊗_R Y^q` sending `x ⊗ y ↦ d_X x ⊗ y + (-1)^p x ⊗ d_Y y`.

* (Definition 3, Acyclic complex) A complex `M` is acyclic if all of its
  cohomology modules vanish, i.e. it is exact at every degree. This is Mathlib's
  `HomologicalComplex.Acyclic`.

* (Definition 4, K-flat complex) A complex `K` is K-flat if for every acyclic
  complex `M` the total complex `Tot(M ⊗_R K)` is acyclic.
  (Stacks More on Algebra, Definition 15.60.1, tag 06XZ.) This is
  `CochainComplex.KFlat`.

# Main Statement

(Stacks tag 0795, Lemma 15.60.4.) If `K` and `L` are K-flat complexes of
`R`-modules, then `Tot(K ⊗_R L)` is a K-flat complex of `R`-modules.

# Formalization notes

We model cochain complexes of `R`-modules as `CochainComplex (ModuleCat R) ℤ`,
i.e. `HomologicalComplex (ModuleCat R) (ComplexShape.up ℤ)`.

Mathlib equips `CochainComplex (ModuleCat R) ℤ` with a symmetric monoidal
structure whose tensor product `X ⊗ Y` is, by definition, the total complex of
the tensor product double complex of `X` and `Y` (using the standard Koszul sign
convention `(-1)^p` matching Stacks Definition 12.18.3). Thus the monoidal
tensor product `X ⊗ Y` *is* `Tot(X ⊗_R Y)` in the notation of the problem.

The associativity isomorphism used in the Stacks proof is provided by the
associator of this monoidal structure.

The ring `R` lives in an arbitrary universe `u`, as in Stacks. Mathlib's
`MonoidalCategory (ModuleCat.{u} R)` instance requires the module universe to
agree with the universe of `R`, so `ModuleCat R` here means `ModuleCat.{u} R`;
this is the same convention as `StacksFrontier.Algebra.Homology.KFlat`.
-/

variable (R : Type u) [CommRing R]

/-! ### Main statements -/

/-- (Stacks tag 0795, Lemma 15.60.4) If `K` and `L` are K-flat complexes of
`R`-modules, then `Tot(K ⊗_R L)` (i.e. the monoidal tensor product `K ⊗ L`) is
K-flat.

For acyclic `M`, K-flatness of `K` makes `M ⊗ K` acyclic, then K-flatness of `L`
makes `(M ⊗ K) ⊗ L` acyclic, and acyclicity transfers to `M ⊗ (K ⊗ L)` across the
associator. -/
@[stacks 0795]
theorem CochainComplex.KFlat.tensor (K L : CochainComplex (ModuleCat R) ℤ)
    (hK : K.KFlat) (hL : L.KFlat) : (K ⊗ L).KFlat := by
  intro M hM
  exact HomologicalComplex.Acyclic.of_iso (α_ M K L) (hL (M ⊗ K) (hK M hM))
