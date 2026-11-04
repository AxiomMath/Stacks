module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Homology.TorAmplitude.Defs
public import StacksFrontier.Homology.TorAmplitude.Termwise
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

-- The mixed-universe tensor functor is built directly out of `TensorProduct`, so recognizing its
-- action on a sum of morphisms means seeing through `ModuleCat.ofHom`; this needs the pre-4.x
-- defeq transparency behaviour.
set_option backward.isDefEq.respectTransparency false

/-!
# Termwise Tor amplitude with independent ring and module universes

Let `R` be a ring. For a cochain complex `K` of `R`-modules and a single `R`-module `M`, the
termwise tensor product `K ⊗ M` computes the derived tensor product `K ⊗^L M` as soon as `K` is a
bounded above complex of flat modules. This module records that termwise construction and the
resulting Tor-amplitude condition in the form that allows the carrier universe of the modules to
be independent of the universe of the ring, and proves that Tor amplitude in `[a, b]` forces the
cokernel of the differential `K^{a-1} → K^a` to be flat.

## Main definitions

* `StacksDraft.TorAmplitude.tensorRightMixed`: tensoring by a module whose carrier universe is
  unrelated to that of its argument.
* `StacksDraft.TorAmplitude.tensorComplex`: the termwise tensor product `K ⊗ M`.
* `StacksDraft.TorAmplitude.BoundedAbove`: vanishing of a complex in all large degrees.
* `StacksDraft.TorAmplitude.IsComplexOfFlats`: termwise flatness of a complex.
* `StacksDraft.TorAmplitude.HasTorAmplitudeIn`: vanishing of `Hⁱ(K ⊗ M)` outside `[a, b]`, for
  every test module in a universe containing both the ring and the carriers of `K`.

## Main results

* `StacksDraft.TorAmplitude.cokernel_flat_of_termwise_torAmplitude`: a complex of flat modules
  with termwise Tor amplitude in `[a, b]` has flat cokernel in degree `a`.

## Implementation notes

Mathlib's monoidal structure on `ModuleCat` requires the modules and the ring to share a universe,
so tensoring a module of `ModuleCat.{v} R` with a module of `ModuleCat.{w} R` is implemented
directly as `TensorProduct`, valued in `ModuleCat.{max v w} R`; this is `tensorRightMixed`.
The test modules in `HasTorAmplitudeIn` range over `ModuleCat.{max u v} R`, which is large enough
to contain both the ring and the carriers of `K`, and therefore large enough to contain the
quotients used by Mathlib's flatness criterion.

Mathlib has no usable `Tor` API, so the classical argument "Tor amplitude in `[a, b]` gives
`Tor₁(Coker d^{a-1}, M) = 0` for all `M`, hence flatness" is reformulated as injectivity of
tensored maps: exactness of `K^{a-2} ⊗ M → K^{a-1} ⊗ M → K^a ⊗ M` gives injectivity of
`(Im d^{a-1}) ⊗ M → K^a ⊗ M`, and a four-lemma chase upgrades that to flatness of the quotient.

This module carries the content of Stacks tag 0653, whose tag is attached to
another module of the library and not here.
-/

open CategoryTheory MonoidalCategory Limits

namespace StacksDraft.TorAmplitude

universe u v w

variable {R : Type u} [CommRing R]

/-- Tensoring a module in one universe with a fixed module in another universe. -/
def tensorRightMixed (M : ModuleCat.{w} R) :
    ModuleCat.{v} R ⥤ ModuleCat.{max v w} R where
  obj X := ModuleCat.of R (TensorProduct R (X : Type v) (M : Type w))
  map f := ModuleCat.ofHom (f.hom.rTensor M)
  map_id := by
    intro X
    ext
    simp [ModuleCat.hom_id, LinearMap.rTensor_id]
  map_comp := by
    intro X Y Z f g
    ext
    simp [ModuleCat.hom_comp, LinearMap.rTensor_comp]

/-- The functor `tensorRightMixed M`, given by `X ↦ X ⊗[R] M`, is additive. -/
instance tensorRightMixed_additive (M : ModuleCat.{w} R) : (tensorRightMixed M).Additive where
  map_add := by
    intro X Y f g
    ext
    simp [tensorRightMixed, ModuleCat.hom_add, LinearMap.rTensor_add]

/-- The termwise derived tensor product of a bounded above complex of flat modules
`K` with a module `M`: the complex with terms `K^n ⊗ M` and differentials
`d_K^n ⊗ id`. For a bounded above complex of flat modules this represents
`K ⊗^L M`. -/
noncomputable def tensorComplex (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (M : ModuleCat.{w} R) : CochainComplex (ModuleCat.{max v w} R) ℤ :=
  ((tensorRightMixed M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- A cochain complex `K` is a *complex of flat `R`-modules* if `K^n` is a flat
`R`-module for every `n`. -/
def IsComplexOfFlats (K : CochainComplex (ModuleCat.{v} R) ℤ) : Prop :=
  ∀ n : ℤ, Module.Flat R (K.X n)

/-- The auxiliary termwise Tor-amplitude condition: `H^i(K ⊗ M) = 0` outside
`[a, b]` for every test module `M`. For a bounded above complex of flat modules,
the comparison below derives this from certified derived Tor-amplitude. -/
def HasTorAmplitudeIn (K : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ) : Prop :=
  ∀ (M : ModuleCat.{max u v} R) (i : ℤ), (i < a ∨ b < i) →
    IsZero ((tensorComplex K M).homology i)

/-- Let `g : B →ₗ D` with the *codomain* `D` flat, `Z := range g ⊆ D`, and suppose that for
*every* module `M` the inclusion `Z ↪ D` induces an injection `Z⊗M → D⊗M`
(`rTensor M Z.subtype` injective). Then the cokernel
`coker g = D ⧸ range g` is flat. This is the Tor-free form of: from the SES
`0 → Z → D → D/Z → 0` with `D` flat, `D/Z` is flat iff `Z⊗M → D⊗M` is injective for
all `M` (Stacks Tag 00M5).

Note: `hinj` is quantified over `M : Type (max u w)`. In Lean a hypothesis
`∀ (M : Type*), …` introduces a *single fixed* universe parameter, which cannot be
applied at the universe `max u w` that the flatness criterion's test module
`N' ⧸ range α` lives in. We therefore pin `hinj`'s universe to exactly `max u w`
(`u`, `w` = universes of `R`, `D`). This helper_0653 lemma is declared with its own local
universe parameters `{u, v, w}` so that it does not perturb the protected declarations'
auto-bound universe signatures. -/
private theorem flat_quotient_range_of_rTensor_subtype_injective
    {R : Type u} [CommRing R]
    {B : Type v} {D : Type w} [AddCommGroup B] [AddCommGroup D]
    [Module R B] [Module R D] (g : B →ₗ[R] D) [Module.Flat R D]
    (hinj : ∀ (M : Type (max u w)) [AddCommGroup M] [Module R M],
      Function.Injective (LinearMap.rTensor M (LinearMap.range g).subtype)) :
    Module.Flat R (D ⧸ LinearMap.range g) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ α hα
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (LinearMap.exact_subtype_mkQ (LinearMap.range g))
    (Submodule.mkQ_surjective (LinearMap.range g))
    (LinearMap.exact_map_mkQ_range α)
    (Submodule.mkQ_surjective (LinearMap.range α))
    (hinj (N' ⧸ LinearMap.range α))
    (Module.Flat.lTensor_preserves_injective_linearMap α hα)

-- Flat-cokernel argument for the auxiliary termwise condition.

/-- If the terms of `K` are flat and all termwise tensor products have vanishing
homology outside `[a, b]`, then the cokernel of `d_K^(a-1)` is flat. This version
works with independent ring and module universes and does not need boundedness. -/
theorem cokernel_flat_of_termwise_torAmplitude
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ)
    (hflat : IsComplexOfFlats K)
    (htor : HasTorAmplitudeIn K a b) :
    Module.Flat R (cokernel (K.d (a - 1) a) : ModuleCat.{v} R) := by
  -- Abbreviations: `g := (K.d (a-1) a).hom`, `f := (K.d (a-2) (a-1)).hom`.
  set g : (K.X (a - 1) : Type _) →ₗ[R] (K.X a : Type _) := (K.d (a - 1) a).hom with hg
  -- `K^a` is flat (from `hflat`).
  have hKa : Module.Flat R (K.X a : Type _) := hflat a
  -- S1: for every module `M`, the tensored sequence is exact in the middle, i.e.
  -- `Function.Exact (rTensor M (K.d (a-2) (a-1)).hom) (rTensor M g)`.
  -- From `htor _ (a-1) (Or.inl (by omega))`, `exactAt_iff_isZero_homology`,
  -- `HomologicalComplex.exactAt_iff`, the `shortComplexFunctor` accessors
  -- (`prev (a-1) = a-2`, `next (a-1) = a`), `Functor.mapHomologicalComplex_obj_d`,
  -- `ModuleCat.hom_whiskerRight` (= `rTensor`), and
  -- `ShortExact.moduleCat_exact_iff_function_exact`.
  -- (S1 is a definitional/categorical unfolding of the hypothesis `htor`; no
  --  independent mathematical content, so no separate counterexample risk.)
  -- S3 ⟹ for every `M`, `rTensor M (range g).subtype` is injective.
  -- (Apply `Termwise.rTensor_range_subtype_injective_of_exact` with the S1 exactness and
  --  `(K.d (a-1) a).hom ∘ₗ (K.d (a-2) (a-1)).hom = 0`, i.e.
  --  `(K.d (a-2) (a-1) ≫ K.d (a-1) a).hom = 0` from `K.d_comp_d` + `ModuleCat.hom_zero`.)
  have hinj : ∀ (M : Type _) [AddCommGroup M] [Module R M],
      Function.Injective (LinearMap.rTensor M (LinearMap.range g).subtype) := by
    intro M _ _
    have hz := htor (ModuleCat.of R M) (a - 1) (Or.inl (by omega))
    have hexactAt : (tensorComplex K (ModuleCat.of R M)).ExactAt (a - 1) := by
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact hz
    rw [HomologicalComplex.exactAt_iff] at hexactAt
    rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hexactAt
    -- `hexactAt : Function.Exact (hom S.f) (hom S.g)` where
    -- `S.f = (tensorComplex K M).d (prev (a-1)) (a-1)` and
    -- `S.g = (tensorComplex K M).d (a-1) (next (a-1))`, and the underlying linear
    -- maps are the corresponding `rTensor`s (definitionally).
    change Function.Exact
        (LinearMap.rTensor M (K.d ((ComplexShape.up ℤ).prev (a - 1)) (a - 1)).hom)
        (LinearMap.rTensor M (K.d (a - 1) ((ComplexShape.up ℤ).next (a - 1))).hom)
      at hexactAt
    have key : Function.Exact
        (LinearMap.rTensor M (K.d ((ComplexShape.up ℤ).prev (a - 1)) (a - 1)).hom)
        (LinearMap.rTensor M (K.d (a - 1) ((ComplexShape.up ℤ).next (a - 1))).hom) := hexactAt
    have hnext : ((ComplexShape.up ℤ).next (a - 1)) = a := by rw [CochainComplex.next]; ring
    rw [hnext] at key
    refine Termwise.rTensor_range_subtype_injective_of_exact
      (K.d ((ComplexShape.up ℤ).prev (a - 1)) (a - 1)).hom g ?_ M key
    -- `g ∘ₗ (K.d (prev (a-1)) (a-1)).hom = 0` from `d_comp_d`.
    have hdd := K.d_comp_d ((ComplexShape.up ℤ).prev (a - 1)) (a - 1) a
    rw [hg, ← ModuleCat.hom_comp, hdd, ModuleCat.hom_zero]
  -- S4 ⟹ `(K.X a) ⧸ range g` is flat.
  have hflatQ : Module.Flat R ((K.X a : Type _) ⧸ LinearMap.range g) :=
    flat_quotient_range_of_rTensor_subtype_injective g hinj
  -- Bridge: `cokernel (K.d (a-1) a) ≅ ModuleCat.of R ((K.X a) ⧸ range g)`,
  -- transport flatness via `Module.Flat.of_linearEquiv` /
  -- `ModuleCat.cokernelIsoRangeQuotient` (its `toLinearEquiv`).
  exact Module.Flat.of_linearEquiv
    (ModuleCat.cokernelIsoRangeQuotient (K.d (a - 1) a)).toLinearEquiv

/-! ### Flatness of a submodule with flat quotient -/

/-- If `0 → A → B → Q → 0` is exact with `Q` flat, then `A ⊗ N → B ⊗ N` is injective for all `N`. -/
private theorem rTensor_injective_of_exact_of_flat_quotient
    {A B Q : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup Q] [Module R Q] [Module.Flat R Q]
    (i : A →ₗ[R] B) (hi : Function.Injective i) (p : B →ₗ[R] Q)
    (hp : Function.Surjective p) (hexact : Function.Exact i p)
    (N : Type*) [AddCommGroup N] [Module R N] :
    Function.Injective (LinearMap.rTensor N i) :=
  (i.lTensor_inj_iff_rTensor_inj N).1
    (LinearMap.lTensor_injective_of_exact_of_flat p hp i hi hexact N)

/-- In a short exact sequence `0 → A → B → Q → 0` of `R`-modules with `B` and `Q` both flat, the
submodule `A` is flat too. Because `Q` is flat, `A` is pure in `B`, so `A ⊗ N → B ⊗ N` is injective
for every `N`; composing the injection `A ⊗ N' → B ⊗ N'` with `A ⊗ α` for an injection
`α : N → N'` therefore gives the same map as the injection `A ⊗ N → B ⊗ N` followed by the
injection `B ⊗ α`, and injectivity of `A ⊗ α` follows. -/
private theorem flat_of_flat_of_flat_quotient
    {A B Q : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup Q] [Module R Q] [Module.Flat R B] [Module.Flat R Q]
    (i : A →ₗ[R] B) (hi : Function.Injective i) (p : B →ₗ[R] Q)
    (hp : Function.Surjective p) (hexact : Function.Exact i p) :
    Module.Flat R A := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ α hα
  have hiN := rTensor_injective_of_exact_of_flat_quotient i hi p hp hexact N
  have hαB : Function.Injective (LinearMap.lTensor B α) :=
    Module.Flat.lTensor_preserves_injective_linearMap α hα
  have hmap : Function.Injective (TensorProduct.map i α) := by
    rw [← LinearMap.lTensor_comp_rTensor]
    exact hαB.comp hiN
  rw [← LinearMap.rTensor_comp_lTensor] at hmap
  exact Function.Injective.of_comp hmap

/-! ### Acyclicity is preserved by termwise tensoring -/

/-- **A bounded above acyclic complex of flat modules stays acyclic after termwise tensoring.**
This is the flat analogue of K-projectivity, and it is the only input needed to compare the
termwise tensor product of two representatives of the same object of the derived category.

The proof splits `C` into the short exact sequences `0 → Zⁿ → Cⁿ → Zⁿ⁺¹ → 0` of cocycles, which
are exact precisely because `C` is acyclic. Descending induction from the degree above which `C`
vanishes makes every `Zⁿ` flat, so every `Zⁿ` is pure in `Cⁿ`; right exactness of the tensor
product then identifies the kernel of `Cⁿ⁺¹ ⊗ M → Cⁿ⁺² ⊗ M` with the image of
`Zⁿ⁺¹ ⊗ M → Cⁿ⁺¹ ⊗ M`, which is the image of `Cⁿ ⊗ M → Cⁿ⁺¹ ⊗ M`. -/
@[ega "IV 2.1.10" "special case", sga "4 V 1.2" "special case"]
theorem isZero_homology_tensorComplex_of_acyclic
    (C : CochainComplex (ModuleCat.{v} R) ℤ) (d : ℤ) (hd : C.IsStrictlyLE d)
    (hflat : IsComplexOfFlats C) (hC : ∀ m : ℤ, IsZero (C.homology m))
    (M : ModuleCat.{w} R) (n : ℤ) :
    IsZero ((tensorComplex C M).homology n) := by
  have := hd
  -- Exactness of `C` in every degree, read off as an equality of a range and a kernel.
  have hex : ∀ m : ℤ, LinearMap.range (C.d m (m + 1)).hom
      = LinearMap.ker (C.d (m + 1) (m + 1 + 1)).hom := by
    intro m
    have h : C.ExactAt (m + 1) :=
      (HomologicalComplex.exactAt_iff_isZero_homology C (m + 1)).2 (hC (m + 1))
    rw [HomologicalComplex.exactAt_iff' C m (m + 1) (m + 1 + 1)
        (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl),
      ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
    exact h
  -- The corestriction of a differential to the cocycles in the next degree.
  have hmem : ∀ (m : ℤ) (x : (C.X m : Type v)),
      (C.d m (m + 1)).hom x ∈ LinearMap.ker (C.d (m + 1) (m + 1 + 1)).hom :=
    fun m x => hex m ▸ LinearMap.mem_range_self _ x
  set q : ∀ m : ℤ, (C.X m : Type v) →ₗ[R] LinearMap.ker (C.d (m + 1) (m + 1 + 1)).hom :=
    fun m => ((C.d m (m + 1)).hom).codRestrict _ (hmem m) with hq
  have hqsurj : ∀ m : ℤ, Function.Surjective (q m) := by
    intro m y
    obtain ⟨x, hx⟩ : (y : (C.X (m + 1) : Type v)) ∈ LinearMap.range (C.d m (m + 1)).hom :=
      (hex m).symm ▸ y.2
    exact ⟨x, Subtype.ext hx⟩
  have hqexact : ∀ m : ℤ,
      Function.Exact (LinearMap.ker (C.d m (m + 1)).hom).subtype (q m) := by
    intro m
    rw [LinearMap.exact_iff, hq]
    simp only [LinearMap.ker_codRestrict, Submodule.range_subtype]
  -- Every module of cocycles is flat, by descending induction on the degree.
  have hZflat : ∀ m : ℤ, Module.Flat R (LinearMap.ker (C.d m (m + 1)).hom) := by
    have hvanish : ∀ m : ℤ, d < m →
        Module.Flat R (LinearMap.ker (C.d m (m + 1)).hom) := by
      intro m hm
      have : Subsingleton (C.X m) :=
        ModuleCat.isZero_iff_subsingleton.mp (C.isZero_of_isStrictlyLE d m hm)
      have : Subsingleton (LinearMap.ker (C.d m (m + 1)).hom) :=
        ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩
      infer_instance
    have key : ∀ (k : ℕ) (m : ℤ), d + 1 - m ≤ (k : ℤ) →
        Module.Flat R (LinearMap.ker (C.d m (m + 1)).hom) := by
      intro k
      induction k with
      | zero => exact fun m hm => hvanish m (by omega)
      | succ k ih =>
          intro m hm
          by_cases hdm : d < m
          · exact hvanish m hdm
          · have hQ : Module.Flat R (LinearMap.ker (C.d (m + 1) (m + 1 + 1)).hom) :=
              ih (m + 1) (by omega)
            have hB : Module.Flat R (C.X m : Type v) := hflat m
            exact flat_of_flat_of_flat_quotient _ Subtype.val_injective (q m)
              (hqsurj m) (hqexact m)
    exact fun m => key (d + 1 - m).toNat m (by omega)
  -- Flatness of the cocycles makes them pure: they stay a submodule after tensoring.
  have hpure : ∀ m : ℤ, Function.Injective
      (LinearMap.rTensor (M : Type w) (LinearMap.ker (C.d m (m + 1)).hom).subtype) := by
    intro m
    have := hZflat (m + 1)
    exact rTensor_injective_of_exact_of_flat_quotient _ Subtype.val_injective (q m)
      (hqsurj m) (hqexact m) (M : Type w)
  -- The tensored complex is exact in every degree.
  have hExT : ∀ m : ℤ, Function.Exact
      (LinearMap.rTensor (M : Type w) (C.d m (m + 1)).hom)
      (LinearMap.rTensor (M : Type w) (C.d (m + 1) (m + 1 + 1)).hom) := by
    intro m
    rw [LinearMap.exact_iff]
    have hfac : ∀ k : ℤ, (C.d k (k + 1)).hom
        = (LinearMap.ker (C.d (k + 1) (k + 1 + 1)).hom).subtype ∘ₗ q k := fun k => rfl
    -- The kernel of the outgoing map is the kernel of its corestriction.
    have hker : LinearMap.ker
        (LinearMap.rTensor (M : Type w) (C.d (m + 1) (m + 1 + 1)).hom)
        = LinearMap.ker (LinearMap.rTensor (M : Type w) (q (m + 1))) := by
      rw [hfac (m + 1), LinearMap.rTensor_comp]
      exact LinearMap.ker_comp_of_ker_eq_bot _
        (LinearMap.ker_eq_bot.2 (hpure (m + 1 + 1)))
    -- Right exactness identifies that kernel with the image of the cocycles.
    have hright : Function.Exact
        (LinearMap.rTensor (M : Type w)
          (LinearMap.ker (C.d (m + 1) (m + 1 + 1)).hom).subtype)
        (LinearMap.rTensor (M : Type w) (q (m + 1))) :=
      rTensor_exact (M : Type w) (hqexact (m + 1)) (hqsurj (m + 1))
    -- The image of the incoming map is the image of the cocycles.
    have hrange : LinearMap.range (LinearMap.rTensor (M : Type w) (C.d m (m + 1)).hom)
        = LinearMap.range (LinearMap.rTensor (M : Type w)
          (LinearMap.ker (C.d (m + 1) (m + 1 + 1)).hom).subtype) := by
      rw [hfac m, LinearMap.rTensor_comp]
      exact LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.2 (LinearMap.rTensor_surjective _ (hqsurj m)))
    rw [hker, hrange, ← LinearMap.exact_iff]
    exact hright
  -- Transport the exactness statement back to the vanishing of homology.
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' (tensorComplex C M) m (m + 1) (m + 1 + 1)
      (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact hExT m

/-! ### Comparison of two bounded above flat representatives -/

section Comparison

attribute [local instance] HasDerivedCategory.standard

/-- A product of two flat modules is flat. -/
private theorem flat_prod {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Flat R A] [Module.Flat R B] :
    Module.Flat R (A × B) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ α hα
  have hcomm : (TensorProduct.prodRight R R N' A B).toLinearMap ∘ₗ
        LinearMap.rTensor (A × B) α
      = (LinearMap.rTensor A α).prodMap (LinearMap.rTensor B α) ∘ₗ
        (TensorProduct.prodRight R R N A B).toLinearMap := by
    refine TensorProduct.ext' fun n ab => ?_
    simp
  intro x y hxy
  have hx := LinearMap.congr_fun hcomm x
  have hy := LinearMap.congr_fun hcomm y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.prodMap_apply] at hx hy
  have key : (LinearMap.rTensor A α ((TensorProduct.prodRight R R N A B) x).1,
        LinearMap.rTensor B α ((TensorProduct.prodRight R R N A B) x).2)
      = (LinearMap.rTensor A α ((TensorProduct.prodRight R R N A B) y).1,
        LinearMap.rTensor B α ((TensorProduct.prodRight R R N A B) y).2) := by
    rw [← hx, ← hy, hxy]
  refine (TensorProduct.prodRight R R N A B).injective (Prod.ext_iff.2 ⟨?_, ?_⟩)
  · exact Module.Flat.rTensor_preserves_injective_linearMap (M := A) α hα
      (congrArg Prod.fst key)
  · exact Module.Flat.rTensor_preserves_injective_linearMap (M := B) α hα
      (congrArg Prod.snd key)

/-- A morphism of cochain complexes is a quasi-isomorphism exactly when its mapping cone is
acyclic: the mapping cone triangle is distinguished in the homotopy category, where the
quasi-isomorphisms are the morphisms whose third vertex is acyclic. -/
private theorem quasiIso_iff_acyclic_mappingCone {A : Type*} [Category* A] [Abelian A]
    {F G : CochainComplex A ℤ} (f : F ⟶ G) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
    ← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact ObjectProperty.trW_iff_of_distinguished _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)

/-- Lift a morphism of the derived category out of a K-projective complex to an actual morphism
of complexes. -/
private lemma exists_chainMap_of_isKProjective {A : Type*} [Category* A] [Abelian A]
    (P G : CochainComplex A ℤ) [P.IsKProjective]
    (ψ : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj G) :
    ∃ γ : P ⟶ G, DerivedCategory.Q.map γ = ψ := by
  have hbij := (Iso.homCongr
      ((DerivedCategory.quotientCompQhIso A).app P)
      ((DerivedCategory.quotientCompQhIso A).app G)).bijective.comp
    (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj G))
  obtain ⟨f, hf⟩ := hbij.surjective ψ
  obtain ⟨γ, hγ⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective f
  refine ⟨γ, ?_⟩
  rw [← hf, ← hγ]
  simp only [Function.comp_apply, Iso.homCongr_apply, Iso.app_hom, Iso.app_inv,
    DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

/-- **Termwise tensoring preserves quasi-isomorphisms of bounded above complexes of flat
modules.** The mapping cone of such a quasi-isomorphism is a bounded above acyclic complex of
flat modules, hence stays acyclic after tensoring; since an additive functor commutes with
mapping cones, the tensored morphism has an acyclic mapping cone as well. -/
@[ega "0 11.9.3" "(i), special case", ega "III 6.10.3" "Remark 6.10.3(ii)"]
theorem quasiIso_mapHomologicalComplex_map_of_flat
    {F G : CochainComplex (ModuleCat.{v} R) ℤ} (dF dG : ℤ)
    (hF : F.IsStrictlyLE dF) (hG : G.IsStrictlyLE dG)
    (hFflat : IsComplexOfFlats F) (hGflat : IsComplexOfFlats G)
    (f : F ⟶ G) (hf : QuasiIso f) (M : ModuleCat.{w} R) :
    QuasiIso (((tensorRightMixed M).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have := hF
  have := hG
  have hCacyclic : (CochainComplex.mappingCone f).Acyclic :=
    (quasiIso_iff_acyclic_mappingCone f).1 hf
  have hCle : (CochainComplex.mappingCone f).IsStrictlyLE (max (dF - 1) dG) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨F.isZero_of_isStrictlyLE dF (i + 1) (by omega),
      G.isZero_of_isStrictlyLE dG i (by omega)⟩
  have hCflat : IsComplexOfFlats (CochainComplex.mappingCone f) := by
    intro i
    have h1 : Module.Flat R (F.X (i + 1) : Type v) := hFflat (i + 1)
    have h2 : Module.Flat R (G.X i : Type v) := hGflat i
    have : Module.Flat R ((F.X (i + 1) : Type v) × (G.X i : Type v)) := flat_prod
    exact Module.Flat.of_linearEquiv
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp) ≪≫
        ModuleCat.biprodIsoProd _ _).toLinearEquiv
  have hTacyclic : ∀ n : ℤ,
      IsZero ((tensorComplex (CochainComplex.mappingCone f) M).homology n) := fun n =>
    isZero_homology_tensorComplex_of_acyclic _ _ hCle hCflat
      (fun m => (hCacyclic m).isZero_homology) M n
  have hiso : ((tensorRightMixed M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone f) ≅ CochainComplex.mappingCone
        (((tensorRightMixed M).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f (tensorRightMixed M)
  rw [quasiIso_iff_acyclic_mappingCone]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hTacyclic n).of_iso (HomologicalComplex.homologyMapIso hiso n).symm

/-- **Tor amplitude from a flat representative.** A bounded above complex of flat modules whose
image in the derived category is isomorphic to a complex of flat modules concentrated in degrees
`[a, b]` has termwise Tor amplitude in `[a, b]`. The comparison goes through a bounded above
projective resolution of the complex, which is K-projective, so the given isomorphism of the
derived category is realized by an actual morphism of complexes. -/
@[sga "4 XVII 4.1.9" "special case", sga "6 I 5.1" "(i) ⇒ (ii)"]
theorem termwise_torAmplitude_of_flat_representative [Small.{v} R]
    (K E : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ)
    (hbounded : BoundedAbove K) (hflat : IsComplexOfFlats K)
    (hEflat : IsComplexOfFlats E) (hGE : E.IsStrictlyGE a) (hLE : E.IsStrictlyLE b)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj E) :
    HasTorAmplitudeIn K a b := by
  obtain ⟨d, hd⟩ := hbounded
  have hKle : K.IsStrictlyLE d := (CochainComplex.isStrictlyLE_iff K d).2 hd
  obtain ⟨P, -⟩ := ProjectiveResolutionLemma.statement3 d K hKle
  have hPle := P.boundedAbove
  have hPproj : ∀ n : ℤ, Projective (P.complex.X n) := P.projective
  have hPflat : IsComplexOfFlats P.complex := by
    intro n
    have := hPproj n
    infer_instance
  have hPqi : QuasiIso P.α := P.quasiIso
  have : P.complex.IsKProjective := CochainComplex.isKProjective_of_projective P.complex d
  obtain ⟨g, hg⟩ :=
    exists_chainMap_of_isKProjective P.complex E (DerivedCategory.Q.map P.α ≫ e.hom)
  have hPαiso : IsIso (DerivedCategory.Q.map P.α) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ P.α).2 hPqi
  have hgqi : QuasiIso g := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, hg]
    infer_instance
  have hLE' := hLE
  intro M i hi
  -- `E` vanishes outside `[a, b]`, hence so does its termwise tensor product with `M`.
  have hEamp : IsZero ((tensorComplex E M).homology i) := by
    have := hGE
    have hz : IsZero (E.X i) := by
      rcases hi with hi | hi
      · exact CochainComplex.isZero_of_isStrictlyGE E a i hi
      · exact CochainComplex.isZero_of_isStrictlyLE E b i hi
    exact ShortComplex.isZero_homology_of_isZero_X₂ _ ((tensorRightMixed M).map_isZero hz)
  -- Both comparison morphisms stay quasi-isomorphisms after tensoring.
  have hgT := quasiIso_mapHomologicalComplex_map_of_flat d b hPle hLE' hPflat hEflat g hgqi M
  have hαT := quasiIso_mapHomologicalComplex_map_of_flat d d hPle hKle hPflat hflat P.α hPqi M
  have hpull : ∀ {X Y : CochainComplex (ModuleCat.{v} R) ℤ} (φ : X ⟶ Y),
      QuasiIso (((tensorRightMixed M).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) →
      (IsZero ((tensorComplex X M).homology i) ↔ IsZero ((tensorComplex Y M).homology i)) :=
    fun φ hφ => by
      have := (quasiIsoAt_iff_isIso_homologyMap _ i).1 (hφ.quasiIsoAt i)
      let e := asIso (HomologicalComplex.homologyMap
        (((tensorRightMixed M).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) i)
      exact ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩
  exact (hpull P.α hαT).1 ((hpull g hgT).2 hEamp)

/-- **The flat-cokernel conclusion from a bounded flat representative.** If a bounded above
complex `K` of flat modules is isomorphic in the derived category to a complex of flat modules
concentrated in degrees `[a, b]`, then the cokernel of `d_K^{a-1}` is flat. -/
theorem cokernel_flat_of_flat_representative [Small.{v} R]
    (K E : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ)
    (hbounded : BoundedAbove K) (hflat : IsComplexOfFlats K)
    (hEflat : IsComplexOfFlats E) (hGE : E.IsStrictlyGE a) (hLE : E.IsStrictlyLE b)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj E) :
    Module.Flat R (cokernel (K.d (a - 1) a) : ModuleCat.{v} R) :=
  cokernel_flat_of_termwise_torAmplitude K a b hflat
    (termwise_torAmplitude_of_flat_representative K E a b hbounded hflat hEflat hGE hLE e)

end Comparison

end StacksDraft.TorAmplitude
