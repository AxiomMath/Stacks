module

public import StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZero
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantFromProZero
public import StacksFrontier.RingTheory.LocalCohomology.MittagLefflerSystems
import all StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZero

/-!
# Consequences of the pro-zero and stable-image assertions of Tag 0EFX

Let `A` be a commutative ring, `I ⊆ A` an ideal, `M` an `A`-module and `T ⊆ Spec(A)` a subset,
and write `H^i_T` for local cohomology with support in `T`. [Stacks, Tag 0EFY] draws seven
consequences from the two conclusions of Lemma [Stacks, Tag 0EFX]: that `{H^i_T(IⁿM)}` is
pro-zero for `i ≤ s`, and that the transition images of `{H^{s+1}_T(IⁿM)}` inject into one fixed
term. Part (1) is
`Stacks.LocalCohomology.exists_forall_injective_localCohomologyAdicProjection_of_proZero` in
`StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZero`; this module proves parts (2)-(6),
from those two conclusions supplied as the inputs `IsProZeroIdealPowerCohomology` and
`HasStableImageIdealPowerCohomology`. Part (7) is in
`StacksFrontier.RingTheory.LocalCohomology.IdealPowerFirstDerivedLimit`.

The engine is the naturality of the connecting map of the long exact sequence of
`0 → IⁿM → M → M/IⁿM → 0` in `n`, which identifies the image of a transition map of
`{H^i_T(M/IⁿM)}` with the image of `H^i_T(M) → H^i_T(M/IⁿM)`: the pro-zero assertion of Tag 0EFX
does it in degrees below `s` and the stable-image assertion in degree `s`.

## Main definitions

* `Stacks.LocalCohomology.IsProZeroIdealPowerCohomology`,
  `Stacks.LocalCohomology.HasStableImageIdealPowerCohomology` — the two conclusions of
  Tag 0EFX, named.

## Main results

* `Stacks.LocalCohomology.localCohomologyδ_idealPowerShortComplex_naturality` — the naturality
  of the connecting map along the morphism of short exact sequences
  `(0 → IᵏM → M → M/IᵏM → 0) ⟶ (0 → IⁿM → M → M/IⁿM → 0)` for `n ≤ k`, from
  `Stacks.LocalCohomology.localCohomologyδ_naturality` and
  `Stacks.LocalCohomology.idealPowerShortComplexMap` of `EssentiallyConstantFromProZero.lean`.
* `Stacks.LocalCohomology.range_localCohomologyAdicTower_map_eq_of_map_eq_zero`,
  `Stacks.LocalCohomology.range_localCohomologyAdicTower_map_eq_of_stableImage` — the images of
  the transition maps of `{H^i_T(M/IⁿM)}`, computed from the two conclusions of Tag 0EFX.
* `Stacks.LocalCohomology.isMittagLefflerCategorical_localCohomologyAdicTower_of_proZero`,
  `Stacks.LocalCohomology.isMittagLefflerCategorical_localCohomologyAdicTower_of_stableImage` —
  the passages to parts (2) and (3) of Tag 0EFY.
* `Stacks.LocalCohomology.isIso_limitLift_localCohomologyAdicCone_of_proZero`,
  `Stacks.LocalCohomology.isIso_limitLift_localCohomologyAdicCone_of_stableImage` — the passages
  to parts (4) and (5) of Tag 0EFY.
* `Stacks.LocalCohomology.exists_injective_limitLift_and_smul_mem_range` — the passage to part (6)
  of Tag 0EFY.

These are engines carrying no tag: each takes a conclusion of Tag 0EFX as an explicit
hypothesis. In Situation [Stacks, Tag 0EFU] those conclusions are theorems, proved at `T = {𝔪}`
over a Noetherian local ring by
`Stacks.Algebraization.exists_map_idealPowerTower_eq_zero_closedPoint` and
`Stacks.Algebraization.hasStableImageIdealPowerCohomology_closedPoint`, and at a general
specialization-stable `T` by `Stacks.Algebraization.isProZeroIdealPowerCohomology` and
`Stacks.Algebraization.exists_hasStableImageIdealPowerCohomology`.

## Implementation notes

Parts (3) and (5) concern the subquotients `I^{m₀}M/IⁿM` of the source. They are stated here for
the adic quotients `N/IⁿN` of a module `N`, the intended instance being `N = I^{m₀}M`, whose adic
quotient tower is the source's system read along the cofinal shift `n ↦ n + m₀`. Under that shift
the source's base index `m₀` becomes the base index `0`, which is why those two statements ask
for the stable-image assertion based at `0`; the identification of the two towers is
`Stacks.Algebraization.idealPowerTowerShiftIso`, and the rebasing it performs is
`Stacks.Algebraization.hasStableImageIdealPowerCohomology_idealPowerSubmodule`.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### The morphisms of short exact sequences, and the naturality of the connecting map -/

/-- **Naturality of the connecting map along the ideal-power filtration.** For `n ≤ k` the
connecting maps of `0 → IⁿM → M → M/IⁿM → 0` and of `0 → IᵏM → M → M/IᵏM → 0` are intertwined by
the transition maps of the towers `{M/IⁿM}` and `{IⁿM}`. -/
theorem localCohomologyδ_idealPowerShortComplex_naturality (T : Set (PrimeSpectrum A))
    (I : Ideal A) (M : ModuleCat.{max u v} A) (i j : ℤ) (hj : i + 1 = j) {n k : ℕ} (h : n ≤ k) :
    (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
          ((idealPowerQuotientTower.{u, v} I M).map (homOfLE h).op) ≫
        localCohomologyδ.{u, v} T (idealPowerShortComplex_shortExact.{u, v} I M n) i j hj =
      localCohomologyδ.{u, v} T (idealPowerShortComplex_shortExact.{u, v} I M k) i j hj ≫
        (localCohomologyWithSupportInModuleFunctor.{u, v} A T j).map
          ((idealPowerTower.{u, v} I M).map (homOfLE h).op) :=
  localCohomologyδ_naturality.{u, v} T
    (idealPowerShortComplex_shortExact.{u, v} I M k)
    (idealPowerShortComplex_shortExact.{u, v} I M n)
    (idealPowerShortComplexMap.{u, v} I M h) i j hj

/-- Composing two transition maps of an inverse system gives the transition map of the composite
bound. -/
private theorem functor_map_comp_map {C : Type*} [Category C] (G : ℕᵒᵖ ⥤ C) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    G.map (homOfLE hjk).op ≫ G.map (homOfLE hij).op = G.map (homOfLE (hij.trans hjk)).op := by
  rw [← G.map_comp]; congr 1

/-- Local cohomology with support in `T`, being `A`-linear, kills the zero morphism. -/
private theorem localCohomologyWithSupportInModuleFunctor_map_zero (T : Set (PrimeSpectrum A))
    (i : ℤ) {X Y : ModuleCat.{max u v} A} :
    (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map (0 : X ⟶ Y) = 0 := by
  have h0 : (0 : X ⟶ Y) = (0 : A) • 0 := by rw [zero_smul]
  rw [h0, Functor.map_smul, zero_smul]

/-- A morphism of `A`-modules that vanishes kills every element. -/
private theorem hom_apply_eq_zero {X Y : ModuleCat.{max u v} A} {f : X ⟶ Y} (hf : f = 0)
    (x : X) : f.hom x = 0 := by
  rw [hf]; rfl

/-- If `f(x) = g(d)` and `g(a · d) = 0` then `f(a · x) = 0`. -/
private theorem hom_apply_smul_eq_zero {X Y Z : ModuleCat.{max u v} A} (f : X ⟶ Y) (g : Z ⟶ Y)
    {a : A} {x : X} {d : Z} (hd : f.hom x = g.hom d) (h0 : g.hom (a • d) = 0) :
    f.hom (a • x) = 0 := by
  rw [f.hom.map_smul, hd, ← g.hom.map_smul, h0]

/-- If `f(x) = g₂(e)`, `e = g₁(d)` and `a` annihilates `x`, then `g₂(g₁(a · d)) = 0`. -/
private theorem comp_hom_apply_smul_eq_zero {X Y Z W : ModuleCat.{max u v} A} (g₁ : Z ⟶ Y)
    (g₂ : Y ⟶ W) (f : X ⟶ W) {a : A} {x : X} {d : Z} {e : Y} (hnat : f.hom x = g₂.hom e)
    (hd : e = g₁.hom d) (hx : a • x = 0) : g₂.hom (g₁.hom (a • d)) = 0 := by
  rw [g₁.hom.map_smul, ← hd, g₂.hom.map_smul, ← hnat, ← f.hom.map_smul, hx, map_zero]

/-- A commuting square of `A`-modules, read on elements. -/
private theorem apply_comp_eq_apply_comp {X Y Z W : ModuleCat.{max u v} A} {f : X ⟶ Y}
    {g : Y ⟶ W} {f' : X ⟶ Z} {g' : Z ⟶ W} (h : f ≫ g = f' ≫ g') (x : X) :
    g.hom (f.hom x) = g'.hom (f'.hom x) :=
  congrArg (fun φ : X ⟶ W => φ.hom x) h

/-! ### A criterion for a cone of modules over `ℕᵒᵖ` to be a limit cone -/

/-- The comparison morphism to the inverse limit, followed by a projection of the limit, is the
corresponding projection of the cone. -/
private theorem limit_π_limitLift {F : ℕᵒᵖ ⥤ ModuleCat.{max u v} A} (c : Cone F) (n : ℕᵒᵖ)
    (x : c.pt) : (limit.π F n).hom ((limit.lift F c).hom x) = (c.π.app n).hom x := by
  conv_rhs => rw [← limit.lift_π c n]
  rfl

/-- The projections of the inverse limit of a system of modules are compatible with its
transition maps. -/
private theorem limit_π_map {F : ℕᵒᵖ ⥤ ModuleCat.{max u v} A} {m n : ℕᵒᵖ} (f : m ⟶ n)
    (z : (limit F : ModuleCat.{max u v} A)) :
    (F.map f).hom ((limit.π F m).hom z) = (limit.π F n).hom z := by
  conv_rhs => rw [← limit.w F f]
  rfl

/-- The comparison morphism from the point of a cone on an inverse system of `A`-modules to the
inverse limit of the system is an isomorphism as soon as the projections of the cone are jointly
injective and the cone hits every compatible family: the first clause makes the comparison
injective and the second makes it surjective. -/
theorem isIso_limitLift_of_jointlyInjective_of_surjective
    {F : ℕᵒᵖ ⥤ ModuleCat.{max u v} A} (c : Cone F)
    (hinj : ∀ x y : c.pt, (∀ n : ℕᵒᵖ, (c.π.app n).hom x = (c.π.app n).hom y) → x = y)
    (hsurj : ∀ y : ∀ n : ℕᵒᵖ, F.obj n,
      (∀ (m n : ℕᵒᵖ) (f : m ⟶ n), (F.map f).hom (y m) = y n) →
      ∃ x : c.pt, ∀ n : ℕᵒᵖ, (c.π.app n).hom x = y n) :
    IsIso (limit.lift F c) := by
  have key := limit_π_limitLift.{u, v} c
  have hmono : Mono (limit.lift F c) := by
    refine (ModuleCat.mono_iff_injective _).2 fun x y hxy => ?_
    refine hinj x y fun n => ?_
    rw [← key n x, ← key n y]
    exact congrArg (limit.π F n).hom hxy
  have hepi : Epi (limit.lift F c) := by
    refine (ModuleCat.epi_iff_surjective _).2 fun z => ?_
    obtain ⟨x, hx⟩ := hsurj (fun n => (limit.π F n).hom z) (fun _ _ f => limit_π_map f z)
    exact ⟨x, Limits.Concrete.limit_ext F _ _ fun n => by rw [key n x, hx n]⟩
  exact isIso_of_mono_of_epi _

/-! ### Tag 0EFY, parts (2)-(7): the Mittag-Leffler conditions and the limit comparisons -/

/-- **The pro-zero assertion of [Stacks, Tag 0EFX] in degree `j`**, as a named hypothesis: for
every `m` some transition map `H^j_T(IᵏM) → H^j_T(IᵐM)` of the inverse system `{H^j_T(IⁿM)}`
vanishes.

This is verbatim the conclusion of `exists_map_idealPowerTower_eq_zero_of_local`, quantified over
the index `m`; in Situation [Stacks, Tag 0EFU] it holds for `j ≤ s`. -/
def IsProZeroIdealPowerCohomology (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (j : ℤ) : Prop :=
  ∀ m : ℕ, ∃ k : ℕ, ∃ h : m ≤ k,
    (localCohomologyWithSupportInModuleFunctor.{u, v} A T j).map
      ((idealPowerTower.{u, v} I M).map (homOfLE h).op) = 0

/-- A pro-zero inverse system has vanishing transition maps from every sufficiently large index:
the transition map `IᵏM → IᵐM` factors through `I^{c}M` for `m ≤ c ≤ k`. -/
theorem IsProZeroIdealPowerCohomology.exists_forall_map_eq_zero {T : Set (PrimeSpectrum A)}
    {I : Ideal A} {M : ModuleCat.{max u v} A} {j : ℤ}
    (h : IsProZeroIdealPowerCohomology.{u, v} T I M j) (m : ℕ) :
    ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      (localCohomologyWithSupportInModuleFunctor.{u, v} A T j).map
        ((idealPowerTower.{u, v} I M).map (homOfLE (hmc.trans hck)).op) = 0 := by
  obtain ⟨c, hmc, hc⟩ := h m
  refine ⟨c, hmc, fun k hck => ?_⟩
  rw [← idealPowerTower_map_comp_map.{u, v} I M hmc hck, Functor.map_comp, hc, comp_zero]

/-- The Mittag-Leffler condition for an inverse system of modules, in terms of the ranges of the
transition maps. (`Stacks.LocalCohomology.subobjectModule_transitionImage` is the same
computation, but its statement fixes the module universe to be the ring's.) -/
private theorem isMittagLefflerCategorical_of_range_eq {F : ℕᵒᵖ ⥤ ModuleCat.{max u v} A}
    (h : ∀ i : ℕ, ∃ c : ℕ, ∃ hic : i ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      LinearMap.range (F.map (homOfLE (hic.trans hck)).op).hom =
        LinearMap.range (F.map (homOfLE hic).op).hom) :
    IsMittagLefflerCategorical F := by
  intro i
  obtain ⟨c, hic, hrange⟩ := h i
  have hsub : ∀ (j : ℕ) (hij : i ≤ j),
      ModuleCat.subobjectModule (F.obj (op i)) (transitionImage F i j hij) =
        LinearMap.range (F.map (homOfLE hij).op).hom := by
    intro j hij
    have heq : Subobject.mk (image.ι (F.map (homOfLE hij).op)) =
        Subobject.mk (ModuleCat.ofHom (F.map (homOfLE hij).op).hom.range.subtype) :=
      Subobject.mk_eq_mk_of_comm _ _ (ModuleCat.imageIsoRange _)
        (ModuleCat.imageIsoRange_hom_subtype _)
    rw [transitionImage, heq]
    exact (ModuleCat.subobjectModule (F.obj (op i))).apply_symm_apply _
  exact ⟨c, hic, fun k hck => (ModuleCat.subobjectModule (F.obj (op i))).injective
    (((hsub k (hic.trans hck)).trans (hrange k hck)).trans (hsub c hic).symm)⟩

/-- The projections of the cone `localCohomologyAdicCone` are compatible with the transition maps
of the tower `{H^i_T(M/IⁿM)}`. -/
private theorem localCohomologyAdicTower_map_proj (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (i : ℤ) (M : ModuleCat.{max u v} A) {n k : ℕ} (h : n ≤ k)
    (x : (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj M) :
    ((localCohomologyAdicTower.{u, v} A T I i M).map (homOfLE h).op).hom
        (((localCohomologyAdicCone.{u, v} A T I i M).π.app (op k)).hom x) =
      ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom x := by
  conv_rhs => rw [← (localCohomologyAdicCone.{u, v} A T I i M).w (homOfLE h).op]
  rfl

/-- A class of `H^i_T(M/IⁿM)` killed by the connecting map comes from `H^i_T(M)`. -/
private theorem mem_range_proj_of_localCohomologyδ_eq_zero (T : Set (PrimeSpectrum A))
    (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℤ) (n : ℕ)
    {w : (localCohomologyAdicTower.{u, v} A T I i M).obj (op n)}
    (hw : (localCohomologyδ.{u, v} T (idealPowerShortComplex_shortExact.{u, v} I M n) i (i + 1)
      rfl).hom w = 0) :
    w ∈ LinearMap.range ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom :=
  (ShortComplex.moduleCat_exact_iff _).mp
    (localCohomology_exact₃.{u, v} T (idealPowerShortComplex_shortExact.{u, v} I M n)
      i (i + 1) rfl) _ hw

/-- The image of `H^i_T(M) → H^i_T(M/IⁿM)` lies in the image of the transition map from any
higher level `k`, since it factors through `H^i_T(M/IᵏM)`. -/
private theorem range_proj_le_range_map (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (i : ℤ) (M : ModuleCat.{max u v} A) {n k : ℕ} (h : n ≤ k) :
    LinearMap.range ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom ≤
      LinearMap.range ((localCohomologyAdicTower.{u, v} A T I i M).map (homOfLE h).op).hom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨((localCohomologyAdicCone.{u, v} A T I i M).π.app (op k)).hom x,
    localCohomologyAdicTower_map_proj.{u, v} T I i M h x⟩

/-- Pro-zero in degree `i` makes the projections `H^i_T(M) → H^i_T(M/IⁿM)` injective for all
large `n`. -/
private theorem exists_forall_injective_proj_of_proZero (T : Set (PrimeSpectrum A))
    (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℤ)
    (hpro : IsProZeroIdealPowerCohomology.{u, v} T I M i) :
    ∃ k₀ : ℕ, ∀ n : ℕ, k₀ ≤ n →
      Function.Injective ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom := by
  obtain ⟨k₀, hk₀, hzero₀⟩ := hpro 0
  exact ⟨k₀, fun n hn => injective_localCohomologyAdicProjection_of_inclusion_eq_zero.{u, v}
    T I M i n (localCohomology_idealPowerInclusion_eq_zero.{u, v} T I M i hk₀ hn hzero₀)⟩

/-- **The images of the transition maps of `{H^i_T(M/IⁿM)}`, computed.** If the transition map
`H^{i+1}_T(IᵏM) → H^{i+1}_T(IⁿM)` vanishes, then the image of `H^i_T(M/IᵏM) → H^i_T(M/IⁿM)` is
exactly the image of `H^i_T(M) → H^i_T(M/IⁿM)`.

*Argument.* One inclusion is the factorization of `H^i_T(M) → H^i_T(M/IⁿM)` through
`H^i_T(M/IᵏM)`. For the other, the long exact sequence of `0 → IⁿM → M → M/IⁿM → 0` identifies
the image of `H^i_T(M) → H^i_T(M/IⁿM)` with the kernel of the connecting map
`H^i_T(M/IⁿM) → H^{i+1}_T(IⁿM)`, and that connecting map annihilates the image of
`H^i_T(M/IᵏM)` because of its naturality in the ideal-power filtration: on that image it factors
through the vanishing transition map `H^{i+1}_T(IᵏM) → H^{i+1}_T(IⁿM)`. -/
theorem range_localCohomologyAdicTower_map_eq_of_map_eq_zero (T : Set (PrimeSpectrum A))
    (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℤ) {n k : ℕ} (h : n ≤ k)
    (hz : (localCohomologyWithSupportInModuleFunctor.{u, v} A T (i + 1)).map
      ((idealPowerTower.{u, v} I M).map (homOfLE h).op) = 0) :
    LinearMap.range ((localCohomologyAdicTower.{u, v} A T I i M).map (homOfLE h).op).hom =
      LinearMap.range ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom := by
  refine le_antisymm ?_ (range_proj_le_range_map.{u, v} T I i M h)
  rintro _ ⟨x, rfl⟩
  exact mem_range_proj_of_localCohomologyδ_eq_zero.{u, v} T I M i n
    ((apply_comp_eq_apply_comp.{u, v}
      (localCohomologyδ_idealPowerShortComplex_naturality.{u, v} T I M i (i + 1) rfl h) x).trans
      (hom_apply_eq_zero.{u, v} hz _))

/-- A compatible family in `{H^i_T(M/IⁿM)}` is the image of a single class in `H^i_T(M)` as soon
as each of its members lies in the image of the corresponding projection and the projections are
injective from some index `k₀` on: the lifts at the levels `≥ k₀` are unique, hence agree, and the
resulting class also has the right image below `k₀` by compatibility. -/
private theorem exists_proj_eq_of_forall_mem_range (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (i : ℤ) {k₀ : ℕ}
    (hinj : ∀ n : ℕ, k₀ ≤ n →
      Function.Injective ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom)
    (y : ∀ n : ℕᵒᵖ, (localCohomologyAdicTower.{u, v} A T I i M).obj n)
    (hy : ∀ (m n : ℕᵒᵖ) (f : m ⟶ n),
      ((localCohomologyAdicTower.{u, v} A T I i M).map f).hom (y m) = y n)
    (hlift : ∀ n : ℕ, ∃ x, ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom x =
      y (op n)) :
    ∃ x : (localCohomologyAdicCone.{u, v} A T I i M).pt,
      ∀ n : ℕᵒᵖ, ((localCohomologyAdicCone.{u, v} A T I i M).π.app n).hom x = y n := by
  obtain ⟨x, hx⟩ := hlift k₀
  refine ⟨x, fun n => ?_⟩
  change ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n.unop)).hom x = y (op n.unop)
  obtain ⟨z, hz⟩ := hlift (max n.unop k₀)
  have hzx : z = x := by
    refine hinj k₀ le_rfl ?_
    rw [hx, ← localCohomologyAdicTower_map_proj.{u, v} T I i M (le_max_right n.unop k₀) z, hz]
    exact hy (op (max n.unop k₀)) (op k₀) (homOfLE (le_max_right n.unop k₀)).op
  rw [← hzx, ← localCohomologyAdicTower_map_proj.{u, v} T I i M (le_max_left n.unop k₀) z, hz]
  exact hy (op (max n.unop k₀)) (op n.unop) (homOfLE (le_max_left n.unop k₀)).op

/-- **The passage from the pro-zero assertion of [Stacks, Tag 0EFX] to part (2) of
[Stacks, Tag 0EFY].** The inverse system `{H^i_T(M/IⁿM)}` satisfies the Mittag-Leffler condition
as soon as `{H^{i+1}_T(IⁿM)}` is pro-zero; in Situation [Stacks, Tag 0EFU] the latter holds for
`i + 1 ≤ s`, that is for `i < s`, which is the range of part (2).

*Argument.* Fix `n` and choose `c ≥ n` beyond which every transition map
`H^{i+1}_T(IᵏM) → H^{i+1}_T(IⁿM)` vanishes. By
`range_localCohomologyAdicTower_map_eq_of_map_eq_zero` the image of
`H^i_T(M/IᵏM) → H^i_T(M/IⁿM)` equals the image of `H^i_T(M) → H^i_T(M/IⁿM)` for every `k ≥ c`,
and in particular is independent of `k`.

*What this assumes, and why it carries no `@[stacks 0EFY]`.* The hypothesis `hpro` is the pro-zero
conclusion of Lemma [Stacks, Tag 0EFX] in degree `i + 1`, which in Situation [Stacks, Tag 0EFU] is
a theorem and not a restriction on the data; so part (2) is not covered *here*, this module making
no use of that situation. This theorem is the engine that delivers it, and it is run on the
discharged hypothesis in
`Stacks.Algebraization.isMittagLefflerCategorical_localCohomologyAdicTower`, which carries the tag
for part (2) at a general specialization-stable `T`. Part (2) is registered separately at
`T = {𝔪}` over a Noetherian local ring, by
`Stacks.LocalCohomology.isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology`. -/
theorem isMittagLefflerCategorical_localCohomologyAdicTower_of_proZero
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℤ)
    (hpro : IsProZeroIdealPowerCohomology.{u, v} T I M (i + 1)) :
    IsMittagLefflerCategorical (localCohomologyAdicTower.{u, v} A T I i M) := by
  refine isMittagLefflerCategorical_of_range_eq.{u, v} fun n => ?_
  obtain ⟨c, hnc, hc⟩ := hpro.exists_forall_map_eq_zero n
  exact ⟨c, hnc, fun k hck =>
    (range_localCohomologyAdicTower_map_eq_of_map_eq_zero.{u, v} T I M i (hnc.trans hck)
        (hc k hck)).trans
      (range_localCohomologyAdicTower_map_eq_of_map_eq_zero.{u, v} T I M i hnc
        (hc c le_rfl)).symm⟩

/-- **The passage from the pro-zero assertion of [Stacks, Tag 0EFX] to part (4) of
[Stacks, Tag 0EFY].** The comparison map
`H^i_T(M) → lim H^i_T(M/IⁿM)` is an isomorphism as soon as both `{H^i_T(IⁿM)}` and
`{H^{i+1}_T(IⁿM)}` are pro-zero; in Situation [Stacks, Tag 0EFU] both hold for `i + 1 ≤ s`,
that is for `i < s`, which is the range of part (4). The comparison map is the one induced by the
projections `H^i_T(M) → H^i_T(M/IⁿM)`, that is `limit.lift` of the cone
`localCohomologyAdicCone`.

*Argument.* Pro-zero in degree `i` gives, by part (1), an `m₀` beyond which every projection
`H^i_T(M) → H^i_T(M/IⁿM)` is injective, so the projections are jointly injective. Pro-zero in
degree `i + 1` gives, by `range_localCohomologyAdicTower_map_eq_of_map_eq_zero`, that every
element of `H^i_T(M/IⁿM)` which is a transition image from a high enough level lies in the image
of `H^i_T(M)`; a compatible family is such at every level, so each of its members lifts, and the
lifts agree because the projections are injective from `m₀` on.

*What this assumes, and why it carries no `@[stacks 0EFY]`.* The hypotheses `hpro` and `hpro'` are
the pro-zero conclusion of Lemma [Stacks, Tag 0EFX] in degrees `i` and `i + 1`, which in
Situation [Stacks, Tag 0EFU] is a theorem and not a restriction on the data; so part (4) is not
covered *here*, this module making no use of that situation. This theorem is the engine that
delivers it, and it is run on the discharged hypotheses in
`Stacks.Algebraization.isIso_limitLift_localCohomologyAdicCone`, which carries the tag for
part (4) at a general specialization-stable `T`. -/
theorem isIso_limitLift_localCohomologyAdicCone_of_proZero (T : Set (PrimeSpectrum A))
    (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℤ)
    (hpro : IsProZeroIdealPowerCohomology.{u, v} T I M i)
    (hpro' : IsProZeroIdealPowerCohomology.{u, v} T I M (i + 1)) :
    IsIso (limit.lift (localCohomologyAdicTower.{u, v} A T I i M)
      (localCohomologyAdicCone.{u, v} A T I i M)) := by
  obtain ⟨k₀, hinj⟩ := exists_forall_injective_proj_of_proZero.{u, v} T I M i hpro
  refine isIso_limitLift_of_jointlyInjective_of_surjective.{u, v} _
    (fun x y hxy => hinj k₀ le_rfl (hxy (op k₀))) fun y hy => ?_
  have hlift : ∀ n : ℕ, ∃ x, ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom x =
      y (op n) := by
    intro n
    obtain ⟨k, hnk, hz⟩ := hpro' n
    rw [← LinearMap.mem_range,
      ← range_localCohomologyAdicTower_map_eq_of_map_eq_zero.{u, v} T I M i hnk hz]
    exact ⟨y (op k), hy (op k) (op n) (homOfLE hnk).op⟩
  exact exists_proj_eq_of_forall_mem_range.{u, v} T I M i hinj y hy hlift

/-! #### Parts (3) and (5): the top degree `s`, from the stable-image assertion of Tag 0EFX -/

/-- **The stable-image assertion of [Stacks, Tag 0EFX] in degree `j`, based at `m₀`**, as a named
hypothesis: for every `m ≥ m₀` there is a `c ≥ m` such that for every `k ≥ c` the image of
`H^j_T(IᵏM) → H^j_T(IᵐM)` maps injectively to `H^j_T(I^{m₀}M)`.

This is verbatim the conclusion of
`exists_eventually_injective_image_idealPowerTower_of_local`; in Situation [Stacks, Tag 0EFU] it
holds in degree `s + 1` for some `m₀`. -/
def HasStableImageIdealPowerCohomology (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (j : ℤ) (m₀ : ℕ) : Prop :=
  ∀ (m : ℕ) (hm₀m : m₀ ≤ m), ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
    ∀ x : (idealPowerTower.{u, v} I M ⋙
        localCohomologyWithSupportInModuleFunctor.{u, v} A T j).obj (op k),
      ((idealPowerTower.{u, v} I M ⋙
        localCohomologyWithSupportInModuleFunctor.{u, v} A T j).map
          (homOfLE (hmc.trans hck)).op).hom x ∈
        LinearMap.ker ((idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T j).map (homOfLE hm₀m).op).hom →
      ((idealPowerTower.{u, v} I M ⋙
        localCohomologyWithSupportInModuleFunctor.{u, v} A T j).map
          (homOfLE (hmc.trans hck)).op).hom x = 0

/-- The stable-image assertion based at `m₀` also holds based at any larger index: the transition
map to `H^j_T(I^{m₀}M)` factors through `H^j_T(I^{m₁}M)`, so a class killed by the latter is
killed by the former. -/
theorem HasStableImageIdealPowerCohomology.mono {T : Set (PrimeSpectrum A)} {I : Ideal A}
    {M : ModuleCat.{max u v} A} {j : ℤ} {m₀ : ℕ}
    (h : HasStableImageIdealPowerCohomology.{u, v} T I M j m₀) {m₁ : ℕ} (hm : m₀ ≤ m₁) :
    HasStableImageIdealPowerCohomology.{u, v} T I M j m₁ := by
  intro m hm₁m
  obtain ⟨c, hmc, hc⟩ := h m (hm.trans hm₁m)
  refine ⟨c, hmc, fun k hck x hx => hc k hck x ?_⟩
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← functor_map_comp_map
    (idealPowerTower.{u, v} I M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T j)
    hm hm₁m, ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero]

/-- The connecting map applied to a transition image from level `k` is a transition image from
level `k` in degree `i + 1`. This is the naturality of the connecting map, packaged so that the
class in `H^{i+1}_T(IᵏM)` it produces is available as a variable. -/
private theorem exists_localCohomologyδ_eq_map (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (i : ℤ) {n k : ℕ} (h : n ≤ k)
    (x : (localCohomologyAdicTower.{u, v} A T I i M).obj (op k)) :
    ∃ d : (localCohomologyWithSupportInModuleFunctor.{u, v} A T (i + 1)).obj
        ((idealPowerTower.{u, v} I M).obj (op k)),
      (localCohomologyδ.{u, v} T (idealPowerShortComplex_shortExact.{u, v} I M n) i (i + 1)
            rfl).hom
          (((localCohomologyAdicTower.{u, v} A T I i M).map (homOfLE h).op).hom x) =
        ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (i + 1)).map
          ((idealPowerTower.{u, v} I M).map (homOfLE h).op)).hom d :=
  ⟨_, apply_comp_eq_apply_comp.{u, v}
    (localCohomologyδ_idealPowerShortComplex_naturality.{u, v} T I M i (i + 1) rfl h) x⟩

/-- The connecting map of `0 → I⁰M → M → M/I⁰M → 0` vanishes: `I⁰M = M`, so the third term of
that short exact sequence is the zero module and `H^i_T` of it is a zero object. -/
theorem localCohomologyδ_idealPowerShortComplex_zero_eq_zero (T : Set (PrimeSpectrum A))
    (I : Ideal A) (M : ModuleCat.{max u v} A) (i j : ℤ) (hj : i + 1 = j) :
    localCohomologyδ.{u, v} T (idealPowerShortComplex_shortExact.{u, v} I M 0) i j hj = 0 := by
  have hid : 𝟙 ((idealPowerQuotientTower.{u, v} I M).obj (op 0)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (I ^ 0 • (⊤ : Submodule A M)) x
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    simp
  have hzero : IsZero ((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj
      ((idealPowerQuotientTower.{u, v} I M).obj (op 0))) := by
    rw [IsZero.iff_id_eq_zero, ← (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map_id
      ((idealPowerQuotientTower.{u, v} I M).obj (op 0)), hid,
      localCohomologyWithSupportInModuleFunctor_map_zero.{u, v} T i]
  exact hzero.eq_zero_of_src _

/-- **The images of the transition maps of `{H^s_T(M/IⁿM)}`, computed from the stable-image
assertion.** Suppose that elements of the image of `H^{s+1}_T(IᵏM) → H^{s+1}_T(IⁿM)` which die in
`H^{s+1}_T(I^{m₀}M)` vanish, and that the connecting map of `0 → I^{m₀}M → M → M/I^{m₀}M → 0`
vanishes. Then the image of `H^s_T(M/IᵏM) → H^s_T(M/IⁿM)` is exactly the image of
`H^s_T(M) → H^s_T(M/IⁿM)`.

*Argument.* As in `range_localCohomologyAdicTower_map_eq_of_map_eq_zero`, the image of
`H^s_T(M) → H^s_T(M/IⁿM)` is the kernel of the connecting map
`H^s_T(M/IⁿM) → H^{s+1}_T(IⁿM)`, and the naturality of that connecting map in the ideal-power
filtration puts the connecting map of a transition image from level `k` inside the image of
`H^{s+1}_T(IᵏM) → H^{s+1}_T(IⁿM)`. Naturality at `m₀ ≤ n` and the vanishing of the connecting map
at level `m₀` show that it dies in `H^{s+1}_T(I^{m₀}M)`, so it vanishes. -/
theorem range_localCohomologyAdicTower_map_eq_of_stableImage (T : Set (PrimeSpectrum A))
    (I : Ideal A) (M : ModuleCat.{max u v} A) (s : ℤ) {m₀ n k : ℕ} (hm₀n : m₀ ≤ n) (hnk : n ≤ k)
    (hδ : localCohomologyδ.{u, v} T (idealPowerShortComplex_shortExact.{u, v} I M m₀) s (s + 1)
      rfl = 0)
    (hstab : ∀ x : (localCohomologyWithSupportInModuleFunctor.{u, v} A T (s + 1)).obj
        ((idealPowerTower.{u, v} I M).obj (op k)),
      ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (s + 1)).map
        ((idealPowerTower.{u, v} I M).map (homOfLE hnk).op)).hom x ∈
        LinearMap.ker ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (s + 1)).map
          ((idealPowerTower.{u, v} I M).map (homOfLE hm₀n).op)).hom →
      ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (s + 1)).map
        ((idealPowerTower.{u, v} I M).map (homOfLE hnk).op)).hom x = 0) :
    LinearMap.range ((localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE hnk).op).hom =
      LinearMap.range ((localCohomologyAdicCone.{u, v} A T I s M).π.app (op n)).hom := by
  refine le_antisymm ?_ (range_proj_le_range_map.{u, v} T I s M hnk)
  rintro _ ⟨x, rfl⟩
  obtain ⟨d, hd⟩ := exists_localCohomologyδ_eq_map.{u, v} T I M s hnk x
  have hw2 := apply_comp_eq_apply_comp.{u, v}
    (localCohomologyδ_idealPowerShortComplex_naturality.{u, v} T I M s (s + 1) rfl hm₀n)
    (((localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE hnk).op).hom x)
  have h3 := hstab d (by
    rw [LinearMap.mem_ker, ← hd]
    exact hw2.symm.trans (hom_apply_eq_zero.{u, v} hδ _))
  exact mem_range_proj_of_localCohomologyδ_eq_zero.{u, v} T I M s n (hd.trans h3)

/-- **The passage from the stable-image assertion of [Stacks, Tag 0EFX] to part (3) of
[Stacks, Tag 0EFY] in the top degree.** The inverse system `{H^s_T(M/IⁿM)}` satisfies the
Mittag-Leffler condition as soon as `{H^{s+1}_T(IⁿM)}` has stable images injecting into
`H^{s+1}_T(I⁰M) = H^{s+1}_T(M)`, which is the stable-image assertion of [Stacks, Tag 0EFX] based
at `m₀ = 0`.

In the source part (3) is the Mittag-Leffler condition for `{H^i_T(I^{m₀}M/IⁿM)}_{n ≥ m₀}` for
`i ≤ s`. Applied to the module `I^{m₀}M`, the tower here is `{I^{m₀}M/Iⁿ(I^{m₀}M)}`, that is
`{I^{m₀}M/I^{n+m₀}M}`: the source's system read along the cofinal shift `n ↦ n + m₀`, exactly as
in `Stacks.LocalCohomology.isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology_smul`.
Under that shift the source's base index `m₀` becomes the base index `0` of the hypothesis, and
the range `i < s` of part (3) is covered by
`isMittagLefflerCategorical_localCohomologyAdicTower_of_proZero`.

*What this assumes, and why it carries no `@[stacks 0EFY]`.* The hypothesis `hstab` is the
stable-image conclusion of Lemma [Stacks, Tag 0EFX], which in Situation [Stacks, Tag 0EFU] is a
theorem and not a restriction on the data. This theorem is the engine; run on that conclusion it
delivers part (3) at a general specialization-stable `T`, in
`Stacks.Algebraization.isMittagLefflerCategorical_localCohomologyAdicTower_idealPowerSubmodule`.
Part (3) is also registered at `T = {𝔪}` over a Noetherian local ring, by
`Stacks.LocalCohomology.isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology_smul`. -/
theorem isMittagLefflerCategorical_localCohomologyAdicTower_of_stableImage
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{max u v} A) (s : ℤ)
    (hstab : HasStableImageIdealPowerCohomology.{u, v} T I M (s + 1) 0) :
    IsMittagLefflerCategorical (localCohomologyAdicTower.{u, v} A T I s M) := by
  refine isMittagLefflerCategorical_of_range_eq.{u, v} fun n => ?_
  obtain ⟨c, hnc, hc⟩ := hstab n (Nat.zero_le n)
  refine ⟨c, hnc, fun k hck =>
    (range_localCohomologyAdicTower_map_eq_of_stableImage.{u, v} T I M s (Nat.zero_le n)
        (hnc.trans hck)
        (localCohomologyδ_idealPowerShortComplex_zero_eq_zero.{u, v} T I M s (s + 1) rfl)
        (hc k hck)).trans
      (range_localCohomologyAdicTower_map_eq_of_stableImage.{u, v} T I M s (Nat.zero_le n) hnc
        (localCohomologyδ_idealPowerShortComplex_zero_eq_zero.{u, v} T I M s (s + 1) rfl)
        (hc c le_rfl)).symm⟩

/-- **The passage from the two conclusions of [Stacks, Tag 0EFX] to part (5) of
[Stacks, Tag 0EFY].** The comparison map
`H^s_T(M) → lim H^s_T(M/IⁿM)` is an isomorphism as soon as `{H^s_T(IⁿM)}` is pro-zero and
`{H^{s+1}_T(IⁿM)}` has stable images injecting into `H^{s+1}_T(I⁰M) = H^{s+1}_T(M)`.

In the source part (5) is the assertion for the module `I^{m₀}M` and its subquotients
`I^{m₀}M/IⁿM`; applied to `I^{m₀}M` the statement here is that assertion read along the cofinal
shift `n ↦ n + m₀`, as explained at
`isMittagLefflerCategorical_localCohomologyAdicTower_of_stableImage`.

*Argument.* Pro-zero in degree `s` gives, by part (1), an index beyond which the projections are
injective. Surjectivity onto the limit is
`range_localCohomologyAdicTower_map_eq_of_stableImage`: every member of a compatible family is a
transition image from an arbitrarily high level, hence lies in the image of `H^s_T(M)`.

*What this assumes, and why it carries no `@[stacks 0EFY]`.* The hypotheses `hpro` and `hstab` are
the two conclusions of Lemma [Stacks, Tag 0EFX], which in Situation [Stacks, Tag 0EFU] are
theorems and not restrictions on the data. This theorem is the engine; run on them it delivers
part (5) at a general specialization-stable `T`, in
`Stacks.Algebraization.isIso_limitLift_localCohomologyAdicCone_idealPowerSubmodule`. -/
theorem isIso_limitLift_localCohomologyAdicCone_of_stableImage (T : Set (PrimeSpectrum A))
    (I : Ideal A) (M : ModuleCat.{max u v} A) (s : ℤ)
    (hpro : IsProZeroIdealPowerCohomology.{u, v} T I M s)
    (hstab : HasStableImageIdealPowerCohomology.{u, v} T I M (s + 1) 0) :
    IsIso (limit.lift (localCohomologyAdicTower.{u, v} A T I s M)
      (localCohomologyAdicCone.{u, v} A T I s M)) := by
  obtain ⟨k₀, hinj⟩ := exists_forall_injective_proj_of_proZero.{u, v} T I M s hpro
  refine isIso_limitLift_of_jointlyInjective_of_surjective.{u, v} _
    (fun x y hxy => hinj k₀ le_rfl (hxy (op k₀))) fun y hy => ?_
  refine exists_proj_eq_of_forall_mem_range.{u, v} T I M s hinj y hy fun n => ?_
  obtain ⟨c, hnc, hc⟩ := hstab n (Nat.zero_le n)
  rw [← LinearMap.mem_range, ← range_localCohomologyAdicTower_map_eq_of_stableImage.{u, v} T I M s
    (Nat.zero_le n) hnc
    (localCohomologyδ_idealPowerShortComplex_zero_eq_zero.{u, v} T I M s (s + 1) rfl) (hc c le_rfl)]
  exact ⟨y (op c), hy (op c) (op n) (homOfLE hnc).op⟩

/-! #### Part (6): the comparison in degree `s` for `M` itself -/

/-- A transition image of a class coming from `H^i_T(M)` again comes from `H^i_T(M)`. -/
private theorem map_mem_range_proj (T : Set (PrimeSpectrum A)) (I : Ideal A) (i : ℤ)
    (M : ModuleCat.{max u v} A) {n m : ℕ} (h : n ≤ m)
    {w : (localCohomologyAdicTower.{u, v} A T I i M).obj (op m)}
    (hw : w ∈ LinearMap.range ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op m)).hom) :
    ((localCohomologyAdicTower.{u, v} A T I i M).map (homOfLE h).op).hom w ∈
      LinearMap.range ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom := by
  rw [LinearMap.mem_range] at hw
  obtain ⟨x, rfl⟩ := hw
  exact ⟨x, (localCohomologyAdicTower_map_proj.{u, v} T I i M h x).symm⟩

/-- An element of `I^{m₀}` annihilates `H^i_T(M/I^{m₀}M)`: it annihilates the identity of
`M/I^{m₀}M`, and `H^i_T` is `A`-linear. -/
theorem smul_eq_zero_localCohomologyAdicTower (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (i : ℤ) (M : ModuleCat.{max u v} A) (m₀ : ℕ) {a : A} (ha : a ∈ I ^ m₀)
    (w : (localCohomologyAdicTower.{u, v} A T I i M).obj (op m₀)) : a • w = 0 := by
  have h1 : a • 𝟙 ((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj
      ((idealPowerQuotientTower.{u, v} I M).obj (op m₀))) = 0 := by
    rw [← (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map_id
      ((idealPowerQuotientTower.{u, v} I M).obj (op m₀)), ← Functor.map_smul,
      smul_id_idealPowerQuotientTower_eq_zero.{u, v} I M (op m₀) ha,
      localCohomologyWithSupportInModuleFunctor_map_zero.{u, v} T i]
  exact congrArg (fun φ : (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj
      ((idealPowerQuotientTower.{u, v} I M).obj (op m₀)) ⟶
    (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj
      ((idealPowerQuotientTower.{u, v} I M).obj (op m₀)) => φ.hom w) h1

/-- **The key step of part (6).** If `{H^{s+1}_T(IⁿM)}` has stable images injecting into
`H^{s+1}_T(I^{m₀}M)` and `a ∈ I^{m₀}`, then `a` times any member of a compatible family in
`{H^s_T(M/IⁿM)}` at a level `n ≥ m₀` comes from `H^s_T(M)`.

*Argument.* The image of the member `yₙ` under the connecting map
`H^s_T(M/IⁿM) → H^{s+1}_T(IⁿM)` is, by naturality, a transition image of a class `d` at an
arbitrarily high level `c`. Naturality at `m₀ ≤ n` identifies the image of that class in
`H^{s+1}_T(I^{m₀}M)` with the connecting map applied to `y_{m₀}`, and `a` annihilates
`H^s_T(M/I^{m₀}M)`, so `a · d` has transition image dying in `H^{s+1}_T(I^{m₀}M)` and hence
vanishing. Therefore the connecting map kills `a · yₙ`, which by the long exact sequence puts
`a · yₙ` in the image of `H^s_T(M)`. -/
private theorem smul_mem_range_proj_of_stableImage (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (s : ℤ) {m₀ : ℕ}
    (hstab : HasStableImageIdealPowerCohomology.{u, v} T I M (s + 1) m₀) {a : A} (ha : a ∈ I ^ m₀)
    (y : ∀ n : ℕᵒᵖ, (localCohomologyAdicTower.{u, v} A T I s M).obj n)
    (hy : ∀ (m n : ℕᵒᵖ) (f : m ⟶ n),
      ((localCohomologyAdicTower.{u, v} A T I s M).map f).hom (y m) = y n)
    (n : ℕ) (hm₀n : m₀ ≤ n) :
    a • y (op n) ∈
      LinearMap.range ((localCohomologyAdicCone.{u, v} A T I s M).π.app (op n)).hom := by
  have hyT : ∀ {p q : ℕ} (h : q ≤ p),
      ((localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE h).op).hom (y (op p)) =
        y (op q) :=
    fun h => hy _ _ (homOfLE h).op
  have hyH : ∀ {p q : ℕ} (h : q ≤ p),
      ((localCohomologyWithSupportInModuleFunctor.{u, v} A T s).map
        ((idealPowerQuotientTower.{u, v} I M).map (homOfLE h).op)).hom (y (op p)) = y (op q) :=
    fun h => hy _ _ (homOfLE h).op
  obtain ⟨c, hnc, hc⟩ := hstab n hm₀n
  obtain ⟨d, hd⟩ := exists_localCohomologyδ_eq_map.{u, v} T I M s (hnc.trans (le_refl c))
    (y (op c))
  rw [hyT (hnc.trans (le_refl c))] at hd
  have hnat := apply_comp_eq_apply_comp.{u, v}
    (localCohomologyδ_idealPowerShortComplex_naturality.{u, v} T I M s (s + 1) rfl hm₀n)
    (y (op n))
  rw [hyH hm₀n] at hnat
  have hker : ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (s + 1)).map
      ((idealPowerTower.{u, v} I M).map (homOfLE (hnc.trans (le_refl c))).op)).hom (a • d) ∈
      LinearMap.ker ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (s + 1)).map
        ((idealPowerTower.{u, v} I M).map (homOfLE hm₀n).op)).hom := by
    rw [LinearMap.mem_ker]
    exact comp_hom_apply_smul_eq_zero.{u, v} _ _ _ hnat hd
      (smul_eq_zero_localCohomologyAdicTower.{u, v} T I s M m₀ ha _)
  have h0 := hc c (le_refl c) (a • d) hker
  have hδ0 := hom_apply_smul_eq_zero.{u, v} _ _ hd h0
  exact mem_range_proj_of_localCohomologyδ_eq_zero.{u, v} T I M s n hδ0

/-- **The passage from the two conclusions of [Stacks, Tag 0EFX] to part (6) of
[Stacks, Tag 0EFY].** There is an `m₀` such that
`H^s_T(M) → lim H^s_T(M/IⁿM)` is injective with cokernel killed by `I^{m₀}`, as soon as
`{H^s_T(IⁿM)}` is pro-zero and `{H^{s+1}_T(IⁿM)}` has stable images injecting into
`H^{s+1}_T(I^{m₀}M)` for some `m₀`; in Situation [Stacks, Tag 0EFU] both hypotheses hold. That
the cokernel is killed by `I^{m₀}` is said by: `a · z` lies in the image of the comparison map
for every `a ∈ I^{m₀}` and every `z` in the limit.

*Argument.* Injectivity is part (1) in degree `s`, transported along a projection of the limit.
For the cokernel, `smul_mem_range_proj_of_stableImage` puts `a · zₙ` in the image of `H^s_T(M)`
at every level `n ≥ m₀`, hence — by factoring a projection through level `max n m₀` — at every
level, and the resulting lifts glue by the injectivity of the projections.

*What this assumes, and why it carries no `@[stacks 0EFY]`.* The hypotheses `hpro` and `hstab` are
the two conclusions of Lemma [Stacks, Tag 0EFX], which in Situation [Stacks, Tag 0EFU] are
theorems and not restrictions on the data. This theorem is the engine; run on them it delivers
part (6) at a general specialization-stable `T`, in
`Stacks.Algebraization.exists_injective_limitLift_and_smul_mem_range`. -/
theorem exists_injective_limitLift_and_smul_mem_range (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (s : ℤ)
    (hpro : IsProZeroIdealPowerCohomology.{u, v} T I M s)
    (hstab : ∃ m₀ : ℕ, HasStableImageIdealPowerCohomology.{u, v} T I M (s + 1) m₀) :
    ∃ m₀ : ℕ,
      Function.Injective (limit.lift (localCohomologyAdicTower.{u, v} A T I s M)
          (localCohomologyAdicCone.{u, v} A T I s M)).hom ∧
        ∀ a ∈ I ^ m₀, ∀ z : (limit (localCohomologyAdicTower.{u, v} A T I s M) :
            ModuleCat.{max u v} A),
          a • z ∈ LinearMap.range (limit.lift (localCohomologyAdicTower.{u, v} A T I s M)
            (localCohomologyAdicCone.{u, v} A T I s M)).hom := by
  obtain ⟨k₀, hinj⟩ := exists_forall_injective_proj_of_proZero.{u, v} T I M s hpro
  obtain ⟨m₁, hstab⟩ := hstab
  refine ⟨max k₀ m₁, fun x₁ x₂ hx => ?_, fun a ha z => ?_⟩
  · refine hinj k₀ le_rfl ?_
    rw [← limit_π_limitLift.{u, v} _ (op k₀) x₁, ← limit_π_limitLift.{u, v} _ (op k₀) x₂]
    exact congrArg (limit.π (localCohomologyAdicTower.{u, v} A T I s M) (op k₀)).hom hx
  · have hstab' := hstab.mono.{u, v} (le_max_right k₀ m₁)
    have hw : ∀ (m n : ℕᵒᵖ) (f : m ⟶ n),
        ((localCohomologyAdicTower.{u, v} A T I s M).map f).hom
            ((limit.π (localCohomologyAdicTower.{u, v} A T I s M) m).hom z) =
          (limit.π (localCohomologyAdicTower.{u, v} A T I s M) n).hom z :=
      fun _ _ f => limit_π_map.{u, v} f z
    have hy : ∀ (m n : ℕᵒᵖ) (f : m ⟶ n),
        ((localCohomologyAdicTower.{u, v} A T I s M).map f).hom
            (a • (limit.π (localCohomologyAdicTower.{u, v} A T I s M) m).hom z) =
          a • (limit.π (localCohomologyAdicTower.{u, v} A T I s M) n).hom z :=
      fun m n f => by rw [map_smul, hw m n f]
    obtain ⟨x, hx⟩ := exists_proj_eq_of_forall_mem_range.{u, v} T I M s hinj
      (fun n => a • (limit.π (localCohomologyAdicTower.{u, v} A T I s M) n).hom z) hy
      (fun n => by
        have h1 := map_mem_range_proj.{u, v} T I s M (le_max_left n (max k₀ m₁))
          (smul_mem_range_proj_of_stableImage.{u, v} T I M s hstab' ha
            (fun p => (limit.π (localCohomologyAdicTower.{u, v} A T I s M) p).hom z) hw
            (max n (max k₀ m₁)) (le_max_right n (max k₀ m₁)))
        rwa [map_smul, hw (op (max n (max k₀ m₁))) (op n)
          (homOfLE (le_max_left n (max k₀ m₁))).op] at h1)
    exact ⟨x, Limits.Concrete.limit_ext _ _ _ fun n => by
      rw [limit_π_limitLift.{u, v} _ n x, hx n, map_smul]⟩

end Stacks.LocalCohomology

end
