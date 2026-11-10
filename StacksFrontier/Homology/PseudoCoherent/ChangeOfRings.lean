module

public import Mathlib
public import StacksFrontier.Homology.PseudoCoherent.Module
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence under change of rings

Let `A → B` be a homomorphism of rings.

Extension of scalars along a *flat* such homomorphism of *commutative* rings is exact, hence
carries `m`-pseudo-coherent and pseudo-coherent `A`-modules to `m`-pseudo-coherent and
pseudo-coherent `B`-modules.

Restriction of scalars along a homomorphism for which `B` is pseudo-coherent *as an `A`-module*
both preserves and reflects pseudo-coherence: a complex of `B`-modules is `m`-pseudo-coherent
over `B` if and only if its restriction of scalars is `m`-pseudo-coherent over `A`, and likewise
for pseudo-coherence.

## Main results

* `StacksDraft.PseudoCoherence.extensionScalars_preserves_pseudoCoherent`: flat extension of
  scalars preserves `m`-pseudo-coherence for every integer `m`, as well as pseudo-coherence,
  Stacks 066C.
* `StacksDraft.PseudoCoherence.pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars`: both
  equivalences under restriction of scalars along a map with pseudo-coherent target,
  Stacks 064Z.
* `StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits` and
  `StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits`: exactness of
  restriction of scalars along a homomorphism of possibly noncommutative rings.

## Implementation notes

Both alternatives of each source statement's "respectively" are combined into a conjunction.

For 066C the extension-of-scalars functor represents `B ⊗_A M`, canonically isomorphic to the
source's `M ⊗_A B` because the rings are commutative. The source allows an arbitrary flat ring
map, so the two coefficient rings have independent universes, as does the module carrier. The
transport itself is `exactFunctor_preserves_pseudoCoherent`; flatness enters only to supply
exactness of extension of scalars.

For 064Z the complex and its restriction of scalars are sent to their respective derived
categories by the localization functor. Both complexes use the common module universe
`max u v w`, which contains both rings and therefore the finite free modules needed to witness
pseudo-coherence on either side. The forward direction resolves the complex by a bounded
finite free approximation and transports it degreewise through Stacks 064Y; the reverse
direction is an induction on the width of the cohomological support, at each step splitting off
the top cohomology by a single finite free module and using the two-out-of-three property of
Stacks 064R.

Neither ring is assumed commutative for 064Z: the source states it for commutative rings, but
every step is about the `A`-module structures obtained by restriction, and pseudo-coherence,
`Module.Finite` and `Module.Free` are available over an arbitrary ring. The generality is used
by Stacks 0CSF, where `B` is the opposite ring of a possibly noncommutative algebra. Mathlib's
exactness instances for `ModuleCat.restrictScalars` assume commutative rings, so the two
instances needed are re-established here at the general signature.

## References

* [Stacks Project, Tag 064Z](https://stacks.math.columbia.edu/tag/064Z)
* [Stacks Project, Tag 066C](https://stacks.math.columbia.edu/tag/066C)
-/

@[expose] public section

-- Needed so that the single-complex normalisations below close by `rfl`.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.PseudoCoherence

universe u v w u₁

/-! ### Flat extension of scalars -/

/-- **Stacks 066C.** Extension of scalars along a flat ring homomorphism preserves
`m`-pseudo-coherent modules for every integer `m` and preserves pseudo-coherent modules. -/
@[stacks 066C]
theorem extensionScalars_preserves_pseudoCoherent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat)
    (M : ModuleCat.{w} A) :
    (∀ m : ℤ, IsModulePseudoCoherentFrom (R := A) M m →
      IsModulePseudoCoherentFrom (R := B) ((ModuleCat.extendScalars f).obj M) m) ∧
      (IsModulePseudoCoherent (R := A) M →
        IsModulePseudoCoherent (R := B) ((ModuleCat.extendScalars f).obj M)) := by
  let : Algebra A B := ((algebraMap B B).comp f).toAlgebra
  have : Module.Flat A B := hf
  let F := ModuleCat.extendScalars.{u, v, w} f
  have : F.Additive := by
    constructor
    intro X Y g h
    exact ModuleCat.hom_ext (LinearMap.baseChange_add (A := B) (f := g.hom) (g := h.hom))
  have hexact : ∀ S : ShortComplex (ModuleCat.{w} A), S.Exact → (S.map F).Exact := by
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact Module.Flat.lTensor_exact B hS
  have hlimits := ((Functor.exact_tfae F).out 2 4).mp hexact
  have : PreservesFiniteLimits F := hlimits.1
  have : PreservesFiniteColimits F := hlimits.2
  have hF : ∀ N : ModuleCat.{w} A, Module.Finite A N → Module.Free A N →
      Module.Finite B (F.obj N) ∧ Module.Free B (F.obj N) := by
    intro N hfinite hfree
    have := hfinite
    have := hfree
    change Module.Finite B (TensorProduct A B N) ∧ Module.Free B (TensorProduct A B N)
    exact ⟨inferInstance, inferInstance⟩
  have h := exactFunctor_preserves_pseudoCoherent F hF
    ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj M)
  let e := (F.mapDerivedCategorySingleFunctor 0).app M
  constructor
  · intro m hM
    obtain ⟨E, hE, α, hiso, hepi⟩ := h.1 m hM
    refine ⟨E, hE, α ≫ e.hom, ?_, ?_⟩
    · intro i hi
      rw [Functor.map_comp]
      have := hiso i hi
      infer_instance
    · rw [Functor.map_comp]
      infer_instance
  · intro hM
    obtain ⟨E, hE, ⟨eE⟩⟩ := h.2 hM
    exact ⟨E, hE, ⟨eE ≪≫ e⟩⟩

/-! ### Exactness of restriction of scalars -/

/-- Restriction of scalars along a homomorphism of possibly noncommutative rings carries exact
short complexes to exact short complexes: on underlying functions nothing changes. -/
theorem restrictScalars_shortComplex_exact {A : Type u} {B : Type v} [Ring A] [Ring B]
    (f : A →+* B) (S : ShortComplex (ModuleCat.{w} B)) (hS : S.Exact) :
    (S.map (ModuleCat.restrictScalars.{w} f)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact hS

/-- Restriction of scalars along a homomorphism of possibly noncommutative rings preserves finite
limits. Mathlib provides this only for commutative rings. -/
instance restrictScalars_preservesFiniteLimits {A : Type u} {B : Type v} [Ring A] [Ring B]
    (f : A →+* B) : PreservesFiniteLimits (ModuleCat.restrictScalars.{w} f) := by
  have h := ((Functor.exact_tfae (ModuleCat.restrictScalars.{w} f)).out 2 4).mp
    (restrictScalars_shortComplex_exact f)
  exact h.1

/-- Restriction of scalars along a homomorphism of possibly noncommutative rings preserves finite
colimits. Mathlib provides this only for commutative rings. -/
instance restrictScalars_preservesFiniteColimits {A : Type u} {B : Type v} [Ring A] [Ring B]
    (f : A →+* B) : PreservesFiniteColimits (ModuleCat.restrictScalars.{w} f) := by
  have h := ((Functor.exact_tfae (ModuleCat.restrictScalars.{w} f)).out 2 4).mp
    (restrictScalars_shortComplex_exact f)
  exact h.2

/-! ### Restriction of scalars: auxiliary transport lemmas -/

/-- An exact functor between module categories over the *same* ring which preserves finite free
modules preserves pseudo-coherence of modules. -/
private lemma modulePseudoCoherent_map {R : Type u} [Ring R]
    (F : ModuleCat.{v} R ⥤ ModuleCat.{w} R) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ M : ModuleCat.{v} R, Module.Finite R M → Module.Free R M →
      Module.Finite R (F.obj M) ∧ Module.Free R (F.obj M))
    (M : ModuleCat.{v} R) (hM : IsModulePseudoCoherent (R := R) M) :
    IsModulePseudoCoherent (R := R) (F.obj M) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hM
  obtain ⟨b, hb⟩ := hE.upperBound
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E,
    ⟨⟨b, inferInstance⟩, fun i ↦ hF _ (hE.finiteFree i).1 (hE.finiteFree i).2⟩,
    ⟨F.mapDerivedCategoryFactors.symm.app E ≪≫ F.mapDerivedCategory.mapIso e ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app M⟩⟩

/-- The functor sending an `R`-module `M` to the module `ι → M` of `ι`-indexed families. -/
private def powerFunctor (R : Type u) [Ring R] (ι : Type w) :
    ModuleCat.{v} R ⥤ ModuleCat.{max v w} R where
  obj M := ModuleCat.of R (ι → M)
  map f := ModuleCat.ofHom (f.hom.compLeft ι)

/-- Taking `ι`-indexed families is additive. -/
private lemma powerFunctor_additive (R : Type u) [Ring R] (ι : Type w) :
    (powerFunctor.{u, v, w} R ι).Additive where
  map_add := by intros; rfl

/-- Taking `ι`-indexed families is exact: a preimage may be chosen index by index. -/
private lemma powerFunctor_exact (R : Type u) [Ring R] (ι : Type w)
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.Exact) :
    letI := powerFunctor_additive.{u, v, w} R ι
    (S.map (powerFunctor.{u, v, w} R ι)).Exact := by
  classical
  have := powerFunctor_additive.{u, v, w} R ι
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x hx
  have h (i : ι) : ∃ y, S.f.hom y = x i := hS (x i) (congrFun hx i)
  exact ⟨fun i ↦ (h i).choose, funext fun i ↦ (h i).choose_spec⟩

/-- A finite power of a pseudo-coherent module is pseudo-coherent. -/
private lemma modulePseudoCoherent_power {R : Type u} [Ring R]
    (ι : Type w) [Finite ι] (M : ModuleCat.{v} R)
    (hM : IsModulePseudoCoherent (R := R) M) :
    IsModulePseudoCoherent (R := R) (ι → M) := by
  let F := powerFunctor.{u, v, w} R ι
  have : F.Additive := powerFunctor_additive R ι
  have h := ((Functor.exact_tfae F).out 2 4).mp (powerFunctor_exact R ι)
  have := h.1
  have := h.2
  apply modulePseudoCoherent_map F _ M hM
  intro N hfin hfree
  have := hfin
  have := hfree
  change Module.Finite R (ι → N) ∧ Module.Free R (ι → N)
  exact ⟨inferInstance, inferInstance⟩

/-- If `B` is pseudo-coherent as an `A`-module, then so is every finite free `B`-module: choose a
basis and identify it with a finite power of `B`. -/
private lemma modulePseudoCoherent_restrictScalars_free
    {A : Type u} {B : Type v} [Ring A] [Ring B] (f : A →+* B)
    (hB : IsModulePseudoCoherent (R := A)
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))
    (M : ModuleCat.{max u v w} B) [Module.Finite B M] [Module.Free B M] :
    IsModulePseudoCoherent (R := A) ((ModuleCat.restrictScalars f).obj M) := by
  classical
  let b := Module.Free.chooseBasis B M
  let N := (ModuleCat.restrictScalars f).obj (ModuleCat.of B B)
  have h := modulePseudoCoherent_power (Module.Free.ChooseBasisIndex B M) N hB
  let e : ((ModuleCat.restrictScalars f).obj M) ≃ₗ[A]
      (Module.Free.ChooseBasisIndex B M → N) :=
    { b.equivFun with
      map_smul' := fun a x ↦ b.equivFun.map_smul (f a) x }
  exact IsPseudoCoherent.ofIso h
    ((DerivedCategory.singleFunctor _ 0).mapIso e.symm.toModuleIso)

/-- The cone on an approximation which is an isomorphism on cohomology above `m` and surjective
in degree `m` has cohomology concentrated in degrees `≤ m - 1`. -/
private lemma cone_isLE_of_approximation
    {R : Type u} [Ring R]
    {E K : DerivedCategory (ModuleCat.{v} R)} {m : ℤ} (α : E ⟶ K)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map α)) :
    ∃ (C : DerivedCategory (ModuleCat.{v} R)) (β : K ⟶ C) (γ : C ⟶ E⟦1⟧),
      Triangle.mk α β γ ∈ distTriang _ ∧ C.IsLE (m - 1) := by
  obtain ⟨C, β, γ, hT⟩ := distinguished_cocone_triangle α
  let T := Triangle.mk α β γ
  refine ⟨C, β, γ, hT, ?_⟩
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hαepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α) := by
    rcases (show m ≤ i by omega).eq_or_lt with rfl | hlt
    · exact hepi
    · exact @IsIso.epi_of_iso _ _ _ _ _ (hiso i hlt)
  have hβ : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₂ = 0 :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 hαepi
  have hδα : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1) rfl).1
      (@IsIso.mono_of_iso _ _ _ _ _ (hiso (i + 1) (by omega)))
  exact (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl).isZero_of_both_zeros
    hβ hδα

/-- An `m`-pseudo-coherent object has cohomology bounded above. -/
private lemma pseudoCoherentFrom_boundedAbove {R : Type u} [Ring R]
    {K : DerivedCategory (ModuleCat.{v} R)} {m : ℤ}
    (hK : IsPseudoCoherentFrom K m) : ∃ n : ℤ, K.IsLE n := by
  obtain ⟨E, hE, α, hiso, hepi⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  refine ⟨max m b, (DerivedCategory.isLE_iff _ _).2 fun i hi ↦ ?_⟩
  have := hiso i (by omega)
  exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj E) b i (by omega)).of_iso
    (asIso ((DerivedCategory.homologyFunctor _ i).map α)).symm

/-- Cohomology in degrees `≤ m - 1` gives `m`-pseudo-coherence. -/
private lemma isPseudoCoherentFrom_of_isLE {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ) [K.IsLE (m - 1)] :
    IsPseudoCoherentFrom K m :=
  isPseudoCoherentFrom_of_homology_isZero K m fun i hi ↦
    DerivedCategory.isZero_of_isLE K (m - 1) i (by omega)

/-- An exact functor between module categories preserves the bound on cohomology. -/
@[sga "6 I 2.13" "Clause, special case"]
private lemma mapDerivedCategory_isLE {R : Type u} {S : Type u₁} [Ring R] [Ring S]
    (F : ModuleCat.{v} R ⥤ ModuleCat.{w} S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory (ModuleCat.{v} R)) (n : ℤ) [K.IsLE n] :
    (F.mapDerivedCategory.obj K).IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact (F.map_isZero (DerivedCategory.isZero_of_isLE K n i hi)).of_iso
    ((mapDerivedCategoryHomologyIso F i).app K)

/-- Restriction of scalars is faithful on vanishing of cohomology, so it detects the bound. -/
private lemma restrictScalars_isLE_iff
    {A : Type u} {B : Type v} [Ring A] [Ring B] (f : A →+* B)
    (K : DerivedCategory (ModuleCat.{w} B)) (n : ℤ) :
    ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsLE n ↔ K.IsLE n := by
  refine ⟨fun h ↦ (DerivedCategory.isLE_iff _ _).2 fun i hi ↦ ?_,
    fun _ ↦ mapDerivedCategory_isLE _ K n⟩
  have hz := (DerivedCategory.isZero_of_isLE _ n i hi).of_iso
    ((mapDerivedCategoryHomologyIso (ModuleCat.restrictScalars f) i).app K).symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hs := ModuleCat.isZero_iff_subsingleton.mp hz
  exact hs

/-- A `B`-module which is finite after restriction of scalars to `A` is finite over `B`. -/
private lemma finite_of_restrictScalars_finite
    {A : Type u} {B : Type v} [Ring A] [Ring B] (f : A →+* B)
    (M : ModuleCat.{w} B) [Module.Finite A ((ModuleCat.restrictScalars f).obj M)] :
    Module.Finite B M := by
  -- Only the scalar action of `A` on `B` through `f` is needed, so `B` need not be commutative
  -- and `f` need not be an algebra map.
  let : SMul A B := ⟨fun a b ↦ f a * b⟩
  have : IsScalarTower A B ((ModuleCat.restrictScalars f).obj M) :=
    ⟨fun a b x ↦ show (f a * b) • (x : M) = f a • b • (x : M) from mul_smul _ _ _⟩
  exact Module.Finite.of_restrictScalars_finite A B ((ModuleCat.restrictScalars f).obj M)

/-- An object with cohomology bounded above by `n` and finite top cohomology admits an
approximation by a finite free module placed in degree `n`. -/
private lemma exists_finiteFree_top_approximation_of_isLE
    {R : Type u} [Ring R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (n : ℤ) [K.IsLE n]
    [Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)] :
    ∃ E : CochainComplex (ModuleCat.{v} R) ℤ, IsBoundedFiniteFree E ∧
      ∃ α : DerivedCategory.Q.obj E ⟶ K,
        (∀ i : ℤ, n < i → IsIso ((DerivedCategory.homologyFunctor _ i).map α)) ∧
        Epi ((DerivedCategory.homologyFunctor _ n).map α) := by
  let L := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  let eh := (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).mapIso e.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).app L
  obtain ⟨P, hfin, hfree, p, hp⟩ := exists_finite_free_epi
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)
  obtain ⟨φ, hφ⟩ := exists_hom_from_single_of_projective L n P (p ≫ eh.hom)
  let E := (CochainComplex.singleFunctor (ModuleCat.{v} R) n).obj P
  refine ⟨E, isBoundedFiniteFree_single P n, DerivedCategory.Q.map φ ≫ e.hom, ?_, ?_⟩
  · intro i hi
    exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj E) n i hi).isIso
      (DerivedCategory.isZero_of_isLE K n i hi) _
  · rw [Functor.map_comp]
    have heq : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
        (DerivedCategory.Q.map φ) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).hom.app E ≫
        HomologicalComplex.homologyMap φ n ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).inv.app L := by
      simpa using (NatIso.naturality_2
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n) φ).symm
    rw [heq]
    infer_instance

/-! ### Restriction of scalars: the two directions -/

/-- Restriction of scalars of a bounded complex of finite free `B`-modules is `m`-pseudo-coherent
over `A`, by applying Stacks 064Y degreewise. -/
private lemma pseudoCoherent_restrictScalars_of_finiteFree
    {A : Type u} {B : Type v} [Ring A] [Ring B] (f : A →+* B)
    (hB : IsModulePseudoCoherent (R := A)
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))
    (E : CochainComplex (ModuleCat.{max u v w} B) ℤ)
    (hE : IsBoundedFiniteFree E) (m : ℤ) :
    IsPseudoCoherentFrom ((ModuleCat.restrictScalars f).mapDerivedCategory.obj
      (DerivedCategory.Q.obj E)) m := by
  let F := ModuleCat.restrictScalars.{max u v w} f
  obtain ⟨b, hb⟩ := hE.upperBound
  refine (pseudoCoherent_iff_all _).mp ?_ m
  apply IsPseudoCoherent.ofIso _ (F.mapDerivedCategoryFactors.app E).symm
  apply (pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ⟨b, inferInstance⟩).2
  intro i
  have := (hE.finiteFree i).1
  have := (hE.finiteFree i).2
  exact modulePseudoCoherent_restrictScalars_free f hB (E.X i)

/-- Restriction of scalars preserves `m`-pseudo-coherence. -/
private lemma pseudoCoherentFrom_restrictScalars
    {A : Type u} {B : Type v} [Ring A] [Ring B] (f : A →+* B)
    (hB : IsModulePseudoCoherent (R := A)
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))
    (K : DerivedCategory (ModuleCat.{max u v w} B)) (m : ℤ)
    (hK : IsPseudoCoherentFrom K m) :
    IsPseudoCoherentFrom ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K) m := by
  let F := ModuleCat.restrictScalars.{max u v w} f
  obtain ⟨E, hE, α, hiso, hepi⟩ := hK
  obtain ⟨C, β, γ, hT, hC⟩ := cone_isLE_of_approximation α hiso hepi
  let T := Triangle.mk α β γ
  apply _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m
    (F.mapDerivedCategory.mapTriangle.obj T) (F.mapDerivedCategory.map_distinguished T hT)
  · exact pseudoCoherent_restrictScalars_of_finiteFree f hB E hE m
  · change IsPseudoCoherentFrom (F.mapDerivedCategory.obj C) m
    have := mapDerivedCategory_isLE F C (m - 1)
    exact isPseudoCoherentFrom_of_isLE _ m

/-- Restriction of scalars reflects `m`-pseudo-coherence, by induction on the width `d` of the
cohomological support above `m - 1`. -/
private lemma pseudoCoherentFrom_of_restrictScalars_bounded
    {A : Type u} {B : Type v} [Ring A] [Ring B] (f : A →+* B)
    (hB : IsModulePseudoCoherent (R := A)
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) (m : ℤ) :
    ∀ d : ℕ, ∀ K : DerivedCategory (ModuleCat.{max u v w} B),
      K.IsLE (m - 1 + d) →
      IsPseudoCoherentFrom ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K) m →
      IsPseudoCoherentFrom K m := by
  let F := ModuleCat.restrictScalars.{max u v w} f
  intro d
  induction d with
  | zero =>
      intro K hbound hK
      have : K.IsLE (m - 1) := by simpa using hbound
      exact isPseudoCoherentFrom_of_isLE K m
  | succ d ih =>
      intro K hbound hK
      let n : ℤ := m - 1 + (d + 1 : ℕ)
      have : K.IsLE n := hbound
      have hle : (F.mapDerivedCategory.obj K).IsLE n := mapDerivedCategory_isLE F K n
      have hfinA := _root_.PseudoCoherence.finite_homology_of_isPseudoCoherentFrom
        (F.mapDerivedCategory.obj K) n (hK.mono (by dsimp [n]; omega))
        (fun i hi ↦ DerivedCategory.isZero_of_isLE _ n i hi)
      let e := (mapDerivedCategoryHomologyIso F n).app K
      have : Module.Finite A (F.obj ((DerivedCategory.homologyFunctor _ n).obj K)) :=
        (Module.Finite.equiv_iff e.toLinearEquiv).mp hfinA
      have := finite_of_restrictScalars_finite f ((DerivedCategory.homologyFunctor _ n).obj K)
      obtain ⟨E, hE, α, hiso, hepi⟩ := exists_finiteFree_top_approximation_of_isLE K n
      obtain ⟨C, β, γ, hT, hC⟩ := cone_isLE_of_approximation α hiso hepi
      let T := Triangle.mk α β γ
      have hEC : IsPseudoCoherent (DerivedCategory.Q.obj E) :=
        ⟨E, ⟨hE.upperBound, hE.finiteFree⟩, ⟨Iso.refl _⟩⟩
      have hCA : IsPseudoCoherentFrom (F.mapDerivedCategory.obj C) m :=
        _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_one m
          (F.mapDerivedCategory.mapTriangle.obj T)
          (F.mapDerivedCategory.map_distinguished T hT)
          (pseudoCoherent_restrictScalars_of_finiteFree f hB E hE (m + 1)) hK
      have hCbound : C.IsLE (m - 1 + d) := by
        have hn : n - 1 = m - 1 + d := by dsimp [n]; omega
        rwa [hn] at hC
      exact _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m T hT
        ((pseudoCoherent_iff_all _).mp hEC m) (ih C hCbound hCA)

/-- Restriction of scalars reflects `m`-pseudo-coherence. -/
private lemma pseudoCoherentFrom_of_restrictScalars
    {A : Type u} {B : Type v} [Ring A] [Ring B] (f : A →+* B)
    (hB : IsModulePseudoCoherent (R := A)
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))
    (K : DerivedCategory (ModuleCat.{max u v w} B)) (m : ℤ)
    (hK : IsPseudoCoherentFrom ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K) m) :
    IsPseudoCoherentFrom K m := by
  obtain ⟨n, hn⟩ := pseudoCoherentFrom_boundedAbove hK
  have hKn := (restrictScalars_isLE_iff f K n).mp hn
  let d : ℕ := (n - (m - 1)).toNat
  have hbound : K.IsLE (m - 1 + d) := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact DerivedCategory.isZero_of_isLE K n i (by dsimp [d] at hi; omega)
  exact pseudoCoherentFrom_of_restrictScalars_bounded f hB m d K hbound hK

/-- **Stacks 064Z.** If `B` is pseudo-coherent as an `A`-module, restriction of scalars along
`A → B` preserves and reflects both `m`-pseudo-coherence and pseudo-coherence of complexes. -/
@[stacks 064Z, sga "6 III 1.12" "affine case, X = Y"]
theorem pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars
    {A : Type u} {B : Type v} [Ring A] [Ring B] (f : A →+* B)
    (hB : IsModulePseudoCoherent (R := A)
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))
    (K : CochainComplex (ModuleCat.{max u v w} B) ℤ) (m : ℤ) :
    let Kₐ := ((ModuleCat.restrictScalars.{max u v w} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    (IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m ↔
      IsPseudoCoherentFrom (DerivedCategory.Q.obj Kₐ) m) ∧
    (IsPseudoCoherent (DerivedCategory.Q.obj K) ↔
      IsPseudoCoherent (DerivedCategory.Q.obj Kₐ)) := by
  let F := ModuleCat.restrictScalars.{max u v w} f
  have h (n : ℤ) : IsPseudoCoherentFrom (DerivedCategory.Q.obj K) n ↔
      IsPseudoCoherentFrom (DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) n :=
    ⟨fun hK ↦ (pseudoCoherentFrom_restrictScalars f hB _ n hK).ofIso
        (F.mapDerivedCategoryFactors.app K),
      fun hK ↦ pseudoCoherentFrom_of_restrictScalars f hB _ n
        (hK.ofIso (F.mapDerivedCategoryFactors.app K).symm)⟩
  refine ⟨h m, ?_⟩
  rw [pseudoCoherent_iff_all, pseudoCoherent_iff_all]
  exact forall_congr' h

end StacksDraft.PseudoCoherence
