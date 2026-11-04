module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Module
public import StacksCore.Algebra.Category.ModuleCat.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Essential
public import StacksFrontier.Algebra.Module.InjectiveHull.Injective

/-!
# Injective hulls

An *injective hull* of an object `M` is an essential monomorphism `M ⟶ I` with `I` injective:
`I` is injective, and every nonzero subobject of `I` meets the image of `M`. This file develops
the basic theory of injective hulls of modules: their existence, their uniqueness up to
isomorphism, and the intrinsic characterization of injectivity by triviality of essential
extensions.

The main thread is the following. An injective hull is unique up to an isomorphism compatible
with the two embeddings, and it is a direct summand of any injective module containing the
original one. A module is injective exactly when it admits no proper essential extension; for a
submodule of an injective module it suffices to test essential extensions inside the ambient
module. Zorn's lemma applied to the essential extensions of a module inside an injective module
containing it produces a maximal one, which is therefore injective: this is the existence of
injective hulls.

## Main definitions

* `Module.IsInjectiveHull` — a monomorphism is an injective hull when its codomain is injective
  and it is an essential monomorphism.

## Main results

* `Module.exists_isInjectiveHull` — every module has an injective hull.
* `Module.exists_iso_of_isInjectiveHull` — two injective hulls of the same object are isomorphic
  compatibly with their embeddings.
* `Module.exists_iso_biprod_of_isInjectiveHull` — an injective hull is a direct summand of any
  injective module containing the original module.
* `Module.injective_iff_isIso_essentialMono` — a module is injective exactly when every essential
  monomorphism out of it is an isomorphism.
* `Module.injective_iff_eq_of_essential_extension` — a submodule of an injective module is
  injective exactly when it has no proper essential extension inside the ambient module.
* `Module.isInjectiveHull_fractionRing` — a domain sits in its fraction field as an injective
  hull.

## References

* [Stacks Project, Tag 08XS](https://stacks.math.columbia.edu/tag/08XS)
* [Stacks Project, Tag 08Y2](https://stacks.math.columbia.edu/tag/08Y2)
* [Stacks Project, Tag 08Y3](https://stacks.math.columbia.edu/tag/08Y3)
* [Stacks Project, Tag 08Y4](https://stacks.math.columbia.edu/tag/08Y4)
* [Stacks Project, Tag 08Y5](https://stacks.math.columbia.edu/tag/08Y5)
* [Stacks Project, Tag 08Y8](https://stacks.math.columbia.edu/tag/08Y8)
-/

@[expose] public section

open CategoryTheory

namespace Module

universe u v w

/-! ### Injective hulls -/

/-- An injective hull is an essential monomorphism into an injective object. -/
@[stacks 08Y2] abbrev IsInjectiveHull {𝒜 : Type u} [Category.{v} 𝒜]
    [Limits.HasZeroObject 𝒜] [Limits.HasPullbacks 𝒜] {M I : 𝒜} (i : M ⟶ I) [Mono i] : Prop :=
  CategoryTheory.Injective I ∧ IsEssentialMono i

/-- Injectivity of a module transports along a linear equivalence. -/
public theorem injective_of_linearEquiv {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : Module.Injective R M) : Module.Injective R N := by
  refine ⟨?_⟩
  intro X Y _ _ _ _ f hf g
  obtain ⟨h, hh⟩ := Module.Injective.out (R := R) (Q := M) f hf (e.symm.toLinearMap.comp g)
  refine ⟨e.toLinearMap.comp h, ?_⟩
  intro x
  show e (h (f x)) = g x
  rw [hh x]
  exact e.apply_symm_apply _

/-- Essentiality only depends on the subobject cut out by a monomorphism. -/
lemma essential_congr_subobject_eq {C : Type*} [Category C]
    [Limits.HasZeroObject C] [Limits.HasPullbacks C]
    {A B D : C} (f : A ⟶ D) (g : B ⟶ D) [Mono f] [Mono g]
    (h : Subobject.mk f = Subobject.mk g) :
    IsEssentialMono f ↔ IsEssentialMono g := by
  show (∀ B' : Subobject D, B' ≠ ⊥ → B' ⊓ Subobject.mk f ≠ ⊥) ↔ _
  rw [h]

/-- An isomorphism is an essential monomorphism. -/
private lemma essential_of_iso {C : Type*} [Category C]
    [Limits.HasZeroObject C] [Limits.HasPullbacks C]
    {A B : C} (f : A ⟶ B) [Mono f] [IsIso f] : IsEssentialMono f := by
  intro B' hB'
  simpa [(Subobject.isIso_iff_mk_eq_top f).mp (inferInstance : IsIso f)] using hB'

/-- An inclusion of submodules is essential precisely when every nonzero element of the larger
submodule has a nonzero multiple in the smaller one. -/
private lemma essential_inclusion_iff_elementwise {R : Type u} [Ring R]
    {I : Type v} [AddCommGroup I] [Module R I]
    (E₀ E : Submodule R I) (h : E₀ ≤ E)
    [Mono (ModuleCat.ofHom (Submodule.inclusion h))] :
    IsEssentialMono (ModuleCat.ofHom (Submodule.inclusion h)) ↔
      ∀ x : E, x ≠ 0 → ∃ r : R, r • (x : I) ∈ E₀ ∧ r • (x : I) ≠ 0 := by
  let F : Submodule R E := Submodule.comap E.subtype E₀
  let e : E₀ ≃ₗ[R] F := (Submodule.comapSubtypeEquivOfLe h).symm
  let g : ModuleCat.of R F ⟶ ModuleCat.of R E := ModuleCat.ofHom F.subtype
  let : Mono g := (ModuleCat.mono_iff_injective g).mpr F.subtype_injective
  let f : ModuleCat.of R E₀ ⟶ ModuleCat.of R E :=
    ModuleCat.ofHom (Submodule.inclusion h)
  let : Mono f := (ModuleCat.mono_iff_injective f).mpr
    (Submodule.inclusion_injective h)
  have heq : ModuleCat.ofHom (Submodule.inclusion h) =
      ModuleCat.ofHom e.toLinearMap ≫ g := by
    ext x
    simp [g, e, F, Submodule.comapSubtypeEquivOfLe]
  have hmk : Subobject.mk (ModuleCat.ofHom (Submodule.inclusion h)) =
      Subobject.mk g := Subobject.mk_eq_mk_of_comm _ _ e.toModuleIso heq.symm
  rw [essential_congr_subobject_eq (ModuleCat.ofHom (Submodule.inclusion h)) g hmk]
  show IsEssentialMono (ModuleCat.ofHom F.subtype) ↔ _
  rw [isEssentialMono_subtype_iff (R := R) (N := ModuleCat.of R E) F]
  constructor
  · intro hx x hx0
    obtain ⟨r, hrF, hr0⟩ := hx x hx0
    refine ⟨r, by simpa [F, Submodule.mem_comap] using hrF, ?_⟩
    intro hz
    exact hr0 (Subtype.ext (by simpa using hz))
  · intro hx x hx0
    obtain ⟨r, hrE₀, hr0⟩ := hx x hx0
    refine ⟨r, by simpa [F, Submodule.mem_comap] using hrE₀, ?_⟩
    intro hz
    exact hr0 (by simpa using congrArg (fun z : E => (z : I)) hz)


/-! ### Extending a map to an injective object

A morphism into an injective object extends along any monomorphism. In particular, a morphism
between the sources of two injective hulls extends to a morphism between the hulls; only
injectivity of the target hull is needed, so the existing categorical declarations state the
result more generally. -/

add_to_stacks 08Y4 "extend_map" CategoryTheory.Injective.factorThru
add_to_stacks 08Y4 "extend_map" CategoryTheory.Injective.comp_factorThru

/-! ### Morphisms between injective hulls -/

/-- A morphism which is monic on an essential subobject is a monomorphism. -/
@[stacks 08Y4 "injective_extension"]
theorem mono_of_isEssentialMono_of_comp_eq {C : Type u} [Category.{v} C] [Abelian C]
    {M E N J : C} (i : M ⟶ E) [Mono i] (hi : IsEssentialMono i) (φ : M ⟶ N) [Mono φ]
    (j : N ⟶ J) [Mono j] (ψ : E ⟶ J) (hψ : i ≫ ψ = φ ≫ j) : Mono ψ :=
  have : Mono (i ≫ ψ) := hψ ▸ inferInstance
  mono_of_isEssentialMono_of_comp_mono i ψ hi

/-- A morphism between injective hulls which extends an essential monomorphism is an isomorphism. -/
@[stacks 08Y4 "essential_extension_iso"]
theorem isIso_of_isInjectiveHull_of_isEssentialMono
    {C : Type u} [Category.{v} C] [Abelian C]
    {M E N E' : C} (i : M ⟶ E) (j : N ⟶ E')
    [Mono i] [Mono j]
    (hi : IsInjectiveHull i)
    (hj : IsInjectiveHull j)
    (phi : M ⟶ N) [Mono phi]
    (hphi : IsEssentialMono phi)
    (psi : E ⟶ E') (hpsi : i ≫ psi = phi ≫ j) :
    IsIso psi := by
  let : Mono psi := mono_of_isEssentialMono_of_comp_eq i hi.2 phi j psi hpsi
  let : CategoryTheory.Injective E := hi.1
  let r : E' ⟶ E := Injective.factorThru (𝟙 E) psi
  have hpsi_r : psi ≫ r = 𝟙 E := Injective.comp_factorThru (𝟙 E) psi
  have : Mono ((phi ≫ j) ≫ r) := by
    rw [← hpsi, Category.assoc, hpsi_r, Category.comp_id]
    infer_instance
  have : Mono r :=
    mono_of_isEssentialMono_of_comp_mono (phi ≫ j) r (isEssentialMono_comp phi j hphi hj.2)
  exact IsIso.of_mono_retraction' ⟨r, hpsi_r⟩

/-- A morphism between injective hulls which extends an isomorphism of the embedded modules is an
isomorphism. -/
@[stacks 08Y4 "iso_extension"]
lemma isIso_of_isInjectiveHull_of_extends_iso
    {C : Type u} [Category.{v} C] [Abelian C] {M N E E' : C}
    (i : M ⟶ E) (j : N ⟶ E') [Mono i] [Mono j]
    (hi : IsInjectiveHull i)
    (hj : IsInjectiveHull j)
    (e : M ≅ N) (f : E ⟶ E')
    (comm : i ≫ f = e.hom ≫ j) :
    IsIso f := isIso_of_isInjectiveHull_of_isEssentialMono
    i j hi hj e.hom (essential_of_iso e.hom) f comm

/-- Any two injective hulls of an object are isomorphic compatibly with their embeddings of that
object. -/
@[stacks 08Y4 "unique_up_to_iso"]
lemma exists_iso_of_isInjectiveHull {𝒜 : Type u} [Category.{v} 𝒜]
    [Abelian 𝒜]
    {M I J : 𝒜} (i : M ⟶ I) (j : M ⟶ J) [Mono i] [Mono j]
    (hi : IsInjectiveHull i) (hj : IsInjectiveHull j) :
    ∃ e : I ≅ J, i ≫ e.hom = j := by
  have : CategoryTheory.Injective J := hj.1
  have : IsIso (Injective.factorThru j i) :=
    isIso_of_isInjectiveHull_of_extends_iso i j hi hj (Iso.refl M) _ (by simp)
  exact ⟨asIso (Injective.factorThru j i), Injective.comp_factorThru j i⟩

/-- An injective hull is a direct summand of any injective module containing the original module,
compatibly with the two embeddings. -/
@[stacks 08Y4 "splits_in_injective"]
lemma exists_iso_biprod_of_isInjectiveHull
    {R : Type u} [Ring R] {M E I : ModuleCat.{v} R}
    (i : M ⟶ E) [Mono i] (hi : IsInjectiveHull i)
    (j : M ⟶ I) [Mono j] [CategoryTheory.Injective I] :
    ∃ I' : ModuleCat.{v} R, ∃ e : I ≅ E ⊞ I',
      j ≫ e.hom = i ≫ Limits.biprod.inl := by
  obtain ⟨f, hf⟩ := Injective.factors j i
  have : Mono (i ≫ f) := hf ▸ inferInstance
  have : Mono f := mono_of_isEssentialMono_of_comp_mono i f hi.2
  have : Module.Injective R E := Module.injective_module_of_injective_object R E (inj := hi.1)
  obtain ⟨K, e, he⟩ := exists_linearEquiv_prod_of_injective
    f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance)
  refine ⟨_, e.toModuleIso ≪≫ (ModuleCat.biprodIsoProd E (ModuleCat.of R K)).symm, ?_⟩
  apply Limits.biprod.hom_ext <;> ext x <;> simp [Category.assoc, ← hf, he]

/-! ### Fraction fields as injective hulls

The fraction field is represented by an arbitrary field `K` satisfying `IsFractionRing R K`. To
allow `R` and `K` in independent universes, the domain is represented by the range of the
canonical algebra map in `K`, canonically isomorphic to `R`; the inclusion is the submodule's
subtype map. -/

/-- The canonical inclusion of a domain into its fraction field is an injective hull. -/
@[stacks 08Y5]
theorem isInjectiveHull_fractionRing
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :
    let M : Submodule R K := (Algebra.linearMap R K).range
    let i : ModuleCat.of R M ⟶ ModuleCat.of R K :=
      ModuleCat.ofHom M.subtype
    letI : Mono i :=
      (ModuleCat.mono_iff_injective i).2 M.injective_subtype
    IsInjectiveHull i := by
  dsimp only [IsInjectiveHull]
  constructor
  · have : IsLocalization (⊥ : Ideal R).primeCompl K :=
      (Ideal.primeCompl_bot (α := R)).symm ▸
        (inferInstance : IsLocalization (nonZeroDivisors R) K)
    have hp : (⊥ : Ideal R) ∈ minimalPrimes R := by
      simp [IsDomain.minimalPrimes_eq_singleton_bot]
    have hloc : Module.Injective R (Localization.AtPrime (⊥ : Ideal R)) :=
      injective_localizationAtPrime_of_minimal (⊥ : Ideal R) hp
    let e : K ≃ₐ[R] Localization.AtPrime (⊥ : Ideal R) :=
      IsLocalization.algEquiv (⊥ : Ideal R).primeCompl K _
    have : Module.Injective R K :=
      Module.Injective.of_ringEquiv (RingEquiv.refl R) e.symm.toLinearEquiv
    exact Module.injective_object_of_injective_module R K
  · apply (isEssentialMono_subtype_iff
      (N := ModuleCat.of R K) ((Algebra.linearMap R K).range)).2
    intro x hx
    obtain ⟨a, ha⟩ := IsLocalization.surj (nonZeroDivisors R) x
    refine ⟨a.2, ?_, ?_⟩
    · rw [Algebra.smul_def]
      show algebraMap R K a.2 * x ∈ (Algebra.linearMap R K).range
      refine ⟨a.1, ?_⟩
      show algebraMap R K a.1 = algebraMap R K a.2 * x
      exact ha.symm.trans (mul_comm _ _)
    · rw [Algebra.smul_def]
      show algebraMap R K a.2 * x ≠ 0
      exact mul_ne_zero
        ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2
          (mem_nonZeroDivisors_iff_ne_zero.mp a.2.2)) hx

/-! ### The injective hull of a residue field

Let `p` be a prime ideal of a commutative ring `R`. If an `R`-module `E` is an injective hull of
`R ⧸ p`, then it is also an injective hull of the residue field of `p`. Since an injective hull is
represented by its essential monomorphism, the conclusion supplies an essential monomorphism from
the residue field into the same module `E`. -/

/-- An injective hull of the quotient by a prime ideal is also an injective hull of the prime's
residue field. -/
@[stacks 08Y8 "hull_of_residue_field"]
theorem exists_isInjectiveHull_residueField_of_quotient
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (E : ModuleCat.{max u v} R)
    (i : ModuleCat.of R (ULift.{v} (R ⧸ p)) ⟶ E) [Mono i]
    (hi : IsInjectiveHull i) :
    ∃ (j : ModuleCat.of R (ULift.{v} p.ResidueField) ⟶ E) (_ : Mono j),
      IsInjectiveHull j := by
  let phi : ModuleCat.of R (ULift.{v} (R ⧸ p)) ⟶
      ModuleCat.of R (ULift.{v} p.ResidueField) := ModuleCat.ofHom
    { toFun := fun x ↦ ULift.up (algebraMap (R ⧸ p) p.ResidueField x.down)
      map_add' := by intro x y; apply ULift.down_injective; simp
      map_smul' := by
        intro r x; apply ULift.down_injective
        simp [Algebra.smul_def, Ideal.algebraMap_quotient_residueField_mk] }
  have hphi : Function.Injective phi := by
    intro x y h; exact ULift.down_injective
      (p.injective_algebraMap_quotient_residueField (congrArg ULift.down h))
  let : Mono phi := (ModuleCat.mono_iff_injective phi).mpr hphi
  let : CategoryTheory.Injective E := hi.1
  let j := Injective.factorThru i phi
  have hij : phi ≫ j = i := Injective.comp_factorThru i phi
  have hj : Function.Injective j := by
    intro x y hxy
    have hx : j (x - y) = 0 := by simp [map_sub, hxy]
    obtain ⟨a, b, hb, hab⟩ :=
      IsFractionRing.div_surjective (R ⧸ p) (x - y).down
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hscalar : r • (x - y) = phi (ULift.up a) := by
      apply ULift.down_injective
      dsimp [phi]; simp only [Algebra.smul_def]
      show algebraMap R p.ResidueField r * (x - y).down =
        algebraMap (R ⧸ p) p.ResidueField a
      rw [← hab, ← Ideal.algebraMap_quotient_residueField_mk (I := p) r,
        div_eq_mul_inv, mul_comm
        (algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p r)), mul_assoc,
        inv_mul_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb), mul_one]
    have ha : (ULift.up a : ULift.{v} (R ⧸ p)) = 0 := by
      apply (ModuleCat.mono_iff_injective i).mp inferInstance
      have : j (phi (ULift.up a)) = 0 := by rw [← hscalar, map_smul, hx, smul_zero]
      rw [← hij]
      show j (phi (ULift.up a)) = j (phi 0)
      simpa using this
    apply sub_eq_zero.mp
    apply ULift.down_injective
    rw [← hab]
    have : a = 0 := congrArg ULift.down ha
    simp [this]
  let : Mono j := (ModuleCat.mono_iff_injective j).mpr hj
  exact ⟨j, inferInstance, hi.1, fun B' hB' h ↦ hi.2 B' hB'
    (le_bot_iff.1 ((inf_le_inf_left B' (Subobject.mk_le_mk_of_comm phi hij)).trans h.le))⟩

/-! ### Injective modules and essential extensions

An injective submodule of an injective module admits no proper essential extension inside the
ambient module; conversely, this property characterizes injective submodules. Intrinsically, a
module is injective exactly when every essential extension of it is trivial. An inclusion of
submodules is regarded as a morphism in `ModuleCat`; in the intrinsic formulation, saying that an
extension is trivial means that its essential monomorphism is an isomorphism. -/

/-- A maximal submodule disjoint from a given one exists. -/
private lemma exists_maximal_disjoint {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M] (A : Submodule R M) :
    ∃ C : Submodule R M, Disjoint A C ∧
      ∀ D : Submodule R M, C ≤ D → Disjoint A D → D = C := by
  obtain ⟨C, -, hC, hmax⟩ := zorn_le_nonempty₀
    {C : Submodule R M | Disjoint A C} (fun c hc hchain y hy ↦ by
      refine ⟨sSup c, ?_, fun _ hz ↦ le_sSup hz⟩
      exact hchain.directedOn.disjoint_sSup_right.2 (fun z hz ↦ hc hz))
    ⊥ disjoint_bot_right
  exact ⟨C, hC, fun D hCD hD ↦ (hmax hD hCD).antisymm hCD⟩

/-- A split essential monomorphism is an isomorphism. -/
private lemma isIso_of_essentialMono_of_retraction
    {R : Type u} [Ring R] {A B : ModuleCat.{v} R}
    (i : A ⟶ B) [Mono i] (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (hi : IsEssentialMono i) : IsIso i := by
  have : Mono r := mono_of_isEssentialMono_of_comp_eq
    i hi (𝟙 A) (𝟙 A) r (by simpa using hir)
  have : IsSplitEpi r := IsSplitEpi.mk' ⟨i, hir⟩
  have : IsIso r := isIso_of_mono_of_isSplitEpi r
  exact isIso_of_comp_hom_eq_id r hir

/-- An essential monomorphism out of an injective module is an isomorphism. -/
private lemma isIso_of_essentialMono_of_injective
    {R : Type u} [Ring R] {A B : ModuleCat.{v} R} [CategoryTheory.Injective A]
    (i : A ⟶ B) [Mono i] (hi : IsEssentialMono i) : IsIso i :=
  isIso_of_essentialMono_of_retraction i (Injective.factorThru (𝟙 A) i)
    (Injective.comp_factorThru _ _) hi

/-- A monomorphism of modules is essential precisely when the inclusion of its range is. -/
lemma isEssentialMono_iff_range
    {R : Type u} [Ring R] {A B : ModuleCat.{v} R}
    (i : A ⟶ B) [Mono i] : IsEssentialMono i ↔
      IsEssentialMono (ModuleCat.ofHom (LinearMap.range i.hom).subtype) := by
  let e : A ≅ ModuleCat.of R (LinearMap.range i.hom) :=
    LinearEquiv.toModuleIso (LinearEquiv.ofInjective i.hom
      ((ModuleCat.mono_iff_injective i).1 inferInstance))
  have he : e.hom ≫ ModuleCat.ofHom (LinearMap.range i.hom).subtype = i := by
    ext x
    rfl
  have hm := Subobject.mk_eq_mk_of_comm i
    (ModuleCat.ofHom (LinearMap.range i.hom).subtype) e he
  show (∀ B' : Subobject B, B' ≠ ⊥ → B' ⊓ Subobject.mk i ≠ ⊥) ↔ _
  rw [hm]

/-- Any monomorphism of modules becomes essential after dividing the target by a submodule
maximally disjoint from the image. -/
private lemma exists_essential_quotient {R : Type u} [Ring R]
    {A B : ModuleCat.{v} R} (i : A ⟶ B) [Mono i] :
    ∃ (P : ModuleCat.{v} R) (q : B ⟶ P),
      ∃ _ : Mono (i ≫ q), IsEssentialMono (i ≫ q) := by
  let U : Submodule R B := LinearMap.range i.hom
  obtain ⟨C, hUC, hC⟩ := exists_maximal_disjoint U
  let P : ModuleCat.{v} R := ModuleCat.of R (B ⧸ C)
  let q : B ⟶ P := ModuleCat.ofHom C.mkQ
  have hk : Function.Injective (i ≫ q) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hixC : i x ∈ C := by
      rw [← Submodule.ker_mkQ C]
      exact hx
    have hixU : i x ∈ U := LinearMap.mem_range_self i.hom x
    have : i x = 0 := (Submodule.mem_bot R).1 (hUC.le_bot ⟨hixU, hixC⟩)
    exact (ModuleCat.mono_iff_injective i).1 inferInstance (by simpa using this)
  let : Mono (i ≫ q) := (ModuleCat.mono_iff_injective _).2 hk
  refine ⟨P, q, inferInstance, ?_⟩
  apply (isEssentialMono_iff_range (i ≫ q)).2
  rw [isEssentialMono_subtype_iff]
  intro x hx
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C x
  have hbC : b ∉ C := fun hb => hx ((Submodule.Quotient.mk_eq_zero C).2 hb)
  have hnot : ¬ Disjoint U (C ⊔ R ∙ b) := by
    intro hd
    have heq := hC (C ⊔ R ∙ b) le_sup_left hd
    apply hbC
    rw [← heq]
    exact (show R ∙ b ≤ C ⊔ R ∙ b from le_sup_right)
      (Submodule.subset_span (by simp))
  have hmeet : U ⊓ (C ⊔ R ∙ b) ≠ ⊥ := by
    simpa [disjoint_iff_inf_le] using hnot
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmeet
  rcases hy with ⟨hyU, hyD⟩
  have hyU' := hyU
  rcases hyU with ⟨z, hz⟩
  rcases Submodule.mem_sup.1 hyD with ⟨c, hc, d, hd, hcd⟩
  rcases Submodule.mem_span_singleton.mp hd with ⟨a, rfl⟩
  refine ⟨a, ?_, ?_⟩
  · refine ⟨z, ?_⟩
    apply (Submodule.Quotient.eq C).2
    have : i z - a • b = c := by rw [hz, ← hcd]; abel
    show i z - a • b ∈ C
    rw [this]
    exact hc
  · intro ha
    have hayC : y ∈ C := by
      have hab : a • b ∈ C := by
        rw [← Submodule.ker_mkQ C, LinearMap.mem_ker]
        simpa using ha
      rw [← hcd]
      exact C.add_mem hc hab
    exact hy0 ((Submodule.mem_bot R).1 (hUC.le_bot ⟨hyU', hayC⟩))

/-- A module which embeds in an injective module and admits no proper essential extension is
injective. -/
private lemma injective_of_all_essential_monos_are_isos
    {R : Type u} [Ring R] {Q : Type v} [AddCommGroup Q] [Module R Q]
    {I : Type (max w v)} [AddCommGroup I] [Module R I] [Module.Injective R I]
    (e : Q →ₗ[R] I) (he : Function.Injective e)
    (h : ∀ (P : ModuleCat.{v} R) (i : ModuleCat.of R Q ⟶ P) [Mono i],
      IsEssentialMono i → IsIso i) : Module.Injective R Q := by
  apply (Module.injective_iff_injective_object R Q).2
  refine ⟨?_⟩
  intro X Y g f hf
  have hfinj : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).1 hf
  let eX : X ≃ₗ[R] ULift.{max w v} X := ULift.moduleEquiv.symm
  let eY : Y ≃ₗ[R] ULift.{max w v} Y := ULift.moduleEquiv.symm
  let f' : ULift.{max w v} X →ₗ[R] ULift.{max w v} Y :=
    eY.toLinearMap.comp (f.hom.comp eX.symm.toLinearMap)
  let g' : ULift.{max w v} X →ₗ[R] I :=
    (e.comp g.hom).comp eX.symm.toLinearMap
  have hf' : Function.Injective f' := eY.injective.comp (hfinj.comp eX.symm.injective)
  obtain ⟨ψ', hψ₀⟩ := Module.Injective.out (R := R) (Q := I) f' hf' g'
  let ψ : Y →ₗ[R] I := ψ'.comp eY.toLinearMap
  have hψ : ψ.comp f.hom = e.comp g.hom := by
    ext x
    have hx := hψ₀ (eX x)
    simpa [ψ, f', g', eX, eY] using hx
  let F : Q × Y →ₗ[R] I := LinearMap.coprod e ψ
  let C : Submodule R (Q × Y) := LinearMap.ker F
  let P : Type v := (Q × Y) ⧸ C
  let q : Q →ₗ[R] P := C.mkQ.comp (LinearMap.inl R Q Y)
  let j : Y →ₗ[R] P := C.mkQ.comp (LinearMap.inr R Q Y)
  have hq : Function.Injective q := by
    intro x y hxy
    apply he
    have hxy' := congrArg (C.liftQ F le_rfl) hxy
    simpa [q, F, Submodule.liftQ_mkQ, LinearMap.comp_apply,
      LinearMap.coprod_apply] using hxy'
  let qM : ModuleCat.of R Q ⟶ ModuleCat.of R P := ModuleCat.ofHom q
  let : Mono qM := (ModuleCat.mono_iff_injective qM).2 hq
  have hrel : g ≫ qM = f ≫ ModuleCat.ofHom j := by
    ext x
    apply (Submodule.Quotient.eq C).2
    show (g.hom x, 0) - (0, f.hom x) ∈ C
    show F ((g.hom x, 0) - (0, f.hom x)) = 0
    simpa [F, LinearMap.coprod_apply, sub_eq_add_neg] using
      sub_eq_zero.mpr (LinearMap.congr_fun hψ x).symm
  obtain ⟨P', q₀, hmono, hess⟩ := exists_essential_quotient qM
  let : Mono (qM ≫ q₀) := hmono
  have : IsIso (qM ≫ q₀) := h P' (qM ≫ q₀) hess
  let eIso : ModuleCat.of R Q ≅ P' := asIso (qM ≫ q₀)
  let r : ModuleCat.of R P ⟶ ModuleCat.of R Q := q₀ ≫ eIso.inv
  refine ⟨ModuleCat.ofHom j ≫ r, ?_⟩
  have hqr : qM ≫ r = 𝟙 (ModuleCat.of R Q) := by
    dsimp [r]
    rw [← Category.assoc]
    show eIso.hom ≫ eIso.inv = 𝟙 _
    exact Iso.hom_inv_id _
  rw [← Category.assoc, ← hrel, Category.assoc, hqr, Category.comp_id]

/-- For a submodule of an injective module, having no proper essential extension inside the
ambient module already forces every essential monomorphism out of it to be an isomorphism. -/
private lemma all_essential_monos_are_isos_of_no_proper_extension
    {R : Type u} [Ring R] {I : Type v} [AddCommGroup I] [Module R I]
    [Module.Injective R I] (E : Submodule R I)
    (h : ∀ (E' : Submodule R I) (hE : E ≤ E'),
      let i := ModuleCat.ofHom (Submodule.inclusion hE)
      letI : Mono i := (ModuleCat.mono_iff_injective i).mpr
        (Submodule.inclusion_injective hE)
      IsEssentialMono i → E = E') :
    ∀ (P : ModuleCat.{v} R) (i : ModuleCat.of R E ⟶ P) [Mono i],
      IsEssentialMono i → IsIso i := by
  intro P i himono hi
  let : Mono i := himono
  let e : ModuleCat.of R E ⟶ ModuleCat.of R I := ModuleCat.ofHom E.subtype
  have iinj : Function.Injective i.hom := (ModuleCat.mono_iff_injective i).1 inferInstance
  obtain ⟨ψ₀, hψ₀⟩ := Module.Injective.out (R := R) (Q := I)
    i.hom iinj E.subtype
  let ψ : P ⟶ ModuleCat.of R I := ModuleCat.ofHom ψ₀
  have hψ : i ≫ ψ = e := by
    ext x
    exact hψ₀ x
  let : Mono e := (ModuleCat.mono_iff_injective e).2 E.subtype_injective
  have : Mono ψ := mono_of_isEssentialMono_of_comp_eq
    i hi e (𝟙 (ModuleCat.of R I)) ψ (by simpa using hψ)
  let F : Submodule R I := LinearMap.range ψ.hom
  have hEF : E ≤ F := by
    intro x hx
    have hxrange : ψ.hom (i.hom ⟨x, hx⟩) = x := by
      simpa [ψ] using hψ₀ ⟨x, hx⟩
    rw [← hxrange]
    exact LinearMap.mem_range_self _ (i.hom ⟨x, hx⟩)
  let EF : Submodule R F := Submodule.comap F.subtype E
  let kSub : ModuleCat.of R EF ⟶ ModuleCat.of R F := ModuleCat.ofHom EF.subtype
  let : Mono kSub := (ModuleCat.mono_iff_injective kSub).2 EF.subtype_injective
  have hessRange : IsEssentialMono kSub := by
    apply (isEssentialMono_subtype_iff (R := R) (N := ModuleCat.of R F) EF).2
    intro x hx
    obtain ⟨b, hbEq⟩ := x.2
    have hb0 : b ≠ 0 := by
      intro hb
      apply hx
      apply Subtype.ext
      simpa [hb] using hbEq.symm
    have hiRange := (isEssentialMono_iff_range i).1 hi
    obtain ⟨r, hrE, hr0⟩ :=
      (isEssentialMono_subtype_iff (R := R) (N := P) (LinearMap.range i.hom)).1 hiRange b hb0
    refine ⟨r, ?_, ?_⟩
    · show F.subtype (r • x) ∈ E
      obtain ⟨a, ha⟩ := hrE
      have hmap : ψ.hom (i.hom a) = E.subtype a := hψ₀ a
      have heq : F.subtype (r • x) = E.subtype a := by
        calc
          F.subtype (r • x) = r • ψ.hom b := by simp [hbEq]
          _ = ψ.hom (r • b) := by simp
          _ = ψ.hom (i.hom a) := by rw [ha]
          _ = E.subtype a := hmap
      exact heq ▸ a.2
    · intro hzero
      apply hr0
      apply (ModuleCat.mono_iff_injective ψ).1 inferInstance
      calc
        ψ.hom (r • b) = r • ψ.hom b := by simp
        _ = r • x := by rw [hbEq]
        _ = 0 := congrArg F.subtype hzero
        _ = ψ.hom 0 := by simp
  let k : ModuleCat.of R E ⟶ ModuleCat.of R F :=
    ModuleCat.ofHom (Submodule.inclusion hEF)
  let : Mono k := (ModuleCat.mono_iff_injective k).2
    (Submodule.inclusion_injective hEF)
  have hkess : IsEssentialMono k := by
    rw [isEssentialMono_iff_range k]
    have hrange : LinearMap.range k.hom = EF := by
      show LinearMap.range (Submodule.inclusion hEF) = EF
      rw [Submodule.range_inclusion]
    rw [hrange]
    exact hessRange
  have hEq : E = F := h F hEF hkess
  have hψE : ∀ p : P, ψ.hom p ∈ E := by
    intro p
    rw [hEq]
    exact LinearMap.mem_range_self _ p
  let r : P →ₗ[R] E := ψ.hom.codRestrict E hψE
  let rM : P ⟶ ModuleCat.of R E := ModuleCat.ofHom r
  have hir : i ≫ rM = 𝟙 (ModuleCat.of R E) := by
    ext x
    exact hψ₀ x
  exact isIso_of_essentialMono_of_retraction i rM hir hi

/-- A submodule of an injective module is injective if and only if it has no
proper essential extension inside the ambient module. -/
@[stacks 08XS "characterization inside an injective module"]
lemma injective_iff_eq_of_essential_extension
    (R : Type u) [Ring R] (I : Type v) [AddCommGroup I] [Module R I]
    [Module.Injective R I] (E : Submodule R I) :
    Module.Injective R E ↔
      ∀ (E' : Submodule R I) (h : E ≤ E'),
        let i := ModuleCat.ofHom (Submodule.inclusion h)
        letI : Mono i := (ModuleCat.mono_iff_injective i).mpr
          (Submodule.inclusion_injective h)
        IsEssentialMono i → E = E' := by
  constructor
  · intro hE E' h
    dsimp only
    let i := ModuleCat.ofHom (Submodule.inclusion h)
    let : Mono i := (ModuleCat.mono_iff_injective i).mpr
      (Submodule.inclusion_injective h)
    intro hess
    let : CategoryTheory.Injective (ModuleCat.of R E) :=
      (Module.injective_iff_injective_object R E).1 hE
    have := isIso_of_essentialMono_of_injective i hess
    apply SetLike.coe_injective
    apply Set.Subset.antisymm h
    intro x hx
    obtain ⟨y, hy⟩ := (ConcreteCategory.isIso_iff_bijective i).1 inferInstance |>.2 ⟨x, hx⟩
    have hy' : (y : I) = x := by simpa [i] using congrArg Subtype.val hy
    exact hy' ▸ y.2
  · exact fun h => injective_of_all_essential_monos_are_isos E.subtype E.subtype_injective
      (all_essential_monos_are_isos_of_no_proper_extension E h)

/-! ### Existence of injective hulls

Every module over a ring admits an essential embedding into an injective module. The result is
expressed in the category of modules, using the predicate `Module.IsInjectiveHull`; the module
category is taken in a universe at least as large as that of the ring, avoiding any artificial
smallness assumption on the ring. -/

/-- Inside an injective module, every submodule has an essential extension which is itself
injective: apply Zorn's lemma to the essential extensions of `E₀` and use
`Module.injective_iff_eq_of_essential_extension` on a maximal one. -/
lemma exists_injective_essential_extension {R : Type u} [Ring R]
    {I : Type v} [AddCommGroup I] [Module R I] [Module.Injective R I]
    (E₀ : Submodule R I) :
    ∃ (E : Submodule R I) (_ : E₀ ≤ E),
      (∀ x : E, x ≠ 0 → ∃ r : R, r • (x : I) ∈ E₀ ∧ r • (x : I) ≠ 0) ∧
        Module.Injective R E := by
  classical
  let P : Submodule R I → Prop := fun E =>
    E₀ ≤ E ∧ ∀ x : E, x ≠ 0 → ∃ r : R, r • (x : I) ∈ E₀ ∧ r • (x : I) ≠ 0
  let S : Set (Submodule R I) := {E | P E}
  have hE₀P : P E₀ := ⟨le_rfl, fun x hx => ⟨1, by simp, by simpa using hx⟩⟩
  have hchain : ∀ c : Set (Submodule R I), c ⊆ S → IsChain (· ≤ ·) c →
      ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hc hcc y hy
    let U : Submodule R I := sSup c
    have hE₀U : E₀ ≤ U := (hc hy).1.trans (le_sSup hy)
    have hessU : ∀ x : U, x ≠ 0 → ∃ r : R, r • (x : I) ∈ E₀ ∧ r • (x : I) ≠ 0 := by
      intro x hx
      obtain ⟨E, hEc, hxE⟩ :=
        (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hcc.directedOn).mp x.property
      obtain ⟨-, hessE⟩ := hc hEc
      have hxE0 : (⟨(x : I), hxE⟩ : E) ≠ 0 := by
        intro hz
        exact hx (Subtype.ext (by simpa using congrArg (fun z : E => (z : I)) hz))
      exact hessE ⟨(x : I), hxE⟩ hxE0
    exact ⟨U, ⟨hE₀U, hessU⟩, fun z hzc => le_sSup hzc⟩
  obtain ⟨E, -, hmax⟩ := zorn_le_nonempty₀ S hchain E₀ hE₀P
  obtain ⟨hE₀E, hessE⟩ : P E := hmax.1
  refine ⟨E, hE₀E, hessE, ?_⟩
  apply (injective_iff_eq_of_essential_extension R I E).2
  intro E' hEE' j hj
  have : Mono (ModuleCat.ofHom (Submodule.inclusion hEE')) :=
    (ModuleCat.mono_iff_injective _).mpr (Submodule.inclusion_injective hEE')
  have hess0E' : ∀ x : E', x ≠ 0 → ∃ r : R, r • (x : I) ∈ E₀ ∧ r • (x : I) ≠ 0 := by
    intro x hx
    obtain ⟨r, hrE, hr0⟩ := (essential_inclusion_iff_elementwise E E' hEE').mp hj x hx
    have hr0E : (⟨r • (x : I), hrE⟩ : E) ≠ 0 := by simpa using hr0
    obtain ⟨s, hsE₀, hs0⟩ := hessE ⟨r • (x : I), hrE⟩ hr0E
    refine ⟨s * r, ?_, ?_⟩
    · simpa [smul_smul] using hsE₀
    · intro h
      exact hs0 (by simpa [smul_smul] using h)
  apply SetLike.coe_injective
  exact le_antisymm hEE' (hmax.2 ⟨hE₀E.trans hEE', hess0E'⟩ hEE')

/-- Every module over a ring has an injective hull. -/
@[stacks 08Y3]
theorem exists_isInjectiveHull (R : Type u) [Ring R]
    (M : ModuleCat.{max v u} R) :
    ∃ (I : ModuleCat.{max v u} R) (i : M ⟶ I) (h : Mono i),
      let _ : Mono i := h
      IsInjectiveHull i := by
  classical
  let p := (EnoughInjectives.presentation M).some
  let I := p.J
  let i := p.f
  let : CategoryTheory.Injective I := p.injective
  let : Mono i := p.mono
  let : Module.Injective R I :=
    (Module.injective_iff_injective_object R I).mpr p.injective
  obtain ⟨E, hE₀E, hessE, hEinj⟩ :=
    exists_injective_essential_extension (LinearMap.range i.hom)
  have : Mono (ModuleCat.ofHom (Submodule.inclusion hE₀E)) :=
    (ModuleCat.mono_iff_injective _).mpr (Submodule.inclusion_injective hE₀E)
  have hessE' : IsEssentialMono (ModuleCat.ofHom (Submodule.inclusion hE₀E)) :=
    (essential_inclusion_iff_elementwise _ E hE₀E).2 hessE
  let e₀ : M ≃ₗ[R] LinearMap.range i.hom := LinearEquiv.ofInjective i.hom
    ((ModuleCat.mono_iff_injective i).1 inferInstance)
  exact ⟨ModuleCat.of R E,
    e₀.toModuleIso.hom ≫ ModuleCat.ofHom (Submodule.inclusion hE₀E), inferInstance,
    (Module.injective_iff_injective_object R E).mp hEinj,
    isEssentialMono_comp _ _ (essential_of_iso _) hessE'⟩

/-- A module is injective if and only if every essential monomorphism from it is an isomorphism. -/
@[stacks 08XS "intrinsic characterization"]
lemma injective_iff_isIso_essentialMono
    (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q] :
    Module.Injective R Q ↔
      ∀ (E' : ModuleCat.{v} R) (i : ModuleCat.of R Q ⟶ E') [Mono i],
        IsEssentialMono i → IsIso i := by
  rw [Module.injective_iff_injective_object]
  constructor
  · intro h E' i _ hi
    exact isIso_of_essentialMono_of_injective i hi
  · intro h
    obtain ⟨J, i, hi, hJ⟩ :=
      exists_isInjectiveHull R (ModuleCat.of R (ULift.{max u v} Q))
    let : Mono i := hi
    have : CategoryTheory.Injective J := hJ.1
    have : Module.Injective R J := (Module.injective_iff_injective_object R J).2 hJ.1
    exact (Module.injective_iff_injective_object R Q).1 <|
      injective_of_all_essential_monos_are_isos
        (i.hom.comp ULift.moduleEquiv.symm.toLinearMap)
        (((ModuleCat.mono_iff_injective i).1 hi).comp ULift.moduleEquiv.symm.injective) h

end Module
