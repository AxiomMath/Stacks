module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasicoherentChaotic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ExtCochainComplexComputesExt
import StacksCore.Tactic.StacksAttribute

/-!
# Objectwise injectivity does not make the cochain complex compute `Ext`

Let `C` be a small category with the chaotic topology, `O` a sheaf of rings on it and `F`, `G`
two `O`-modules. Stacks 08S0 compares `Ext^i_O(G, F)` with the cohomology of the cochain complex
`K^•(G, F)` of `Stacks.CategoryExt.extCochainComplex`, whose degree-`n` term is the product over
the strings `U₀ ⟶ ⋯ ⟶ Uₙ` of `Hom_{O(Uₙ)}(G(Uₙ), F(U₀))`. The comparison holds when `F(U)` is
injective over `O(V)`, through restriction, for every arrow `U ⟶ V`
(`Stacks.CategoryExt.extAddEquivCohomology_of_arrowwiseInjective`). This file shows that it fails
when `F(U)` is only asked to be an injective `O(U)`-module for every object `U`: restriction of
scalars along a non-flat ring map need not preserve injectivity.

Take for `C` the category `false ⟶ true` (the order `Bool`), with `O(true) = ℤ`,
`O(false) = ℤ/2` and reduction as restriction, and let `F` have `F(true) = 0`,
`F(false) = ℤ/2`, and `G` have `G(true) = ℤ/2`, `G(false) = 0`. Both sections of `F` are injective
over their rings, as `ℤ/2` is a field. On the one hand `Ext²_O(G, F) ≠ 0`: the module `P` with
`P(true) = ℤ`, `P(false) = ℤ/2` is projective (maps out of it are sections over `true`) and
covers `G` with kernel `K`, where `K(true) = ℤ`, `K(false) = ℤ/2` with zero restriction, so
`Ext¹_O(K, F)` injects into `Ext²_O(G, F)`; and `Ext¹_O(K, F) ≠ 0`, because the extension
`0 ⟶ F ⟶ E ⟶ K ⟶ 0` with `E(true) = ℤ`, `E(false) = (ℤ/2)²` and restriction `k ↦ (k, 0)` does
not split. On the other hand `H²(K^•(G, F)) = 0`: a degree-two cochain vanishes on strings
ending at `false` or starting at `true`, and its values on the strings `false ⟶ false ⟶ true`
and `false ⟶ true ⟶ true` are, up to sign, its coboundary on the strings
`false ⟶ false ⟶ false ⟶ true` and `false ⟶ true ⟶ true ⟶ true`, so every degree-two cocycle is
zero.

## Main definitions

* `Stacks.CategoryExt.ArrowCounterexample.ring` and
  `Stacks.CategoryExt.ArrowCounterexample.module`: a presheaf of rings on `false ⟶ true` given by
  a ring map, and a module over it given by a semilinear map.
* `Stacks.CategoryExt.ArrowCounterexample.O`, `Stacks.CategoryExt.ArrowCounterexample.source` and
  `Stacks.CategoryExt.ArrowCounterexample.target`: the ring sheaf `O` and the modules `G` and `F`
  above.

## Main results

* `Stacks.CategoryExt.ArrowCounterexample.injective_obj_and_not_nonempty_extAddEquiv_two`:
  every `F(U)` is an injective `O(U)`-module, and `Ext²_O(G, F)` is not isomorphic to
  `H²(K^•(G, F))`.
* `Stacks.CategoryExt.ArrowCounterexample.not_forall_injective_obj_nonempty_extAddEquiv`:
  case (2) of Stacks 08S0 with objectwise injectivity as hypothesis is false.
* `Stacks.CategoryExt.ArrowCounterexample.not_arrowwiseInjective_target`: consequently `F` does
  not satisfy the arrowwise injectivity hypothesis.

## References

* [Stacks Project, Tag 08S0](https://stacks.math.columbia.edu/tag/08S0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryExt.ArrowCounterexample

variable {R S : Type} [Ring R] [Ring S] (φ : R →+* S)

/-- The presheaf of rings on the arrow `false ⟶ true` with sections `S` over `false`, `R` over
`true`, and restriction `φ`. -/
abbrev ring : Boolᵒᵖ ⥤ RingCat.{0} where
  obj X := match X with
    | op false => RingCat.of S
    | op true => RingCat.of R
  map {X Y} f := match X, Y, f with
    | op false, op false, _ => 𝟙 _
    | op true, op true, _ => 𝟙 _
    | op true, op false, _ => RingCat.ofHom φ
    | op false, op true, f => absurd (leOfHom f.unop) (by decide)
  map_id X := by rcases X with ⟨_ | _⟩ <;> rfl
  map_comp {X Y Z} f g := by
    rcases X with ⟨_ | _⟩ <;> rcases Y with ⟨_ | _⟩ <;> rcases Z with ⟨_ | _⟩
    all_goals first
      | rfl
      | exact absurd (leOfHom f.unop) (by decide)
      | exact absurd (leOfHom g.unop) (by decide)

/-- A module over `ring φ`: an `S`-module `M₀` over `false`, an `R`-module `M₁` over `true`, and
the restriction map `t : M₁ ⟶ M₀`, semilinear along `φ`. -/
abbrev module (M₀ : ModuleCat.{0} S) (M₁ : ModuleCat.{0} R) (t : M₁ →ₛₗ[φ] M₀) :
    PresheafOfModules.{0} (ring φ) where
  obj X := match X with
    | op false => M₀
    | op true => M₁
  map {X Y} f := match X, Y, f with
    | op false, op false, _ => ModuleCat.ofHom
        { toFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    | op true, op true, _ => ModuleCat.ofHom
        { toFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    | op true, op false, _ => ModuleCat.ofHom (Y := (ModuleCat.restrictScalars φ).obj M₀)
        { toFun := t, map_add' := t.map_add, map_smul' := t.map_smulₛₗ }
    | op false, op true, f => absurd (leOfHom f.unop) (by decide)
  map_id X := by rcases X with ⟨_ | _⟩ <;> rfl
  map_comp {X Y Z} f g := by
    rcases X with ⟨_ | _⟩ <;> rcases Y with ⟨_ | _⟩ <;> rcases Z with ⟨_ | _⟩
    all_goals first
      | rfl
      | exact absurd (leOfHom f.unop) (by decide)
      | exact absurd (leOfHom g.unop) (by decide)

variable {φ} in
/-- A morphism of modules over `ring φ`, from a pair of linear maps commuting with the
restriction maps. -/
def moduleHom {M₀ N₀ : ModuleCat.{0} S} {M₁ N₁ : ModuleCat.{0} R} {t : M₁ →ₛₗ[φ] M₀}
    {u : N₁ →ₛₗ[φ] N₀} (a₀ : M₀ →ₗ[S] N₀) (a₁ : M₁ →ₗ[R] N₁) (h : ∀ x, a₀ (t x) = u (a₁ x)) :
    module φ M₀ M₁ t ⟶ module φ N₀ N₁ u where
  app X := match X with
    | op false => ModuleCat.ofHom a₀
    | op true => ModuleCat.ofHom a₁
  naturality {X Y} f := by
    rcases X with ⟨_ | _⟩ <;> rcases Y with ⟨_ | _⟩
    · rfl
    · exact absurd (leOfHom f.unop) (by decide)
    · ext x
      exact h x
    · rfl

/-! ### The counterexample -/

/-- The restriction map `ℤ ⟶ ℤ/2` of the counterexample. -/
abbrev castRingHom : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)

/-- The sheaf of rings of the counterexample: `ℤ/2` over `false`, `ℤ` over `true`. -/
abbrev O : Boolᵒᵖ ⥤ RingCat.{0} := ring castRingHom

/-- The reduction map `ℤ ⟶ ℤ/2`, semilinear along the restriction map of `O`. -/
def reduction : ModuleCat.of ℤ ℤ →ₛₗ[castRingHom] ModuleCat.of (ZMod 2) (ZMod 2) where
  toFun k := castRingHom k
  map_add' := map_add castRingHom
  map_smul' r k := by simp

/-- The target module `F` of the counterexample: `ℤ/2` over `false` and `0` over `true`. -/
abbrev target : PresheafOfModules.{0} O :=
  module castRingHom (ModuleCat.of (ZMod 2) (ZMod 2)) (ModuleCat.of ℤ PUnit) 0

/-- The source module `G` of the counterexample: `0` over `false` and `ℤ/2` over `true`. -/
abbrev source : PresheafOfModules.{0} O :=
  module castRingHom (ModuleCat.of (ZMod 2) PUnit) (ModuleCat.of ℤ (ZMod 2)) 0

/-- The free module on the representable of `true`: `ℤ/2` over `false`, `ℤ` over `true`. -/
abbrev cover : PresheafOfModules.{0} O :=
  module castRingHom (ModuleCat.of (ZMod 2) (ZMod 2)) (ModuleCat.of ℤ ℤ) reduction

/-- The kernel of `cover ⟶ source`: `ℤ/2` over `false`, `ℤ` over `true`, zero restriction. -/
abbrev syzygy : PresheafOfModules.{0} O :=
  module castRingHom (ModuleCat.of (ZMod 2) (ZMod 2)) (ModuleCat.of ℤ ℤ) 0

/-- The restriction map `k ↦ (k mod 2, 0)` of the non-split extension. -/
def reductionInl :
    ModuleCat.of ℤ ℤ →ₛₗ[castRingHom] ModuleCat.of (ZMod 2) (ZMod 2 × ZMod 2) where
  toFun k := (castRingHom k, 0)
  map_add' k l := by simp
  map_smul' r k := by ext <;> simp

/-- A non-split extension of `syzygy` by `target`. -/
abbrev extension : PresheafOfModules.{0} O :=
  module castRingHom (ModuleCat.of (ZMod 2) (ZMod 2 × ZMod 2)) (ModuleCat.of ℤ ℤ) reductionInl

/-- Twice an integer reduces to zero modulo `2`. -/
lemma castRingHom_two_zsmul (k : ℤ) : castRingHom ((2 : ℤ) • k) = 0 := by
  rw [zsmul_eq_mul, map_mul]
  exact (congrArg (· * _) (by decide)).trans (zero_mul _)

/-- The inclusion of the syzygy: the identity over `false`, multiplication by `2` over `true`. -/
def syzygyToCover : syzygy ⟶ cover :=
  moduleHom LinearMap.id ((2 : ℤ) • LinearMap.id) fun k ↦ (castRingHom_two_zsmul k).symm

/-- The cover of the source: zero over `false`, reduction modulo `2` over `true`. -/
def coverToSource : cover ⟶ source :=
  moduleHom 0 (Int.castAddHom (ZMod 2)).toIntLinearMap fun _ ↦ rfl

/-- The inclusion of the target into the extension: `x ↦ (x, 0)` over `false`. -/
def targetToExtension : target ⟶ extension :=
  moduleHom (LinearMap.inl (ZMod 2) (ZMod 2) (ZMod 2)) 0 fun _ ↦ by
    ext <;> rfl

/-- The projection of the extension onto the syzygy: `(x, y) ↦ y` over `false`. -/
def extensionToSyzygy : extension ⟶ syzygy :=
  moduleHom (LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2)) LinearMap.id fun _ ↦ rfl

/-- The short exact sequence `0 ⟶ syzygy ⟶ cover ⟶ source ⟶ 0`. -/
def coverSequence : ShortComplex (PresheafOfModules.{0} O) :=
  ShortComplex.mk syzygyToCover coverToSource (by
    refine PresheafOfModules.hom_ext fun X ↦ ?_
    rcases X with ⟨_ | _⟩
    · rfl
    · exact ModuleCat.hom_ext (LinearMap.ext fun k ↦ castRingHom_two_zsmul k))

/-- The short exact sequence `0 ⟶ target ⟶ extension ⟶ syzygy ⟶ 0`. -/
def extensionSequence : ShortComplex (PresheafOfModules.{0} O) :=
  ShortComplex.mk targetToExtension extensionToSyzygy (by
    refine PresheafOfModules.hom_ext fun X ↦ ?_
    rcases X with ⟨_ | _⟩
    · exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)
    · exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

/-- The arrow `false ⟶ true` of `Bool`, as an arrow of `Boolᵒᵖ`. -/
abbrev arrow : op true ⟶ op false := (homOfLE (by decide : false ≤ true)).op

/-- `coverSequence` is short exact. -/
lemma shortExact_coverSequence : coverSequence.ShortExact where
  exact := ChaoticQCoh.exact_of_evaluation _ _ fun X ↦ by
    rw [ShortComplex.moduleCat_exact_iff]
    rcases X with ⟨_ | _⟩
    · exact fun x _ ↦ ⟨x, rfl⟩
    · intro k hk
      obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k 2).mp hk
      refine ⟨j, (smul_eq_mul (2 : ℤ) j).trans ?_⟩
      rw [hj]
      norm_num
  mono_f := PresheafOfModules.mono_of_injective <| by
    intro X
    rcases X with ⟨_ | _⟩
    · exact fun _ _ h ↦ h
    · intro (j : ℤ) (k : ℤ) h
      have hjk : j = k := mul_left_cancel₀ (M₀ := ℤ) two_ne_zero h
      exact hjk
  epi_g := PresheafOfModules.epi_of_surjective <| by
    intro X
    rcases X with ⟨_ | _⟩
    · exact fun _ ↦ ⟨0, rfl⟩
    · intro (x : ZMod 2)
      obtain ⟨k, hk⟩ := ZMod.intCast_surjective x
      exact ⟨k, hk⟩

/-- `extensionSequence` is short exact. -/
lemma shortExact_extensionSequence : extensionSequence.ShortExact where
  exact := ChaoticQCoh.exact_of_evaluation _ _ fun X ↦ by
    rw [ShortComplex.moduleCat_exact_iff]
    rcases X with ⟨_ | _⟩
    · rintro ⟨x, y⟩ (hy : y = 0)
      exact ⟨x, Prod.ext rfl hy.symm⟩
    · intro k (hk : k = 0)
      exact ⟨PUnit.unit, hk.symm⟩
  mono_f := PresheafOfModules.mono_of_injective <| by
    intro X
    rcases X with ⟨_ | _⟩
    · exact fun _ _ h ↦ congrArg Prod.fst h
    · exact fun _ _ _ ↦ rfl
  epi_g := PresheafOfModules.epi_of_surjective <| by
    intro X
    rcases X with ⟨_ | _⟩
    · exact fun y ↦ ⟨(0, y), rfl⟩
    · exact fun k ↦ ⟨k, rfl⟩

/-- The extension of `syzygy` by `target` does not split. -/
lemma targetToExtension_comp_ne_id (r : extension ⟶ target) : targetToExtension ≫ r ≠ 𝟙 _ := by
  intro h
  have h₁ : r.app (op false) ((1 : ZMod 2), (0 : ZMod 2)) = (1 : ZMod 2) :=
    congrArg (fun t : target ⟶ target ↦ t.app (op false) (1 : ZMod 2)) h
  have h₂ : r.app (op false) ((1 : ZMod 2), (0 : ZMod 2)) = 0 :=
    PresheafOfModules.naturality_apply r arrow (1 : ℤ)
  exact absurd (h₁.symm.trans h₂ : (1 : ZMod 2) = 0) (by decide)

/-- The component over `false` of the morphism out of `cover` determined by a section. -/
def fromSectionFalse (M : PresheafOfModules.{0} O) (m : M.obj (op true)) :
    cover.obj (op false) ⟶ M.obj (op false) :=
  ModuleCat.ofHom (@LinearMap.toSpanSingleton (O.obj (op false)) (M.obj (op false)) _ _
    (M.obj (op false)).isModule (M.map arrow m))

/-- The component over `true` of the morphism out of `cover` determined by a section. -/
def fromSectionTrue (M : PresheafOfModules.{0} O) (m : M.obj (op true)) :
    cover.obj (op true) ⟶ M.obj (op true) :=
  ModuleCat.ofHom (@LinearMap.toSpanSingleton (O.obj (op true)) (M.obj (op true)) _ _
    (M.obj (op true)).isModule m)

/-- The morphism out of `cover` determined by a section over `true`. -/
def fromSection (M : PresheafOfModules.{0} O) (m : M.obj (op true)) : cover ⟶ M where
  app X := match X with
    | op false => fromSectionFalse M m
    | op true => fromSectionTrue M m
  naturality {X Y} f := by
    rcases X with ⟨_ | _⟩ <;> rcases Y with ⟨_ | _⟩
    · obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
      simp only [PresheafOfModules.map_id]
      rfl
    · exact absurd (leOfHom f.unop) (by decide)
    · obtain rfl : f = arrow := Subsingleton.elim _ _
      refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
      change @HSMul.hSMul _ _ _ (@instHSMul _ _ (M.obj (op false)).isModule.toSMul)
          (castRingHom 1) (M.map arrow m) =
        M.map arrow (@HSMul.hSMul _ _ _ (@instHSMul _ _ (M.obj (op true)).isModule.toSMul) 1 m)
      rw [map_one]
      exact (@one_smul _ _ _ (M.obj (op false)).isModule.toDistribMulAction.toMulAction _).trans
        (congrArg _
          (@one_smul _ _ _ (M.obj (op true)).isModule.toDistribMulAction.toMulAction m).symm)
    · obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
      simp only [PresheafOfModules.map_id]
      rfl

/-- `cover` is projective: a morphism out of it is a section over `true`, and an epimorphism of
presheaves of modules is surjective on sections. -/
instance : Projective cover where
  factors {E X} f e _ := by
    obtain ⟨m, hm⟩ := PresheafOfModules.surjective_of_epi e (op true) (f.app (op true) (1 : ℤ))
    refine ⟨fromSection E m, PresheafOfModules.hom_ext fun Y ↦ ?_⟩
    rcases Y with ⟨_ | _⟩
    · refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
      have h₁ : (fromSectionFalse E m).hom 1 = E.map arrow m := one_smul _ _
      have h₂ : cover.map arrow (1 : ℤ) = (1 : ZMod 2) := map_one castRingHom
      change e.app (op false) ((fromSectionFalse E m).hom 1) = f.app (op false) 1
      rw [h₁, PresheafOfModules.naturality_apply, hm, ← h₂]
      exact (PresheafOfModules.naturality_apply f arrow (1 : ℤ)).symm
    · refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
      have h₁ : (fromSectionTrue E m).hom 1 = m :=
        @one_smul _ _ _ (E.obj (op true)).isModule.toDistribMulAction.toMulAction m
      change e.app (op true) ((fromSectionTrue E m).hom 1) = f.app (op true) 1
      rw [h₁, hm]

/-- Each section of `target` is an injective module over the ring at the same object. -/
lemma injective_target_obj (U : Bool) : Injective (target.obj (op U)) := by
  rcases U with _ | _
  · have := Module.injective_of_isSemisimpleRing (ZMod 2) (ZMod 2)
    exact Module.injective_object_of_injective_module (ZMod 2) (ZMod 2)
  · have : Subsingleton (target.obj (op true)) := inferInstanceAs (Subsingleton PUnit)
    exact Injective.of_iso (ModuleCat.isZero_of_subsingleton _).isoZero.symm
      Injective.zero_injective

section Ext

variable [HasExt.{0} (PresheafOfModules.{0} O)]

/-- The class of the non-split extension `extensionSequence` is nonzero in
`Ext¹(syzygy, target)`. -/
lemma extClass_extensionSequence_ne_zero : shortExact_extensionSequence.extClass ≠ 0 := by
  intro h
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ shortExact_extensionSequence
    extensionSequence.X₁ (Abelian.Ext.mk₀ (𝟙 extensionSequence.X₁)) (n₁ := 1) (by omega)
    ((Abelian.Ext.comp_mk₀_id _).trans h)
  obtain ⟨r, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x₂
  rw [Abelian.Ext.mk₀_comp_mk₀] at hx₂
  exact targetToExtension_comp_ne_id r ((Abelian.Ext.mk₀_bijective _ _).1 hx₂)

/-- The Yoneda product of the two extension classes is a nonzero element of
`Ext²(source, target)`. -/
lemma extClass_comp_extClass_ne_zero :
    shortExact_coverSequence.extClass.comp shortExact_extensionSequence.extClass
      (by omega : 1 + 1 = 2) ≠ 0 := by
  intro h
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ shortExact_coverSequence target
    shortExact_extensionSequence.extClass (n₁ := 2) (by omega) h
  have : Projective coverSequence.X₂ := inferInstanceAs (Projective cover)
  rw [Abelian.Ext.eq_zero_of_projective (n := 0) x₂, Abelian.Ext.comp_zero] at hx₂
  exact extClass_extensionSequence_ne_zero hx₂.symm

end Ext

attribute [local instance] HasDerivedCategory.standard in
/-- `Ext²_O(source, target)` is nonzero. -/
lemma nontrivial_zExt_source_target_two : Nontrivial (Abelian.zExt source target (2 : ℕ)) := by
  let : HasExt.{0} (PresheafOfModules.{0} O) := hasExt_presheafOfModules.{0, 0, 0}
  refine ⟨Abelian.Ext.homAddEquiv
    (shortExact_coverSequence.extClass.comp shortExact_extensionSequence.extClass
      (by omega : 1 + 1 = 2)), 0, fun h ↦ extClass_comp_extClass_ne_zero ?_⟩
  exact Abelian.Ext.homAddEquiv.injective (h.trans (map_zero _).symm)

/-! ### The cochain complex -/

/-- A string of arrows of `Bool` is determined by its objects. -/
lemma string_ext {n : ℕ} {x y : ComposableArrows Bool n} (h : ∀ i, x.obj i = y.obj i) :
    x = y :=
  ComposableArrows.ext h fun _ _ ↦ Subsingleton.elim _ _

/-- A cochain takes the same value at equal strings. -/
lemma extCochain_apply_heq {n : ℕ} (ψ : extCochain source target n)
    {x y : ComposableArrows Bool n} (h : x = y) (s : source.obj (op (x.obj (Fin.last n))))
    (t : source.obj (op (y.obj (Fin.last n)))) (hst : HEq s t) : HEq (ψ x s) (ψ y t) := by
  subst h
  cases hst
  rfl

/-- The sections of `source` over `false` vanish. -/
lemma source_eq_zero {b : Bool} (hb : b = false) (s : source.obj (op b)) : s = 0 := by
  subst hb
  rfl

/-- The sections of `target` over `true` vanish. -/
lemma target_eq_zero {b : Bool} (hb : b = true) (s : target.obj (op b)) : s = 0 := by
  subst hb
  rfl

/-- The string `false ⟶ false ⟶ true`. -/
abbrev stringFFT : ComposableArrows Bool 2 :=
  ComposableArrows.mk₂ (homOfLE (le_refl false)) (homOfLE (by decide : false ≤ true))

/-- The string `false ⟶ false ⟶ false ⟶ true`. -/
abbrev stringFFFT : ComposableArrows Bool 3 :=
  ComposableArrows.mk₃ (homOfLE (le_refl false)) (homOfLE (le_refl false))
    (homOfLE (by decide : false ≤ true))

/-- The string `false ⟶ true ⟶ true`. -/
abbrev stringFTT : ComposableArrows Bool 2 :=
  ComposableArrows.mk₂ (homOfLE (by decide : false ≤ true)) (homOfLE (le_refl true))

/-- The string `false ⟶ true ⟶ true ⟶ true`. -/
abbrev stringFTTT : ComposableArrows Bool 3 :=
  ComposableArrows.mk₃ (homOfLE (by decide : false ≤ true)) (homOfLE (le_refl true))
    (homOfLE (le_refl true))

/-- A degree-two cocycle vanishes on the string `false ⟶ false ⟶ true`. -/
lemma extCochain_apply_stringFFT_eq_zero (ψ : extCochain source target 2)
    (hψ : (extCochainComplex source target).d 2 3 ψ = 0)
    (s : source.obj (op (stringFFT.obj (Fin.last 2)))) : ψ stringFFT s = 0 := by
  have hd : ((extCochainComplex source target).d 2 3 ψ : extCochain source target 3) stringFFFT s =
      0 := by
    rw [hψ]
    rfl
  rw [extCochainComplex_d_apply, Fin.sum_univ_four] at hd
  have e : ∀ i : Fin 4, i ≠ 3 →
      extCochainSimplexMap source target (SimplexCategory.δ i) ψ stringFFFT s = ψ stringFFT s := by
    intro i hi
    fin_cases i
    all_goals first
      | exact absurd rfl hi
      | exact eq_of_heq
          (extCochain_apply_heq ψ (string_ext fun k ↦ by fin_cases k <;> rfl) _ _ HEq.rfl)
  have e₃ : extCochainSimplexMap source target (SimplexCategory.δ (3 : Fin 4)) ψ stringFFFT s =
      0 := by
    rw [extCochainSimplexMap_apply]
    exact (congrArg _ ((congrArg _ (source_eq_zero rfl _)).trans (map_zero _))).trans
      (map_zero _)
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e₃, smul_zero, add_zero, ← add_zsmul,
    ← add_zsmul] at hd
  rwa [show (-1 : ℤ) ^ ((0 : Fin 4) : ℕ) + (-1) ^ ((1 : Fin 4) : ℕ) + (-1) ^ ((2 : Fin 4) : ℕ) = 1
    from rfl, one_zsmul] at hd

/-- A degree-two cocycle vanishes on the string `false ⟶ true ⟶ true`. -/
lemma extCochain_apply_stringFTT_eq_zero (ψ : extCochain source target 2)
    (hψ : (extCochainComplex source target).d 2 3 ψ = 0)
    (s : source.obj (op (stringFTT.obj (Fin.last 2)))) : ψ stringFTT s = 0 := by
  have hd : ((extCochainComplex source target).d 2 3 ψ : extCochain source target 3) stringFTTT s =
      0 := by
    rw [hψ]
    rfl
  rw [extCochainComplex_d_apply, Fin.sum_univ_four] at hd
  have e₀ : extCochainSimplexMap source target (SimplexCategory.δ (0 : Fin 4)) ψ stringFTTT s =
      0 := by
    rw [extCochainSimplexMap_apply]
    exact (congrArg _ (target_eq_zero rfl _)).trans (map_zero _)
  have e : ∀ i : Fin 4, i ≠ 0 →
      extCochainSimplexMap source target (SimplexCategory.δ i) ψ stringFTTT s = ψ stringFTT s := by
    intro i hi
    fin_cases i
    all_goals first
      | exact absurd rfl hi
      | exact eq_of_heq
          (extCochain_apply_heq ψ (string_ext fun k ↦ by fin_cases k <;> rfl) _ _ HEq.rfl)
  rw [e₀, e 1 (by decide), e 2 (by decide), e 3 (by decide), smul_zero, zero_add, ← add_zsmul,
    ← add_zsmul] at hd
  rwa [show (-1 : ℤ) ^ ((1 : Fin 4) : ℕ) + (-1) ^ ((2 : Fin 4) : ℕ) + (-1) ^ ((3 : Fin 4) : ℕ) = -1
    from rfl, neg_one_zsmul, neg_eq_zero] at hd

/-- Every degree-two cocycle of `K^•(source, target)` vanishes. -/
lemma extCochain_eq_zero_of_d_eq_zero (ψ : extCochain source target 2)
    (hψ : (extCochainComplex source target).d 2 3 ψ = 0) : ψ = 0 := by
  funext y
  refine LinearMap.ext fun s ↦ ?_
  change ψ y s = 0
  rcases Bool.eq_false_or_eq_true (y.obj (Fin.last 2)) with h₂ | h₂
  swap
  · rw [source_eq_zero h₂ s, map_zero]
  rcases Bool.eq_false_or_eq_true (y.obj 0) with h₀ | h₀
  · exact target_eq_zero h₀ _
  rcases Bool.eq_false_or_eq_true (y.obj 1) with h₁ | h₁
  · obtain rfl : y = stringFTT := string_ext fun k ↦ by fin_cases k; exacts [h₀, h₁, h₂]
    exact extCochain_apply_stringFTT_eq_zero ψ hψ s
  · obtain rfl : y = stringFFT := string_ext fun k ↦ by fin_cases k; exacts [h₀, h₁, h₂]
    exact extCochain_apply_stringFFT_eq_zero ψ hψ s

/-- `H²(K^•(source, target)) = 0`. -/
lemma isZero_extCochainComplex_homology_two :
    IsZero ((extCochainComplex source target).homology 2) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 1 2 3 (by simp) (by simp), ShortComplex.ab_exact_iff]
  intro ψ hψ
  exact ⟨0, (map_zero _).trans (extCochain_eq_zero_of_d_eq_zero ψ hψ).symm⟩

attribute [local instance] HasDerivedCategory.standard in
/-- **Stacks 08S0**, the counterexample to case (2) with objectwise injectivity. On the category
`false ⟶ true` with `O(true) = ℤ`, `O(false) = ℤ/2`, the module `F = target` has
`F(true) = 0` and `F(false) = ℤ/2`, so each `F(U)` is an injective `O(U)`-module; yet for
`G = source`, with `G(true) = ℤ/2` and `G(false) = 0`, the groups `Ext²_O(G, F)` and
`H²(K^•(G, F))` are not isomorphic. -/
@[stacks 08S0 "the counterexample: objectwise injectivity of F does not suffice in case (2)"]
theorem injective_obj_and_not_nonempty_extAddEquiv_two :
    (∀ U : Bool, Injective (target.obj (op U))) ∧
      ¬ Nonempty (Abelian.zExt source target ((2 : ℕ) : ℤ) ≃+
        (extCochainComplex source target).homology 2) := by
  refine ⟨injective_target_obj, fun ⟨e⟩ ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := nontrivial_zExt_source_target_two
  have := AddCommGrpCat.subsingleton_of_isZero isZero_extCochainComplex_homology_two
  exact hab (e.injective (Subsingleton.elim _ _))

attribute [local instance] HasDerivedCategory.standard in
/-- Case (2) of Stacks 08S0 is false under the hypothesis that `F(U)` be an injective
`O(U)`-module for every object `U`. -/
theorem not_forall_injective_obj_nonempty_extAddEquiv :
    ¬ ∀ (C : Type) [SmallCategory C] (O : Cᵒᵖ ⥤ RingCat.{0}) (G F : PresheafOfModules.{0} O),
      (∀ U : C, Injective (F.obj (op U))) →
        ∀ n : ℕ, Nonempty (Abelian.zExt G F (n : ℤ) ≃+ (extCochainComplex G F).homology n) :=
  fun h ↦ injective_obj_and_not_nonempty_extAddEquiv_two.2
    (h Bool O source target injective_target_obj 2)

/-- The module `target` is injective at every object but does not satisfy the arrowwise
injectivity hypothesis of `Stacks.CategoryExt.extAddEquivCohomology_of_arrowwiseInjective`:
`F(false) = ℤ/2` is not injective over `O(true) = ℤ`. -/
theorem not_arrowwiseInjective_target :
    ¬ ∀ {U V : Bool} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (target.obj (op U))) :=
  fun hF ↦ injective_obj_and_not_nonempty_extAddEquiv_two.2
    ⟨extAddEquivCohomology_of_arrowwiseInjective.{0, 0, 0} source target hF 2⟩

end Stacks.CategoryExt.ArrowCounterexample
