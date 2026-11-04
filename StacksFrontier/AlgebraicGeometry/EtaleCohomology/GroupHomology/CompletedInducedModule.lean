module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.DerivedCoinvariants

/-!
# The completed induced module `M[[G]] = Λ[[G]] ⊗_Λ M`

Let `Λ` be a ring, `G` a topological group and `M` a `Λ`-module. The completed induced module
`M[[G]]` is the limit over the open normal subgroups `U` of `G` of the modules `M[G/U]` of finitely
supported `M`-valued functions on `G/U`, the transition maps being push-forward along the quotient
maps. The completed group algebra `Λ[[G]]` acts on it through the convolution action of `Λ[G/U]` on
`M[G/U]`. For `M = Λ` this is `Λ[[G]]` itself, and for a finite projective `Λ`-module `M` it is a
projective `Λ[[G]]`-module, namely `Λ[[G]] ⊗_Λ M`. Its coinvariants are `M`, through the sum of the
values.

All names are in the namespace `Stacks.GroupHomology`.

## Main definitions

* `levelAction`: the convolution action of `Λ[H]` on `H →₀ M`.
* `CompletedInduced Λ G M`: the module `M[[G]]`, with its `Λ[[G]]`-module structure.
* `CompletedInduced.map`: functoriality in `M`.
* `CompletedInduced.linearEquivSelf`: the `Λ[[G]]`-linear isomorphism of `Λ[[G]]` with the
  completed induced module of `Λ`.
* `CompletedInduced.sumValues`: the `Λ`-linear map `M[[G]] → M` summing the values, and
  `CompletedInduced.coinvariantsLinearEquiv` the resulting identification of the coinvariants of
  `M[[G]]` with `M`, for `M` finite projective.

## Main results

* `CompletedInduced.projective`: `M[[G]]` is projective for `M` finite projective.
* `CompletedInduced.mem_augmentationSubmodule_of_sumValues_eq_zero`: an element of `M[[G]]` whose
  values sum to zero lies in `I M[[G]]`, for `M` finite projective.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.GroupHomology

open CompletedGroupAlgebra MonoidAlgebra

/-- Evaluation of a sum of additive endomorphisms. -/
public theorem addMonoidEnd_add_apply {X : Type*} [AddCommMonoid X] (f g : AddMonoid.End X)
    (x : X) : (f + g) x = f x + g x :=
  rfl

section Level

variable (Λ : Type u) [Ring Λ] (M : Type u) [AddCommGroup M] [Module Λ M] (H : Type u) [Group H]

/-- Left translation of finitely supported functions: `h` sends `δ_x m` to `δ_{hx} m`. -/
public def translate : H →* AddMonoid.End (H →₀ M) where
  toFun h := Finsupp.mapDomain.addMonoidHom (h * ·)
  map_one' := AddMonoidHom.ext fun f => by
    change Finsupp.mapDomain (1 * ·) f = f
    simp only [one_mul]
    exact Finsupp.mapDomain_id
  map_mul' g h := AddMonoidHom.ext fun f => by
    change Finsupp.mapDomain ((g * h) * ·) f =
      Finsupp.mapDomain (g * ·) (Finsupp.mapDomain (h * ·) f)
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext x
    simp [mul_assoc]

/-- Left translation by `h` is push-forward along `x ↦ h x`. -/
@[simp]
public theorem translate_apply (h : H) (f : H →₀ M) :
    translate M H h f = Finsupp.mapDomain (h * ·) f :=
  rfl

/-- **The convolution action of `Λ[H]` on `M[H] = H →₀ M`**: `a δ_h` acts as `a` times left
translation by `h`. -/
public def levelAction : MonoidAlgebra Λ H →+* AddMonoid.End (H →₀ M) :=
  liftNCRingHom (Module.toAddMonoidEnd Λ (H →₀ M)) (translate M H) fun a h =>
    AddMonoidHom.ext fun f => by
      change a • Finsupp.mapDomain (h * ·) f = Finsupp.mapDomain (h * ·) (a • f)
      rw [Finsupp.mapDomain_smul]

/-- The element `a δ_h` acts on `f` as `a` times the left translate of `f` by `h`. -/
@[simp]
public theorem levelAction_single (h : H) (a : Λ) (f : H →₀ M) :
    levelAction Λ M H (single h a) f = a • Finsupp.mapDomain (h * ·) f := by
  simp [levelAction, liftNCRingHom, liftNC_single]
  rfl

variable {H} {H' : Type u} [Group H']

/-- Push-forward along a homomorphism is compatible with the convolution actions. -/
public theorem mapDomain_levelAction (π : H →* H') (x : MonoidAlgebra Λ H) (f : H →₀ M) :
    Finsupp.mapDomain π (levelAction Λ M H x f) =
      levelAction Λ M H' (mapDomainRingHom Λ π x) (Finsupp.mapDomain π f) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, addMonoidEnd_add_apply, Finsupp.mapDomain_add, hx, hy]
  | single h a =>
    rw [levelAction_single, mapDomainRingHom_apply, mapDomain_single, levelAction_single,
      Finsupp.mapDomain_smul, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 2
    funext x
    simp

/-- The convolution action of `Λ[H]` on `Λ[H]` is multiplication. -/
public theorem levelAction_coeff (x y : MonoidAlgebra Λ H) :
    levelAction Λ Λ H x y.coeff = (x * y).coeff := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y' hx hy => simp only [map_add, addMonoidEnd_add_apply, hx, hy, add_mul, coeff_add]
  | single h a =>
    rw [levelAction_single]
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y z hy hz => simp only [coeff_add, Finsupp.mapDomain_add, smul_add, hy, hz, mul_add]
    | single k b =>
      rw [coeff_single, Finsupp.mapDomain_single, single_mul_single, coeff_single,
        Finsupp.smul_single, smul_eq_mul]

/-- The convolution action commutes with applying a linear map to the values. -/
public theorem mapRange_levelAction {M' : Type u} [AddCommGroup M'] [Module Λ M']
    (φ : M →ₗ[Λ] M') (x : MonoidAlgebra Λ H) (f : H →₀ M) :
    Finsupp.mapRange φ φ.map_zero (levelAction Λ M H x f) =
      levelAction Λ M' H x (Finsupp.mapRange φ φ.map_zero f) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, addMonoidEnd_add_apply, Finsupp.mapRange_add (map_add φ), hx, hy, map_add,
      addMonoidEnd_add_apply]
  | single h a =>
    rw [levelAction_single, levelAction_single, Finsupp.mapRange_smul a _ (map_smul φ a),
      Finsupp.mapDomain_mapRange _ _ _ _ (map_add φ)]

/-- The sum of the values of `a • f` is the augmentation of `a` times the sum of the values of `f`.
-/
public theorem sum_levelAction (x : MonoidAlgebra Λ H) (f : H →₀ M) :
    (levelAction Λ M H x f).sum (fun _ m => m) =
      finiteAugmentation (Λ := Λ) H x • f.sum (fun _ m => m) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [Finsupp.sum]
  | add x y hx hy =>
    simp only [map_add, addMonoidEnd_add_apply, add_smul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hx, hy]
  | single h a =>
    rw [levelAction_single, finiteAugmentation_single,
      Finsupp.sum_smul_index' (h := fun _ m => m) (fun _ => rfl),
      Finsupp.sum_mapDomain_index (fun _ => smul_zero a) (fun _ _ _ => smul_add a _ _),
      Finsupp.smul_sum]

end Level

variable (Λ : Type u) [Ring Λ] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [Module Λ M]

/-- The quotient map `G/U → G/V` for open normal subgroups `U ≤ V`. -/
public abbrev levelMap {G : Type u} [Group G] [TopologicalSpace G] {U V : OpenNormalSubgroup G}
    (h : U ≤ V) : G ⧸ (U : Subgroup G) →* G ⧸ (V : Subgroup G) :=
  QuotientGroup.map _ _ (MonoidHom.id G) fun _ hx => h hx

/-- The compatible families of finitely supported functions `G/U →₀ M`. -/
public def completedInducedSubmodule :
    Submodule Λ (∀ U : OpenNormalSubgroup G, G ⧸ (U : Subgroup G) →₀ M) where
  carrier := {f | ∀ ⦃U V : OpenNormalSubgroup G⦄ (h : U ≤ V),
    Finsupp.mapDomain (levelMap h) (f U) = f V}
  add_mem' {f g} hf hg U V h := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finsupp.mapDomain_add] at *
    rw [hf h, hg h]
  zero_mem' U V h := by simp
  smul_mem' a f hf U V h := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, Finsupp.mapDomain_smul] at *
    rw [hf h]

/-- **The completed induced module** `M[[G]] = lim_U M[G/U]`. -/
public abbrev CompletedInduced : Type u := ↥(completedInducedSubmodule Λ G M)

namespace CompletedInduced

variable {Λ G M}

/-- The component of an element of `M[[G]]` at an open normal subgroup. -/
public abbrev level (f : CompletedInduced Λ G M) (U : OpenNormalSubgroup G) :
    G ⧸ (U : Subgroup G) →₀ M :=
  (f : ∀ U : OpenNormalSubgroup G, G ⧸ (U : Subgroup G) →₀ M) U

omit [IsTopologicalGroup G] in
/-- The components of an element of `M[[G]]` are compatible. -/
public theorem mapDomain_level {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (f : CompletedInduced Λ G M) : Finsupp.mapDomain (levelMap h) (f.level U) = f.level V :=
  f.2 h

omit [IsTopologicalGroup G] in
/-- Two elements of `M[[G]]` with the same components are equal. -/
public theorem ext {f g : CompletedInduced Λ G M} (h : ∀ U, f.level U = g.level U) : f = g :=
  Subtype.ext (funext h)

omit [IsTopologicalGroup G] in
/-- The components of a sum are the sums of the components. -/
@[simp]
public theorem level_add (f g : CompletedInduced Λ G M) (U : OpenNormalSubgroup G) :
    (f + g).level U = f.level U + g.level U :=
  rfl

omit [IsTopologicalGroup G] in
/-- The components of `0` are `0`. -/
@[simp]
public theorem level_zero (U : OpenNormalSubgroup G) :
    (0 : CompletedInduced Λ G M).level U = 0 :=
  rfl

omit [IsTopologicalGroup G] in
/-- The components of `a • f`, for `a : Λ`, are `a` times the components of `f`. -/
@[simp]
public theorem level_smul (a : Λ) (f : CompletedInduced Λ G M) (U : OpenNormalSubgroup G) :
    (a • f).level U = a • f.level U :=
  rfl

omit [IsTopologicalGroup G] in
/-- The transition map `Λ[G/U] → Λ[G/V]` is push-forward along `G/U → G/V`. -/
public theorem quotientAlgebraMap_eq {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    quotientAlgebraMap Λ h = mapDomainRingHom Λ (levelMap h) :=
  rfl

/-- An element of `M[[G]]` given by a compatible family. -/
public def mk (f : ∀ U : OpenNormalSubgroup G, G ⧸ (U : Subgroup G) →₀ M)
    (hf : ∀ ⦃U V : OpenNormalSubgroup G⦄ (h : U ≤ V), Finsupp.mapDomain (levelMap h) (f U) = f V) :
    CompletedInduced Λ G M :=
  ⟨f, hf⟩

omit [IsTopologicalGroup G] in
/-- The component at `U` of the element given by a compatible family is its member at `U`. -/
@[simp]
public theorem level_mk (f : ∀ U : OpenNormalSubgroup G, G ⧸ (U : Subgroup G) →₀ M) (hf)
    (U : OpenNormalSubgroup G) : (mk (Λ := Λ) f hf).level U = f U :=
  rfl

variable (Λ G M)

/-- The action of `Λ[[G]]` on `M[[G]]`, componentwise by convolution. -/
public def action : CompletedGroupAlgebra Λ G →+* AddMonoid.End (CompletedInduced Λ G M) where
  toFun a :=
    { toFun := fun f => mk (fun U => levelAction Λ M _ (eval U a) (f.level U)) fun U V h => by
        rw [mapDomain_levelAction, ← quotientAlgebraMap_eq, quotientAlgebraMap_eval,
          mapDomain_level]
      map_zero' := ext fun U => by simp
      map_add' := fun f g => ext fun U => by simp }
  map_one' := by
    ext f : 1
    exact ext fun U => by
      change levelAction Λ M _ (eval U 1) (f.level U) = f.level U
      simp
  map_mul' a b := by
    ext f : 1
    exact ext fun U => by
      change levelAction Λ M _ (eval U (a * b)) (f.level U) =
        levelAction Λ M _ (eval U a) (levelAction Λ M _ (eval U b) (f.level U))
      simp
  map_zero' := by
    ext f : 1
    exact ext fun U => by
      change levelAction Λ M _ (eval U 0) (f.level U) = 0
      simp
  map_add' a b := by
    ext f : 1
    exact ext fun U => by
      change levelAction Λ M _ (eval U (a + b)) (f.level U) =
        levelAction Λ M _ (eval U a) (f.level U) + levelAction Λ M _ (eval U b) (f.level U)
      simp [addMonoidEnd_add_apply]

/-- `M[[G]]` is a `Λ[[G]]`-module. -/
public instance instModule : Module (CompletedGroupAlgebra Λ G) (CompletedInduced Λ G M) :=
  Module.compHom _ (action Λ G M)

variable {Λ G M}

omit [IsTopologicalGroup G] in
/-- The component at `U` of `a • f`, for `a : Λ[[G]]`, is the convolution of the components of `a`
and `f` at `U`. -/
public theorem smul_level (a : CompletedGroupAlgebra Λ G) (f : CompletedInduced Λ G M)
    (U : OpenNormalSubgroup G) :
    (a • f).level U = levelAction Λ M _ (eval U a) (f.level U) :=
  rfl

/-- The element `δ_g m` of `M[[G]]`. -/
public def single (g : G) (m : M) : CompletedInduced Λ G M :=
  mk (fun U => Finsupp.single (g : G ⧸ (U : Subgroup G)) m) fun U V h => by
    rw [Finsupp.mapDomain_single]
    rfl

omit [IsTopologicalGroup G] in
/-- The component at `U` of `δ_g m` is `δ_{gU} m`. -/
@[simp]
public theorem level_single (g : G) (m : M) (U : OpenNormalSubgroup G) :
    (single (Λ := Λ) g m).level U = Finsupp.single (g : G ⧸ (U : Subgroup G)) m :=
  rfl

/-! ### Functoriality in the coefficients -/

/-- The `Λ[[G]]`-linear map `M[[G]] → M'[[G]]` induced by a `Λ`-linear map `M → M'`. -/
public def map {M' : Type u} [AddCommGroup M'] [Module Λ M'] (φ : M →ₗ[Λ] M') :
    CompletedInduced Λ G M →ₗ[CompletedGroupAlgebra Λ G] CompletedInduced Λ G M' where
  toFun f := mk (fun U => Finsupp.mapRange φ φ.map_zero (f.level U)) fun U V h => by
    rw [Finsupp.mapDomain_mapRange _ _ _ _ (map_add φ), mapDomain_level]
  map_add' f g := ext fun U => Finsupp.mapRange_add (hf := φ.map_zero) (map_add φ) _ _
  map_smul' a f := ext fun U => by
    simp only [level_mk, smul_level, RingHom.id_apply]
    exact mapRange_levelAction Λ M φ _ _

omit [IsTopologicalGroup G] in
/-- The component at `U` of `map φ f` is the component of `f` at `U` with `φ` applied to its
values. -/
@[simp]
public theorem map_level {M' : Type u} [AddCommGroup M'] [Module Λ M'] (φ : M →ₗ[Λ] M')
    (f : CompletedInduced Λ G M) (U : OpenNormalSubgroup G) :
    (map φ f).level U = Finsupp.mapRange φ φ.map_zero (f.level U) :=
  rfl

omit [IsTopologicalGroup G] in
/-- The map induced by the identity is the identity. -/
public theorem map_id (f : CompletedInduced Λ G M) : map (LinearMap.id : M →ₗ[Λ] M) f = f :=
  ext fun _U => Finsupp.mapRange_id _

omit [IsTopologicalGroup G] in
/-- The map induced by `ψ ∘ φ` is the composite of the maps induced by `φ` and `ψ`. -/
public theorem map_comp {M' M'' : Type u} [AddCommGroup M'] [Module Λ M'] [AddCommGroup M'']
    [Module Λ M''] (φ : M →ₗ[Λ] M') (ψ : M' →ₗ[Λ] M'') (f : CompletedInduced Λ G M) :
    map ψ (map φ f) = map (ψ ∘ₗ φ) f :=
  ext fun _U => (Finsupp.mapRange_comp _ ψ.map_zero _ φ.map_zero (ψ ∘ₗ φ).map_zero _).symm

/-! ### The case `M = Λ` -/

/-- `Λ[[G]]` regarded as `Λ[[G]]`-valued: the component of `a` at `U` as a function on `G/U`. -/
public def ofCompletedGroupAlgebra (a : CompletedGroupAlgebra Λ G) : CompletedInduced Λ G Λ :=
  mk (fun U => (eval U a).coeff) fun U V h => by
    rw [← quotientAlgebraMap_eval h a, quotientAlgebraMap_eq]
    rfl

/-- **`Λ[[G]] ⊗_Λ Λ = Λ[[G]]`**: the completed induced module of `Λ` is `Λ[[G]]`. -/
public def linearEquivSelf :
    CompletedGroupAlgebra Λ G ≃ₗ[CompletedGroupAlgebra Λ G] CompletedInduced Λ G Λ where
  toFun := ofCompletedGroupAlgebra
  invFun f := CompletedGroupAlgebra.mk (fun U => MonoidAlgebra.ofCoeff (f.level U)) fun U V h => by
    rw [quotientAlgebraMap_eq, ← mapDomain_level h f]
    rfl
  map_add' a b := ext fun U => by
    change (eval U (a + b)).coeff = (eval U a).coeff + (eval U b).coeff
    rw [map_add, coeff_add]
  map_smul' a b := ext fun U => by
    simp only [ofCompletedGroupAlgebra, level_mk, smul_eq_mul, map_mul, RingHom.id_apply,
      smul_level]
    exact (levelAction_coeff Λ _ _).symm
  left_inv a := CompletedGroupAlgebra.ext fun U => rfl
  right_inv f := ext fun U => rfl

/-! ### Projectivity -/

omit [IsTopologicalGroup G] in
/-- The components of a finite sum are the sums of the components. -/
@[simp]
public theorem level_sum {ι : Type*} (s : Finset ι) (f : ι → CompletedInduced Λ G M)
    (U : OpenNormalSubgroup G) : (∑ i ∈ s, f i).level U = ∑ i ∈ s, (f i).level U := by
  simp only [level, Submodule.coe_sum, Finset.sum_apply]

omit [IsTopologicalGroup G] in
/-- For `M = Λ^n`, an element `f` of `M[[G]]` is the sum over `j` of the image of its `j`-th
coordinate under the `j`-th inclusion. -/
public theorem sum_map_single_map_proj {n : ℕ} (f : CompletedInduced Λ G (Fin n → Λ)) :
    ∑ j, map (LinearMap.single Λ (fun _ => Λ) j) (map (LinearMap.proj j) f) = f :=
  ext fun U => by
    rw [level_sum]
    refine Finsupp.ext fun x => ?_
    rw [Finsupp.finsetSum_apply]
    simp only [map_level, Finsupp.mapRange_apply, LinearMap.coe_proj, Function.eval]
    exact Finset.univ_sum_single (f.level U x)

/-- The completed induced module of `Λ` is projective, being `Λ[[G]]`. -/
public instance projective_self :
    Module.Projective (CompletedGroupAlgebra Λ G) (CompletedInduced Λ G Λ) :=
  Module.Projective.of_equiv linearEquivSelf

/-- **The completed induced module of a finite projective module is projective.** -/
public instance projective [Module.Finite Λ M] [Module.Projective Λ M] :
    Module.Projective (CompletedGroupAlgebra Λ G) (CompletedInduced Λ G M) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ M
  have hfree : Module.Projective (CompletedGroupAlgebra Λ G) (CompletedInduced Λ G (Fin n → Λ)) :=
    Module.Projective.of_split (M := Fin n → CompletedGroupAlgebra Λ G)
      { toFun := fun f j => linearEquivSelf.symm (map (LinearMap.proj j) f)
        map_add' := fun f g => funext fun j => by simp
        map_smul' := fun a f => funext fun j => by simp }
      { toFun := fun g => ∑ j, map (LinearMap.single Λ (fun _ => Λ) j) (linearEquivSelf (g j))
        map_add' := fun f g => by simp [Finset.sum_add_distrib]
        map_smul' := fun a g => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← smul_eq_mul, map_smul, map_smul] }
      (LinearMap.ext fun f => by simpa using sum_map_single_map_proj f)
  exact Module.Projective.of_split (map i) (map p)
    (LinearMap.ext fun f => by
      rw [LinearMap.comp_apply, map_comp, hpi, LinearMap.id_apply, map_id])

/-! ### The sum of the values -/

variable (Λ G M) in
/-- The `Λ`-linear map `M[[G]] → M` summing the values (at any level). -/
public def sumValues : CompletedInduced Λ G M →ₗ[Λ] M where
  toFun f := (f.level topSubgroup).sum fun _ m => m
  map_add' f g := by
    rw [level_add, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  map_smul' a f := by
    rw [level_smul, Finsupp.sum_smul_index' (h := fun _ m => m) (fun _ => rfl), RingHom.id_apply,
      Finsupp.smul_sum]

omit [IsTopologicalGroup G] in
/-- The sum of the values may be computed at any level. -/
public theorem sumValues_eq (f : CompletedInduced Λ G M) (U : OpenNormalSubgroup G) :
    sumValues Λ G M f = (f.level U).sum fun _ m => m := by
  rw [sumValues, LinearMap.coe_mk, AddHom.coe_mk,
    ← mapDomain_level (fun _ _ => trivial : U ≤ topSubgroup) f,
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

omit [IsTopologicalGroup G] in
/-- `Σ (a f) = ε(a) Σ f`. -/
public theorem sumValues_smul (a : CompletedGroupAlgebra Λ G) (f : CompletedInduced Λ G M) :
    sumValues Λ G M (a • f) = augmentation a • sumValues Λ G M f := by
  rw [sumValues_eq _ topSubgroup, smul_level, sum_levelAction, sumValues_eq _ topSubgroup,
    augmentation]
  rfl

omit [IsTopologicalGroup G] in
/-- Summing the values commutes with the map induced by `φ`. -/
public theorem sumValues_map {M' : Type u} [AddCommGroup M'] [Module Λ M'] (φ : M →ₗ[Λ] M')
    (f : CompletedInduced Λ G M) : sumValues Λ G M' (map φ f) = φ (sumValues Λ G M f) := by
  rw [sumValues_eq _ topSubgroup, sumValues_eq _ topSubgroup, map_level,
    Finsupp.sum_mapRange_index (fun _ => rfl), map_finsuppSum]

omit [IsTopologicalGroup G] in
/-- The sum of the values of `δ_g m` is `m`. -/
@[simp]
public theorem sumValues_single (g : G) (m : M) : sumValues Λ G M (single g m) = m := by
  rw [sumValues_eq _ topSubgroup, level_single, Finsupp.sum_single_index rfl]

omit [IsTopologicalGroup G] in
/-- The sum of the values of `a ∈ Λ[[G]]`, regarded in the completed induced module of `Λ`, is the
augmentation of `a`. -/
public theorem sumValues_ofCompletedGroupAlgebra (a : CompletedGroupAlgebra Λ G) :
    sumValues Λ G Λ (ofCompletedGroupAlgebra a) = augmentation a := by
  have h := sum_levelAction Λ Λ (eval topSubgroup a) (1 : MonoidAlgebra Λ _).coeff
  rw [levelAction_coeff, mul_one] at h
  rw [sumValues_eq _ topSubgroup, augmentation, RingHom.comp_apply]
  simp only [MonoidAlgebra.one_def, coeff_single, Finsupp.sum_single_index, smul_eq_mul,
    mul_one] at h
  exact h

/-! ### The coinvariants of `M[[G]]` -/

/-- An element of `M[[G]]` whose values sum to zero lies in `I M[[G]]`, for `M = Λ`. -/
public theorem mem_augmentationSubmodule_of_sumValues_eq_zero_self (f : CompletedInduced Λ G Λ)
    (hf : sumValues Λ G Λ f = 0) : f ∈ augmentationSubmodule Λ G (CompletedInduced Λ G Λ) := by
  obtain ⟨a, rfl⟩ := linearEquivSelf.surjective f
  have ha : augmentation a = 0 := by rwa [← sumValues_ofCompletedGroupAlgebra]
  have : linearEquivSelf a = a • linearEquivSelf (1 : CompletedGroupAlgebra Λ G) := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [this]
  exact smul_mem_augmentationSubmodule ha _

/-- **An element of `M[[G]]` whose values sum to zero lies in `I M[[G]]`**, for `M` finite
projective. -/
public theorem mem_augmentationSubmodule_of_sumValues_eq_zero [Module.Finite Λ M]
    [Module.Projective Λ M] (f : CompletedInduced Λ G M) (hf : sumValues Λ G M f = 0) :
    f ∈ augmentationSubmodule Λ G (CompletedInduced Λ G M) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ M
  have hf' : f = map p (∑ j, map (LinearMap.single Λ (fun _ => Λ) j)
      (map (LinearMap.proj j) (map i f))) := by
    rw [sum_map_single_map_proj, map_comp, hpi, map_id]
  rw [hf']
  refine augmentationSubmodule_le_comap (map p) (Submodule.sum_mem _ fun j _ => ?_)
  refine augmentationSubmodule_le_comap (map (LinearMap.single Λ (fun _ => Λ) j)) ?_
  refine mem_augmentationSubmodule_of_sumValues_eq_zero_self _ ?_
  rw [sumValues_map, sumValues_map, hf, map_zero, map_zero]

/-- `Σ` kills `I M[[G]]`. -/
public theorem sumValues_eq_zero_of_mem {f : CompletedInduced Λ G M}
    (hf : f ∈ augmentationSubmodule Λ G (CompletedInduced Λ G M)) : sumValues Λ G M f = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, n, rfl⟩ := hx
    rw [sumValues_smul, ha, zero_smul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [sumValues_smul, hx, smul_zero]

variable (Λ G M) in
/-- The `Λ`-linear map from the coinvariants of `M[[G]]` to `M` induced by the sum of the values.
-/
public def coinvariantsToSelf :
    (coinvariantsFunctor Λ G).obj (ModuleCat.of (CompletedGroupAlgebra Λ G)
      (CompletedInduced Λ G M)) →ₗ[Λ] M where
  toFun x := Quotient.liftOn' x (sumValues Λ G M) fun f g hfg => by
    have h : -f + g ∈ augmentationSubmodule Λ G (CompletedInduced Λ G M) :=
      QuotientAddGroup.leftRel_apply.mp hfg
    have h0 := sumValues_eq_zero_of_mem h
    rwa [map_add, map_neg, neg_add_eq_zero] at h0
  map_add' x y := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact map_add (sumValues Λ G M) f g
  map_smul' a x := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change sumValues Λ G M ((const a : CompletedGroupAlgebra Λ G) • f) = a • sumValues Λ G M f
    rw [sumValues_smul, augmentation_const]

/-- On representatives, the map from the coinvariants of `M[[G]]` to `M` is the sum of the values.
-/
public theorem coinvariantsToSelf_mk (f : CompletedInduced Λ G M) :
    coinvariantsToSelf Λ G M (Submodule.Quotient.mk f) = sumValues Λ G M f :=
  rfl

variable (Λ G M) in
/-- **The coinvariants of `M[[G]]` are `M`**, through the sum of the values, for `M` finite
projective. -/
public def coinvariantsLinearEquiv [Module.Finite Λ M] [Module.Projective Λ M] :
    (coinvariantsFunctor Λ G).obj (ModuleCat.of (CompletedGroupAlgebra Λ G)
      (CompletedInduced Λ G M)) ≃ₗ[Λ] M :=
  LinearEquiv.ofBijective (coinvariantsToSelf Λ G M)
    ⟨fun x y hxy => by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [coinvariantsToSelf_mk, coinvariantsToSelf_mk] at hxy
      change Submodule.Quotient.mk f = Submodule.Quotient.mk g
      rw [Submodule.Quotient.eq]
      exact mem_augmentationSubmodule_of_sumValues_eq_zero _ (by rw [map_sub, hxy, sub_self]),
    fun m => ⟨Submodule.Quotient.mk (single 1 m), sumValues_single 1 m⟩⟩

/-- On representatives, the identification of the coinvariants of `M[[G]]` with `M` is the sum of
the values. -/
public theorem coinvariantsLinearEquiv_mk [Module.Finite Λ M] [Module.Projective Λ M]
    (f : CompletedInduced Λ G M) :
    coinvariantsLinearEquiv Λ G M (Submodule.Quotient.mk f) = sumValues Λ G M f :=
  rfl

end CompletedInduced

end Stacks.GroupHomology

end
