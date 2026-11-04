module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairing
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.ConnectingSurjective

/-!
# Duality at an induced object

Let `L : C ⥤ D` and `R : D ⥤ C` be exact functors with adjunctions `L ⊣ R` and `R ⊣ L`; for a
finite étale cover `π : Y → X` these are `π⁻¹` and `π_* = π_!`. A trace `t : Ext^N(O, E) → A` on
`C` induces a trace on `D`,

`t_D(z) = t (η_O ∘ R z ∘ ε'_E) : Ext^N(L O, L E) → A`,

with `η` the unit of `L ⊣ R` and `ε'` the counit of `R ⊣ L` (the trace map `π_* π⁻¹ E → E`).
Under the identifications `Ext^i(O, R M) ≅ Ext^i(L O, M)` and `Ext^j(M, L E) ≅ Ext^j(R M, E)` of
the two adjunctions the Yoneda pairing of `R M` on `C` corresponds to the Yoneda pairing of `M`
on `D`, so duality holds at `R M` with respect to `t` if and only if it holds at `M` with respect
to `t_D`. For étale sheaves: Poincaré duality on `X` with coefficients `π_* M` is Poincaré
duality on `Y` with coefficients `M`, for the induced trace on `Y`.

## Main results

* `CategoryTheory.Abelian.Ext.transferTrace`: the induced trace `t_D`.
* `CategoryTheory.Abelian.Ext.transferTrace_comp_extMap`: compatibility of the pairings.
* `CategoryTheory.Abelian.Ext.isDualityPerfect_obj_iff`: duality at `R M` iff at `M`.
* `CategoryTheory.Abelian.Ext.surjective_transferTrace_id`: the transfer is onto when the
  counit `R L E → E` is onto with kernel acyclic in degree `N + 1`.
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.Abelian.Ext

open Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C] [EnoughInjectives D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (adj₁ : L ⊣ R) (adj₂ : R ⊣ L) (O E : C) (N : ℕ) {A : Type*} [AddCommGroup A]
  (t : Ext.{w} O E N →+ A)

/-- The trace `z ↦ t (η_O ∘ R z ∘ ε'_E)` on `Ext^N(L O, L E)` induced by a trace on
`Ext^N(O, E)`. -/
noncomputable def transferTrace : Ext.{w'} (L.obj O) (L.obj E) N →+ A :=
  t.comp (AddMonoidHom.mk' (fun z => (mk₀ (adj₁.unit.app O)).comp
      ((z.mapExactFunctor R).comp (mk₀ (adj₂.counit.app E)) (add_zero N)) (zero_add N))
    (fun z z' => by simp [Ext.add_comp, Ext.comp_add]))

omit [EnoughInjectives C] [EnoughInjectives D] [L.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] in
/-- The induced trace `transferTrace adj₁ adj₂ O E N t` sends `z` to `t (η_O ∘ R z ∘ ε'_E)`. -/
lemma transferTrace_apply (z : Ext.{w'} (L.obj O) (L.obj E) N) :
    transferTrace adj₁ adj₂ O E N t z = t ((mk₀ (adj₁.unit.app O)).comp
      ((z.mapExactFunctor R).comp (mk₀ (adj₂.counit.app E)) (add_zero N)) (zero_add N)) :=
  rfl

omit [EnoughInjectives D] in
/-- **The pairings correspond.** For `x ∈ Ext^i(O, R M)` and `y ∈ Ext^j(M, L E)`,
`t_D (x♭ ∘ y) = t (x ∘ y♯)`, where `x♭ ∈ Ext^i(L O, M)` and `y♯ ∈ Ext^j(R M, E)` are the
adjoint classes. -/
theorem transferTrace_comp_extMap (M : D) {i j : ℕ} (h : i + j = N)
    (x : Ext.{w} O (R.obj M) i) (y : Ext.{w'} M (L.obj E) j) :
    transferTrace adj₁ adj₂ O E N t ((Stacks.ExtAdjunction.extMap adj₁ O M i x).comp y h) =
      t (x.comp (Stacks.ExtAdjunction.extMap adj₂ M E j y) h) := by
  rw [transferTrace_apply, Stacks.ExtAdjunction.extMap_apply, Stacks.ExtAdjunction.extMap_apply]
  congr 1
  have e1 : (((x.mapExactFunctor L).comp (mk₀ (adj₁.counit.app M)) (add_zero i)).comp y
      h).mapExactFunctor R = ((x.mapExactFunctor (L ⋙ R)).comp
        (mk₀ (R.map (adj₁.counit.app M))) (add_zero i)).comp (y.mapExactFunctor R) h := by
    rw [mapExactFunctor_comp, mapExactFunctor_comp, mapExactFunctor_mk₀,
      Stacks.ExtFunctorial.mapExactFunctor_comp_functor L R O i x]
  have e2 : (mk₀ (adj₁.unit.app O)).comp (x.mapExactFunctor (L ⋙ R)) (zero_add i) =
      x.comp (mk₀ (adj₁.unit.app (R.obj M))) (add_zero i) := by
    simpa only [Stacks.ExtFunctorial.mapExactFunctor_id] using
      Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor adj₁.unit O i x
  rw [e1, comp_assoc_of_third_deg_zero, comp_assoc_of_second_deg_zero,
    ← comp_assoc (mk₀ (adj₁.unit.app O)) (x.mapExactFunctor (L ⋙ R)) _ (zero_add i) h
      (by omega), e2, comp_assoc_of_second_deg_zero, mk₀_comp_mk₀_assoc,
    adj₁.right_triangle_components, mk₀_id_comp]

/-- **Duality at an induced object.** Duality holds at `R M` for the trace `t` if and only if it
holds at `M` for the induced trace `transferTrace adj₁ adj₂ O E N t`. -/
theorem isDualityPerfect_obj_iff (M : D) :
    IsDualityPerfect O E N t (R.obj M) ↔
      IsDualityPerfect (L.obj O) (L.obj E) N (transferTrace adj₁ adj₂ O E N t) M := by
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun h => ?_
  let α := Stacks.ExtAdjunction.extMap adj₁ O M i
  have hα : Function.Bijective α := Stacks.ExtAdjunction.extMap_bijective adj₁ O M i
  let eβ := AddEquiv.ofBijective (Stacks.ExtAdjunction.extMap adj₂ M E j)
    (Stacks.ExtAdjunction.extMap_bijective adj₂ M E j)
  let pre : (Ext.{w} (R.obj M) E j →+ A) ≃ (Ext.{w'} M (L.obj E) j →+ A) :=
    { toFun φ := φ.comp eβ.toAddMonoidHom
      invFun φ := φ.comp eβ.symm.toAddMonoidHom
      left_inv φ := by ext; simp
      right_inv φ := by ext; simp }
  have hcomp : (dualityPairing (L.obj O) (L.obj E) N (transferTrace adj₁ adj₂ O E N t) M h) ∘ α =
      pre ∘ (dualityPairing O E N t (R.obj M) h) := by
    funext x
    ext y
    simp only [pre, Function.comp_apply, Equiv.coe_fn_mk, AddMonoidHom.comp_apply,
      dualityPairing_apply]
    exact transferTrace_comp_extMap adj₁ adj₂ O E N t M h x y
  refine ⟨fun hX => (Function.Bijective.of_comp_iff _ hα).1 ?_,
    fun hY => (Function.Bijective.of_comp_iff' pre.bijective _).1 ?_⟩
  · rw [hcomp]
    exact pre.bijective.comp hX
  · rw [← hcomp]
    exact hY.comp hα

omit [EnoughInjectives D] in
/-- **The transfer `Ext^N(L O, L E) → Ext^N(O, E)` is onto** when the counit `R L E → E` is an
epimorphism whose kernel `K` has `Ext^{N+1}(O, K) = 0`: for a finite étale cover of a curve the
trace map `π_* Λ → Λ` is onto and `H³` vanishes, so the transfer `H²(Y, Λ) → H²(X, Λ)` is onto. -/
theorem surjective_transferTrace_id [Epi (adj₂.counit.app E)]
    (hvan : Subsingleton (Ext.{w} O (kernel (adj₂.counit.app E)) (N + 1))) :
    Function.Surjective (transferTrace adj₁ adj₂ O E N (AddMonoidHom.id _)) := by
  intro w
  let S := ShortComplex.mk (kernel.ι (adj₂.counit.app E)) (adj₂.counit.app E)
    (kernel.condition _)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel (adj₂.counit.app E)
      epi_g := inferInstanceAs (Epi (adj₂.counit.app E)) }
  obtain ⟨x, hx⟩ := surjective_comp_mk₀_g_of_subsingleton hS O N hvan w
  refine ⟨(Stacks.ExtAdjunction.extMap adj₁ O (L.obj E) N x).comp (mk₀ (𝟙 (L.obj E)))
    (add_zero N), ?_⟩
  rwa [transferTrace_comp_extMap adj₁ adj₂ O E N _ (L.obj E) (add_zero N),
    Stacks.ExtAdjunction.extMap_apply, mapExactFunctor_mk₀, R.map_id, mk₀_id_comp]

end CategoryTheory.Abelian.Ext
