module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairingShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairingAdjunction

/-!
# Duality at an object pushed forward along a closed immersion

Let `L : C ⥤ D` and `R : D ⥤ C` be exact functors with an adjunction `L ⊣ R`; for a closed
immersion `ι : T̄ → X̄` of schemes these are `ι⁻¹` and `ι_*`. Fix a trace `t : Ext^N(O, D_C) → A`
on `C`, an object `E` of `D` and a class `Γ ∈ Ext^c(R E, D_C)` (a *Gysin class*: for a smooth
`T` of codimension `c'` in a smooth `W`, `c = 2c'` and `Γ` is the class of purity). They induce
the trace

`t_Γ(z) = t (η_O ∘ R z ∘ Γ) : Ext^{N - c}(L O, E) → A`

with `η` the unit of `L ⊣ R`. Under `Ext^i(O, R M) ≅ Ext^i(L O, M)` (the adjunction) and the
map `Ext^j(M, E) → Ext^{j + c}(R M, D_C)`, `y ↦ R y ∘ Γ`, the Yoneda pairing of `R M` on `C`
corresponds to the Yoneda pairing of `M` on `D` with respect to `t_Γ`. When the second map is
bijective (purity), `Ext^i(O, R M)` vanishes above `N - c` and `Ext^j(R M, D_C)` below `c`,
duality at `R M` for `t` is duality at `M` for `t_Γ`. This is the step of the proof of
Poincaré duality that passes from a smooth variety to a smooth closed stratum of its boundary.

## Main results

* `CategoryTheory.Abelian.Ext.gysinTrace`: the trace `t_Γ`.
* `CategoryTheory.Abelian.Ext.gysinTrace_comp_extMap`: compatibility of the pairings.
* `CategoryTheory.Abelian.Ext.isDualityPerfect_obj_iff_gysinTrace`: duality at `R M` iff at `M`.
* `CategoryTheory.Abelian.Ext.isDualityPerfect_iff_compTrace`: in one category, duality at `F`
  for a dualizing object `D` iff for `D'`, along `Γ ∈ Ext^c(D', D)` with `y ↦ y ∘ Γ` bijective.
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
  (adj : L ⊣ R) (O : C) (E : D) (DC : C) {N N' c : ℕ} (hN : N' + c = N)
  (Γ : Ext.{w} (R.obj E) DC c) {A : Type*} [AddCommGroup A] (t : Ext.{w} O DC N →+ A)

/-- The trace `z ↦ t (η_O ∘ R z ∘ Γ)` on `Ext^{N'}(L O, E)` induced by a trace on
`Ext^N(O, D_C)` and a class `Γ ∈ Ext^c(R E, D_C)`, `N' + c = N`. -/
noncomputable def gysinTrace : Ext.{w'} (L.obj O) E N' →+ A :=
  t.comp (((mk₀ (adj.unit.app O)).precomp DC (zero_add N)).comp
    ((Γ.postcomp _ hN).comp (R.mapExtAddHom (L.obj O) E N')))

omit [EnoughInjectives C] [EnoughInjectives D] [L.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] in
/-- The value of `gysinTrace` at `z` is `t (η_O ∘ R z ∘ Γ)`. -/
lemma gysinTrace_apply (z : Ext.{w'} (L.obj O) E N') :
    gysinTrace adj O E DC hN Γ t z =
      t ((mk₀ (adj.unit.app O)).comp ((z.mapExactFunctor R).comp Γ hN) (zero_add N)) :=
  rfl

omit [EnoughInjectives D] in
/-- **The pairings correspond.** For `x ∈ Ext^i(O, R M)` and `y ∈ Ext^j(M, E)`,
`t_Γ (x♭ ∘ y) = t (x ∘ (R y ∘ Γ))`, where `x♭ ∈ Ext^i(L O, M)` is the adjoint class. -/
theorem gysinTrace_comp_extMap (M : D) {i j : ℕ} (h : i + j = N')
    (x : Ext.{w} O (R.obj M) i) (y : Ext.{w'} M E j) :
    gysinTrace adj O E DC hN Γ t ((Stacks.ExtAdjunction.extMap adj O M i x).comp y h) =
      t (x.comp ((y.mapExactFunctor R).comp Γ rfl) (by omega)) := by
  rw [gysinTrace_apply, Stacks.ExtAdjunction.extMap_apply]
  congr 1
  have e1 : (((x.mapExactFunctor L).comp (mk₀ (adj.counit.app M)) (add_zero i)).comp y
      h).mapExactFunctor R = ((x.mapExactFunctor (L ⋙ R)).comp
        (mk₀ (R.map (adj.counit.app M))) (add_zero i)).comp (y.mapExactFunctor R) h := by
    rw [mapExactFunctor_comp, mapExactFunctor_comp, mapExactFunctor_mk₀,
      Stacks.ExtFunctorial.mapExactFunctor_comp_functor L R O i x]
  have e2 : (mk₀ (adj.unit.app O)).comp (x.mapExactFunctor (L ⋙ R)) (zero_add i) =
      x.comp (mk₀ (adj.unit.app (R.obj M))) (add_zero i) := by
    have hnat := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor adj.unit O i x
    rwa [Stacks.ExtFunctorial.mapExactFunctor_id] at hnat
  rw [e1, comp_assoc_of_second_deg_zero,
    comp_assoc (x.mapExactFunctor (L ⋙ R)) _ Γ h rfl (by omega),
    ← comp_assoc (mk₀ (adj.unit.app O)) (x.mapExactFunctor (L ⋙ R)) _ (zero_add i) (by omega)
      (by omega), e2, comp_assoc_of_second_deg_zero,
    comp_assoc (mk₀ (R.map (adj.counit.app M))) (y.mapExactFunctor R) Γ (zero_add j) rfl
      (by omega), mk₀_comp_mk₀_assoc, adj.right_triangle_components, mk₀_id_comp]

/-- **Duality at a pushed-forward object.** If `y ↦ R y ∘ Γ` is bijective
`Ext^j(M, E) → Ext^{j + c}(R M, D_C)` for every `j`, `Ext^i(O, R M) = 0` for `i > N'` and
`Ext^j(R M, D_C) = 0` for `j < c`, then duality holds at `R M` for `t` if and only if it holds at
`M` for the induced trace `t_Γ`. -/
theorem isDualityPerfect_obj_iff_gysinTrace (M : D)
    (hβ : ∀ j, Function.Bijective
      (fun y : Ext.{w'} M E j => (y.mapExactFunctor R).comp Γ (rfl : j + c = j + c)))
    (hO : ∀ i, N' < i → Subsingleton (Ext.{w} O (R.obj M) i))
    (hD : ∀ j, j < c → Subsingleton (Ext.{w} (R.obj M) DC j)) :
    IsDualityPerfect O DC N t (R.obj M) ↔
      IsDualityPerfect (L.obj O) E N' (gysinTrace adj O E DC hN Γ t) M := by
  let β : ∀ j, Ext.{w'} M E j →+ Ext.{w} (R.obj M) DC (j + c) := fun j =>
    (Γ.postcomp _ rfl).comp (R.mapExtAddHom M E j)
  exact isDualityPerfect_iff_of_addEquiv t (gysinTrace adj O E DC hN Γ t) c hN.symm
    (fun i => AddEquiv.ofBijective (Stacks.ExtAdjunction.extMap adj O M i)
      (Stacks.ExtAdjunction.extMap_bijective adj O M i))
    (fun j => AddEquiv.ofBijective (β j) (hβ j))
    (fun i j h x y => gysinTrace_comp_extMap adj O E DC hN Γ t M h x y) hO hD

section ChangeOfDualizing

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {O D D' : C} {N N' c : ℕ}
  (hN : N' + c = N) (Γ : Ext.{w} D' D c) {A : Type*} [AddCommGroup A] (t : Ext.{w} O D N →+ A)

/-- The trace `z ↦ t (z ∘ Γ)` on `Ext^{N'}(O, D')` induced by a trace on `Ext^N(O, D)` and a
class `Γ ∈ Ext^c(D', D)`, `N' + c = N`. -/
noncomputable def compTrace : Ext.{w} O D' N' →+ A :=
  t.comp (Γ.postcomp O hN)

/-- The value of `compTrace` at `z` is `t (z ∘ Γ)`. -/
lemma compTrace_apply (z : Ext.{w} O D' N') : compTrace hN Γ t z = t (z.comp Γ hN) :=
  rfl

/-- **Change of dualizing object along a Gysin class.** If `y ↦ y ∘ Γ` is bijective
`Ext^j(F, D') → Ext^{j + c}(F, D)` for every `j`, `Ext^i(O, F) = 0` for `i > N'` and
`Ext^j(F, D) = 0` for `j < c`, then duality at `F` for `(D, t)` is duality at `F` for
`(D', t ∘ Γ)`. For `c = 0` and `Γ = mk₀ φ` this is `isDualityPerfect_pullbackTrace_iff`; for a
smooth stratum `T` of codimension `c'` of a smooth `W`, both locally closed in a proper `X̄`,
`D = (W → X̄)_! Λ`, `D' = (T → X̄)_! Λ`, `c = 2c'` and `Γ` the purity class, it passes Poincaré
duality from `T` to the sheaves on `W` supported on `T`. -/
theorem isDualityPerfect_iff_compTrace (F : C)
    (hβ : ∀ j, Function.Bijective
      (fun y : Ext.{w} F D' j => y.comp Γ (rfl : j + c = j + c)))
    (hO : ∀ i, N' < i → Subsingleton (Ext.{w} O F i))
    (hD : ∀ j, j < c → Subsingleton (Ext.{w} F D j)) :
    IsDualityPerfect O D N t F ↔ IsDualityPerfect O D' N' (compTrace hN Γ t) F :=
  isDualityPerfect_iff_of_addEquiv t (compTrace hN Γ t) c hN.symm (fun i => AddEquiv.refl _)
    (fun j => AddEquiv.ofBijective (Γ.postcomp F rfl) (hβ j))
    (fun i j h x y => by
      change t ((x.comp y h).comp Γ hN) = t (x.comp (y.comp Γ rfl) _)
      rw [comp_assoc x y Γ h rfl (by omega)]) hO hD

end ChangeOfDualizing

end CategoryTheory.Abelian.Ext
