module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairing

/-!
# Changing the dualizing object of a Yoneda duality pairing

For a morphism `φ : D' ⟶ D` and a trace `t` on `Ext^N(O, D)`, the trace `t ∘ φ_*` on
`Ext^N(O, D')` gives the same duality at an object `F` as `t` does, provided
`φ_* : Ext^j(F, D') → Ext^j(F, D)` is bijective in every degree.  This is how duality on an open
`V ⊂ U` (dualizing object `j_{V!}Λ`, trace on `H^{2d}_c(V)`) is compared with duality at
`j_{V!}F` for the dualizing object `j_{U!}Λ` of `U` (trace on `H^{2d}_c(U)`): both
`Ext(j_{V!}F, -)` are `Ext_V(F, Λ)`.

## Main definitions

* `CategoryTheory.Abelian.Ext.pullbackTrace`: the trace `t ∘ φ_*` on `Ext^N(O, D')`.

## Main results

* `CategoryTheory.Abelian.Ext.isDualityPerfect_pullbackTrace_iff`: if `φ_*` is bijective on
  `Ext^j(F, -)` in every degree, duality at `F` for `(D', t ∘ φ_*)` is equivalent to duality at
  `F` for `(D, t)`.
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {O D D' : C} {N : ℕ} {A : Type*} [AddCommGroup A] (t : Ext O D N →+ A) (φ : D' ⟶ D)

/-- The trace `z ↦ t (φ_* z)` on `Ext^N(O, D')` induced by `φ : D' ⟶ D`. -/
def pullbackTrace : Ext O D' N →+ A :=
  t.comp (AddMonoidHom.mk' (fun z => z.comp (mk₀ φ) (add_zero N))
    (fun z z' => by simp [Ext.add_comp]))

/-- The trace `pullbackTrace t φ` sends `z` to `t (φ_* z)`. -/
lemma pullbackTrace_apply (z : Ext O D' N) :
    pullbackTrace t φ z = t (z.comp (mk₀ φ) (add_zero N)) :=
  rfl

/-- **Duality along a change of dualizing object.**  If `φ : D' ⟶ D` induces bijections
`Ext^j(F, D') → Ext^j(F, D)`, then duality holds at `F` for `(D', t ∘ φ_*)` if and only if it
holds for `(D, t)`. -/
theorem isDualityPerfect_pullbackTrace_iff (F : C)
    (hφ : ∀ j : ℕ, Function.Bijective (fun y : Ext F D' j => y.comp (mk₀ φ) (add_zero j))) :
    IsDualityPerfect O D' N (pullbackTrace t φ) F ↔ IsDualityPerfect O D N t F := by
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun h => ?_
  let β : Ext F D' j ≃+ Ext F D j := AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun y => y.comp (mk₀ φ) (add_zero j)) (fun y y' => by simp [Ext.add_comp]))
    (hφ j)
  let pre : (Ext F D j →+ A) ≃ (Ext F D' j →+ A) :=
    { toFun ψ := ψ.comp β.toAddMonoidHom
      invFun ψ := ψ.comp β.symm.toAddMonoidHom
      left_inv ψ := by ext; simp
      right_inv ψ := by ext; simp }
  have key : pre ∘ dualityPairing O D N t F h =
      dualityPairing O D' N (pullbackTrace t φ) F h := by
    funext x
    ext y
    change t (x.comp (y.comp (mk₀ φ) (add_zero j)) h) = t ((x.comp y h).comp (mk₀ φ) (add_zero N))
    rw [comp_assoc_of_third_deg_zero]
  rw [← key]
  exact Function.Bijective.of_comp_iff' pre.bijective _

end CategoryTheory.Abelian.Ext
