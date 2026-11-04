module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Descent along a commutative square of adjunctions

Consider four adjunctions `Lₐ ⊣ Rₐ`, `L_h ⊣ R_h`, `L_b ⊣ R_b`, `L_c ⊣ R_c` arranged in a square
```
  𝒯 --R_h--> 𝒱
  |           |
 R_b         Rₐ
  v           v
  𝒴 --R_c--> 𝒳
```
whose right adjoints commute, `R_c ∘ R_b ≅ Rₐ ∘ R_h`. This is the shape of the comparison of a
morphism of topoi `a : Sh(𝒱) → Sh(𝒳)` with a second one `b` through comparison morphisms `h` and
`c` along which the inverse images are fully faithful; in the application `a` is the augmentation
of the small étale site of a simplicial algebraic space, `b` the augmentation of the total ph site
and `h`, `c` the comparisons of the ph and the étale topologies (the square of Stacks 0DHJ).

This file records the formal half of the argument of Stacks 0DHL.

* If the units of `h`, `b` and `c` are invertible at the relevant objects, then so is the unit of
  `a`: the unit of the composite adjunction `Lₐ ⋙ L_h ⊣ R_h ⋙ Rₐ` is the unit of `a` followed by
  `Rₐ` of the unit of `h`, and it agrees, through the square, with the unit of the composite
  `L_c ⋙ L_b ⊣ R_b ⋙ R_c`.
* In abelian categories, if moreover `M = L_b(L_c x)` is acyclic for `R_h` and for `R_b`, and
  `L_c x` is acyclic for `R_c`, then `Lₐ x` is acyclic for `Rₐ`. Indeed `Lₐ x = R_h M` by the unit
  of `h`, so `Rᵠ Rₐ (Lₐ x) = Rᵠ(Rₐ ∘ R_h)(M) = Rᵠ(R_c ∘ R_b)(M) = Rᵠ R_c (L_c x)`, the first and
  last steps being the collapse of the Grothendieck spectral sequence at an acyclic object
  (`Stacks.RightDerivedComp.objIso`), `R_h` and `R_b` preserving injectives.

## Main results

* `CategoryTheory.Adjunction.isIso_unit_app_of_comp_iso`: the unit of `a` from the units of `h`,
  `b` and `c`.
* `CategoryTheory.Adjunction.isZero_rightDerived_of_comp_iso`: the acyclicity of `Lₐ x` for `Rₐ`.

## References

* [Stacks Project, Tag 0DHL](https://stacks.math.columbia.edu/tag/0DHL)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {𝒳 𝒱 𝒯 𝒴 : Type*} [Category* 𝒳] [Category* 𝒱] [Category* 𝒯] [Category* 𝒴]
  {Lₐ : 𝒳 ⥤ 𝒱} {Rₐ : 𝒱 ⥤ 𝒳} {L_h : 𝒱 ⥤ 𝒯} {R_h : 𝒯 ⥤ 𝒱}
  {L_b : 𝒴 ⥤ 𝒯} {R_b : 𝒯 ⥤ 𝒴} {L_c : 𝒳 ⥤ 𝒴} {R_c : 𝒴 ⥤ 𝒳}
  (adjₐ : Lₐ ⊣ Rₐ) (adj_h : L_h ⊣ R_h) (adj_b : L_b ⊣ R_b) (adj_c : L_c ⊣ R_c)
  (α : R_b ⋙ R_c ≅ R_h ⋙ Rₐ)

/-- **Units along an isomorphism of right adjoints.** For adjunctions `L ⊣ R` and `L' ⊣ R'` with
`R ≅ R'`, the unit of the first is invertible at `x` exactly when that of the second is. -/
theorem isIso_unit_app_iff_of_iso {L L' : 𝒳 ⥤ 𝒱} {R R' : 𝒱 ⥤ 𝒳} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (e : R ≅ R') (x : 𝒳) : IsIso (adj.unit.app x) ↔ IsIso (adj'.unit.app x) := by
  have h : (adj.ofNatIsoRight e).unit.app x = adj.unit.app x ≫ e.hom.app _ := by
    simp [Adjunction.ofNatIsoRight]
  rw [← unit_leftAdjointUniq_hom_app (adj.ofNatIsoRight e) adj' x, h, isIso_comp_right_iff,
    isIso_comp_right_iff]

/-- **Left adjoints of isomorphic right adjoints are isomorphic.** -/
def leftAdjointIsoOfIso {L L' : 𝒳 ⥤ 𝒱} {R R' : 𝒱 ⥤ 𝒳} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (e : R ≅ R') : L ≅ L' :=
  leftAdjointUniq (adj.ofNatIsoRight e) adj'

/-- **The square on left adjoints.** The left adjoints of the two composites around a square of
right adjoints are isomorphic: `Lₐ ⋙ L_h ≅ L_c ⋙ L_b`. -/
def leftAdjointCompIsoOfCompIso : Lₐ ⋙ L_h ≅ L_c ⋙ L_b :=
  leftAdjointUniq (adjₐ.comp adj_h) ((adj_c.comp adj_b).ofNatIsoRight α)

include α in
/-- **The unit of `a` from the units around a commutative square.** If the right adjoints of a
square of adjunctions commute, `R_c ∘ R_b ≅ Rₐ ∘ R_h`, and the units of `c` at `x`, of `b` at
`L_c x` and of `h` at `Lₐ x` are isomorphisms, then the unit of `a` at `x` is an isomorphism. -/
theorem isIso_unit_app_of_comp_iso (x : 𝒳) [IsIso (adj_c.unit.app x)]
    [IsIso (adj_b.unit.app (L_c.obj x))] [IsIso (adj_h.unit.app (Lₐ.obj x))] :
    IsIso (adjₐ.unit.app x) := by
  have := (isIso_unit_app_iff_of_iso (adj_c.comp adj_b) (adjₐ.comp adj_h) α x).1
    (by rw [comp_unit_app]; infer_instance)
  rwa [comp_unit_app, isIso_comp_right_iff] at this

include α in
/-- **The units around a commutative square**, for units invertible everywhere. -/
theorem isIso_unit_of_comp_iso [IsIso adj_c.unit] [IsIso adj_b.unit] [IsIso adj_h.unit] :
    IsIso adjₐ.unit :=
  have : ∀ x, IsIso (adjₐ.unit.app x) := fun x ↦
    isIso_unit_app_of_comp_iso adjₐ adj_h adj_b adj_c α x
  NatIso.isIso_of_isIso_app _

section Abelian

variable [Abelian 𝒳] [Abelian 𝒱] [Abelian 𝒯] [Abelian 𝒴]
  [HasInjectiveResolutions 𝒯] [HasInjectiveResolutions 𝒱] [HasInjectiveResolutions 𝒴]
  [Rₐ.Additive] [R_h.Additive] [R_b.Additive] [R_c.Additive]
  [PreservesFiniteLimits R_h] [PreservesFiniteLimits R_b]
  [R_h.PreservesInjectiveObjects] [R_b.PreservesInjectiveObjects]

include adjₐ adj_c α in
/-- **Acyclicity transported around a commutative square.** If the right adjoints of a square of
adjunctions commute, `R_c ∘ R_b ≅ Rₐ ∘ R_h`, with `R_h` and `R_b` left exact and preserving
injective objects, and if for an object `x`

* the units of `h` at `Lₐ x` and of `b` at `L_c x` are isomorphisms,
* `M = L_b (L_c x)` is acyclic for `R_h` and for `R_b`, and
* `L_c x` is acyclic for `R_c`,

then `Lₐ x` is acyclic for `Rₐ`: `Rᵠ Rₐ (Lₐ x) = 0` for `q > 0`. -/
theorem isZero_rightDerived_of_comp_iso (x : 𝒳) [IsIso (adj_h.unit.app (Lₐ.obj x))]
    [IsIso (adj_b.unit.app (L_c.obj x))]
    (hh : ∀ q, 0 < q → IsZero ((R_h.rightDerived q).obj (L_b.obj (L_c.obj x))))
    (hb : ∀ q, 0 < q → IsZero ((R_b.rightDerived q).obj (L_b.obj (L_c.obj x))))
    (hc : ∀ q, 0 < q → IsZero ((R_c.rightDerived q).obj (L_c.obj x)))
    (q : ℕ) (hq : 0 < q) :
    IsZero ((Rₐ.rightDerived q).obj (Lₐ.obj x)) := by
  let M := L_b.obj (L_c.obj x)
  let eG : Lₐ.obj x ≅ R_h.obj M :=
    asIso (adj_h.unit.app (Lₐ.obj x)) ≪≫
      R_h.mapIso ((leftAdjointCompIsoOfCompIso adjₐ adj_h adj_b adj_c α).app x)
  have e₃ := Stacks.RightDerivedComp.objIso R_h (injectiveResolution M) hh Rₐ q
  have e₄ := (Functor.rightDerivedIsoOfNatIso α.symm q).app M
  have e₅ := Stacks.RightDerivedComp.objIso R_b (injectiveResolution M) hb R_c q
  have e₆ : R_b.obj M ≅ L_c.obj x := (asIso (adj_b.unit.app (L_c.obj x))).symm
  exact (hc q hq).of_iso
    ((Rₐ.rightDerived q).mapIso eG ≪≫ e₃.symm ≪≫ e₄ ≪≫ e₅ ≪≫ (R_c.rightDerived q).mapIso e₆)

end Abelian

end CategoryTheory.Adjunction
