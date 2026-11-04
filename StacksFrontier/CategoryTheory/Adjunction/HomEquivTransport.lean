module

public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Transporting a hom-set bijection along a comparison of two left adjoints

Let `a : La ⊣ Ra` and `d : Ld ⊣ Rd` be two adjunctions, and let `Lb` and `Lc` be two further
left adjoints, `b : Lb ⊣ Rb` and `c : Lc ⊣ Rc`, arranged in a square

```
      La
   A ----→ B
Lc |        | Lb
   v        v
   E ----→ F
      Ld
```

An isomorphism `ν : La ⋙ Lb ≅ Lc ⋙ Ld` of the two composites round the square carries a
morphism `f : La X ⟶ Y` to a morphism `Ld (Lc X) ⟶ Lb Y`, namely `ν.inv.app X ≫ Lb.map f`.
This file records what happens to the two **adjoint transposes**: the transpose of the
transported morphism along `d` is the transport along `Lc` of the transpose of `f` along `a`,
followed by one comparison morphism `Lc (Ra Y) ⟶ Rd (Lb Y)` that does not depend on `f`.

That comparison is forced: it is the mate, under `b` and `c`, of the conjugate of `ν`.  So
nothing is chosen here beyond `ν` itself, and the statement below is the assertion that the two
hom-set bijections of a square of adjunctions correspond under the square's own comparisons.

## Main definitions

* `Stacks.CategoryTheory.transportMate`: the comparison `Ra ⋙ Lc ⟶ Lb ⋙ Rd` attached to `ν` —
  the mate of the conjugate of `ν`.

## Main results

* `Stacks.CategoryTheory.homEquiv_transport`: **the two hom-set bijections correspond.**
* `Stacks.CategoryTheory.homEquiv_symm_transport`: the same read through the inverse
  bijections.
* `Stacks.CategoryTheory.unit_transport`: **the two units correspond.**  This is
  `Stacks.CategoryTheory.homEquiv_transport` at the identity.
* `Stacks.CategoryTheory.transportMate_app`: the comparison on components.
* `Stacks.CategoryTheory.isIso_transportMate`: **the comparison is invertible when the two
  vertical adjunctions are adjoint equivalences.**  This is what lets a comparison of the two
  composite left adjoints round such a square be turned into a comparison of the two composite
  right adjoints, and so the square be read in the other direction.

## Implementation notes

The content is `Stacks.CategoryTheory.homEquiv_mate`, the element-level mates correspondence,
which is stated for an arbitrary 2-cell `t : Rb ⋙ Ra ⟶ Rd ⋙ Rc` between the two composite
right adjoints and the 2-cell `(conjugateEquiv (a.comp b) (c.comp d)).symm t` between the two
composite left adjoints that corresponds to it.  Here the 2-cell between the left adjoints is
the datum, so `t` is produced from it by `CategoryTheory.conjugateEquiv` and the conjugation
cancels: no identification of two separately built comparisons is needed.

`ν` is data, not a hypothesis.
-/

@[expose] public section

open CategoryTheory TwoSquare

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.CategoryTheory

variable {A : Type u₁} {B : Type u₂} {E : Type u₃} {F : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} E] [Category.{v₄} F]
variable {La : A ⥤ B} {Ra : B ⥤ A} {Lb : B ⥤ F} {Rb : F ⥤ B}
  {Lc : A ⥤ E} {Rc : E ⥤ A} {Ld : E ⥤ F} {Rd : F ⥤ E}
variable (a : La ⊣ Ra) (b : Lb ⊣ Rb) (c : Lc ⊣ Rc) (d : Ld ⊣ Rd)

/-- **The comparison of right adjoints attached to a comparison of the two composite left
adjoints round a square.**  For `ν : La ⋙ Lb ≅ Lc ⋙ Ld`, this is the mate under `b` and `c` of
the conjugate of `ν`, a morphism of functors `Ra ⋙ Lc ⟶ Lb ⋙ Rd` whose component at `Y` is a
map `Lc (Ra Y) ⟶ Rd (Lb Y)`.

It is determined by `ν`, so appending it is not a choice: it is the unique correction under
which the two hom-set bijections of the square correspond, which is
`Stacks.CategoryTheory.homEquiv_transport`. -/
noncomputable def transportMate (ν : La ⋙ Lb ≅ Lc ⋙ Ld) : Ra ⋙ Lc ⟶ Lb ⋙ Rd :=
  ((mateEquiv b c).symm (TwoSquare.mk Rb Rd Ra Rc
    (conjugateEquiv (a.comp b) (c.comp d) ν.inv))).natTrans

/-- **The two hom-set bijections of a square of adjunctions correspond.**  Let
`ν : La ⋙ Lb ≅ Lc ⋙ Ld` compare the two composites round the square.  For a morphism
`f : La X ⟶ Y`, the transpose along `d` of the transported morphism
`ν.inv.app X ≫ Lb.map f : Ld (Lc X) ⟶ Lb Y` is the image under `Lc` of the transpose of `f`
along `a`, followed by the comparison `Stacks.CategoryTheory.transportMate`.

This is `Stacks.CategoryTheory.homEquiv_mate` with the 2-cell between the right adjoints taken
to be the conjugate of `ν`, so that the conjugation in that statement cancels. -/
theorem homEquiv_transport (ν : La ⋙ Lb ≅ Lc ⋙ Ld) {X : A} {Y : B} (f : La.obj X ⟶ Y) :
    d.homEquiv (Lc.obj X) (Lb.obj Y) (ν.inv.app X ≫ Lb.map f) =
      Lc.map (a.homEquiv X Y f) ≫ (transportMate a b c d ν).app Y := by
  have h := homEquiv_mate a b c d (conjugateEquiv (a.comp b) (c.comp d) ν.inv) f
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- **The same correspondence read through the inverse bijections.**  For `v : X ⟶ Ra Y`, the
transpose along `d` of `Lc.map v` followed by the comparison is the transport along `ν` of the
transpose of `v` along `a`. -/
theorem homEquiv_symm_transport (ν : La ⋙ Lb ≅ Lc ⋙ Ld) {X : A} {Y : B} (v : X ⟶ Ra.obj Y) :
    (d.homEquiv (Lc.obj X) (Lb.obj Y)).symm
        (Lc.map v ≫ (transportMate a b c d ν).app Y) =
      ν.inv.app X ≫ Lb.map ((a.homEquiv X Y).symm v) := by
  refine ((d.homEquiv (Lc.obj X) (Lb.obj Y)).symm_apply_eq).2
    (Eq.trans (congrArg (fun w ↦ Lc.map w ≫ (transportMate a b c d ν).app Y)
      ((a.homEquiv X Y).apply_symm_apply v).symm) ?_)
  exact (homEquiv_transport a b c d ν ((a.homEquiv X Y).symm v)).symm

/-- **The two units of a square of adjunctions correspond.**  Let `ν : La ⋙ Lb ≅ Lc ⋙ Ld`
compare the two composites round the square.  Then the unit of `d` at `Lc X`, followed by `Rd`
of the comparison, is the image under `Lc` of the unit of `a` at `X`, followed by
`Stacks.CategoryTheory.transportMate`.

This is `Stacks.CategoryTheory.homEquiv_transport` at `f = 𝟙 (La.obj X)`, since the unit is the
transpose of the identity (`CategoryTheory.Adjunction.homEquiv_id`). -/
theorem unit_transport (ν : La ⋙ Lb ≅ Lc ⋙ Ld) (X : A) :
    d.unit.app (Lc.obj X) ≫ Rd.map (ν.inv.app X) =
      Lc.map (a.unit.app X) ≫ (transportMate a b c d ν).app (La.obj X) := by
  have h := homEquiv_transport a b c d ν (𝟙 (La.obj X))
  rw [a.homEquiv_id] at h
  dsimp only [Functor.comp_obj] at h
  simpa only [Functor.map_id, Category.comp_id, Adjunction.homEquiv_unit] using h

/-- **The comparison, on components.**  Unfolding `CategoryTheory.mateEquiv`, the component of
`Stacks.CategoryTheory.transportMate` at `Y` is the unit of `b`, the conjugate of `ν`, and the
counit of `c`, in that order. -/
theorem transportMate_app (ν : La ⋙ Lb ≅ Lc ⋙ Ld) (Y : B) :
    (transportMate a b c d ν).app Y =
      Lc.map (Ra.map (b.unit.app Y)) ≫
        Lc.map ((conjugateEquiv (a.comp b) (c.comp d) ν.inv).app (Lb.obj Y)) ≫
          c.counit.app (Rd.obj (Lb.obj Y)) := by
  simp [transportMate, mateEquiv]

/-- **The comparison is invertible when the two vertical adjunctions come from equivalences.**
By `Stacks.CategoryTheory.transportMate_app` its components are the unit of `b`, the conjugate
of `ν` and the counit of `c`; the middle one is invertible because `ν` is
(`CategoryTheory.conjugateEquiv_iso`), and the outer two are invertible exactly when the two
vertical adjunctions are adjoint equivalences, which is what `hb` and `hc` say.

The two invertibilities are explicit arguments, not instance arguments: for a named adjunction
`b` the goal `IsIso b.unit` is not always found by instance resolution.

So in a square whose two vertical functors are equivalences a comparison of the two composite
left adjoints is matched by a comparison of the two composite right adjoints that is itself an
isomorphism. -/
theorem isIso_transportMate (ν : La ⋙ Lb ≅ Lc ⋙ Ld) (hb : IsIso b.unit)
    (hc : IsIso c.counit) : IsIso (transportMate a b c d ν) := by
  have := hb
  have := hc
  have : ∀ Y : B, IsIso ((transportMate a b c d ν).app Y) := fun Y ↦ by
    rw [transportMate_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Stacks.CategoryTheory

end
