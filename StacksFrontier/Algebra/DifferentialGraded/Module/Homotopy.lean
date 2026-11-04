module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# Homotopies between homomorphisms of differential graded modules

A homotopy between two homomorphisms `f, g : M ⟶ N` of right differential graded modules is a
map `h` of the underlying right `A`-modules which lowers degree by one and satisfies
`f - g = d_N ∘ h + h ∘ d_M`. Two homomorphisms are homotopic when such an `h` exists. This file
defines homotopies, shows that they are stable under pre- and postcomposition, and records the
bundled notion of a square of differential graded modules that commutes only up to a chosen
homotopy.

## Main definitions

* `DifferentialGradedModule.Homotopy`: a homotopy together with its defining properties.
* `DifferentialGradedModule.Homotopic`: the existence of a homotopy.
* `DifferentialGradedModule.HomotopyCommutativeSquare`: a square of differential graded modules
  with a chosen homotopy between its two composites.

## Main results

* `DifferentialGradedModule.Homotopy.ext`: homotopies with the same underlying map are equal.
* `DifferentialGradedModule.Homotopy.exists_comp`: composing a homotopy with homomorphisms on
  either side gives a homotopy between the composites, with the expected underlying map.

## Implementation notes

The right action of the differential graded algebra is encoded by a module structure over its
opposite algebra, so a homotopy is linear over that opposite algebra; it is not required to
commute with the differentials. The grading and homotopy equations are fields rather than
side conditions, so that the homotopy category and the cone constructions can use them
directly. `Homotopic` is an abbreviation, which lets those constructions use its existential
meaning without unfolding. `exists_comp` pins the underlying map of the resulting homotopy down
pointwise rather than merely asserting that some homotopy exists.

## References

* [Stacks Project, Tag 09JN](https://stacks.math.columbia.edu/tag/09JN)
* [Stacks Project, Tag 09JP](https://stacks.math.columbia.edu/tag/09JP)
* [Stacks Project, Section 22.7](https://stacks.math.columbia.edu/tag/09JV)
-/

@[expose] public section

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}
  {M N : DifferentialGradedModule.{u, v, w} A}

/-- An `A`-linear degree `-1` homotopy between homomorphisms of differential graded
`A`-modules. -/
@[stacks 09JN "homotopy between morphisms"]
structure Homotopy (f g : Hom M N) where
  /-- The underlying map of right `A`-modules. -/
  toLinearMap : M.M →ₗ[MulOpposite A.A] N.M
  /-- A homotopy lowers the grading by one. -/
  map_grading : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → toLinearMap x ∈ N.grading (n - 1)
  /-- The difference of the homomorphisms is the commutator with the differentials. -/
  homotopy_eq : ∀ x : M.M,
    f.toFun x - g.toFun x = N.d (toLinearMap x) + toLinearMap (M.d x)

/-- Homotopies agree if their underlying maps agree at every element. -/
@[ext]
theorem Homotopy.ext {f g : Hom M N} (h k : Homotopy f g)
    (heq : ∀ x, h.toLinearMap x = k.toLinearMap x) : h = k := by
  cases h; cases k; congr 1; exact LinearMap.ext heq

/-- Two homomorphisms of differential graded modules are homotopic if a homotopy between them
exists. -/
@[stacks 09JN "homotopic morphisms"]
abbrev Homotopic (f g : Hom M N) : Prop := Nonempty (Homotopy f g)

/-- Composing a homotopy with homomorphisms of differential graded modules on either side gives
a homotopy whose underlying map is the corresponding composite. -/
@[stacks 09JP]
theorem Homotopy.exists_comp {K L : DifferentialGradedModule.{u, v, w} A} (f g : Hom L M)
    (a : Hom K L) (c : Hom M N) (h : Homotopy f g) :
    ∃ k : Homotopy (c.comp (f.comp a)) (c.comp (g.comp a)),
      ∀ x : K.M, k.toLinearMap x = c.toFun (h.toLinearMap (a.toFun x)) :=
  ⟨{ toLinearMap :=
      { toFun := fun x => c.toFun (h.toLinearMap (a.toFun x))
        map_add' := by intros; simp only [map_add]
        map_smul' := by
          intro r x
          rw [show a.toFun (r • x) = r • a.toFun x from a.map_smul x (MulOpposite.unop r),
            map_smul,
            show c.toFun (r • h.toLinearMap (a.toFun x)) =
              r • c.toFun (h.toLinearMap (a.toFun x)) from
                c.map_smul _ (MulOpposite.unop r)]
          rfl }
     map_grading := by
       intro n x hx
       exact c.map_grading (n - 1) _ (h.map_grading n _ (a.map_grading n x hx))
     homotopy_eq := by
       intro x
       show c.toFun (f.toFun (a.toFun x)) - c.toFun (g.toFun (a.toFun x)) =
         N.d (c.toFun (h.toLinearMap (a.toFun x))) +
           c.toFun (h.toLinearMap (a.toFun (K.d x)))
       have hc := LinearMap.congr_fun c.map_d (h.toLinearMap (a.toFun x))
       have ha := LinearMap.congr_fun a.map_d x
       simp only [LinearMap.comp_apply] at hc ha
       rw [← map_sub, h.homotopy_eq, map_add, hc, ha] }, fun _ => rfl⟩

/-- A square of differential graded `A`-modules together with a chosen homotopy from the
composite `b ∘ f` along the top and right edges to the composite `g ∘ a` along the left and
bottom edges. -/
structure HomotopyCommutativeSquare (A : DifferentialGradedAlgebra.{u, v} R) where
  /-- The upper-left module. -/
  K : DifferentialGradedModule.{u, v, w} A
  /-- The upper-right module. -/
  L : DifferentialGradedModule.{u, v, w} A
  /-- The lower-left module. -/
  M : DifferentialGradedModule.{u, v, w} A
  /-- The lower-right module. -/
  N : DifferentialGradedModule.{u, v, w} A
  /-- The upper horizontal map. -/
  f : Hom K L
  /-- The left vertical map. -/
  a : Hom K M
  /-- The right vertical map. -/
  b : Hom L N
  /-- The lower horizontal map. -/
  g : Hom M N
  /-- The chosen homotopy, whose equation is `b f - g a = d h + h d`. -/
  h : Homotopy (b.comp f) (g.comp a)

end DifferentialGradedModule
