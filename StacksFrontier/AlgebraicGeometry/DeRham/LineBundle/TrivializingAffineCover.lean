module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Laurent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An affine trivializing cover of a line bundle

Let `L` be an invertible module on a scheme `X`. Being locally trivial, `L` becomes isomorphic
to the structure sheaf over each member of some open cover of `X`; the members of that cover are
arbitrary opens. This file refines such a cover to one by *affine* opens, which is the shape a
computation on the relative spectrum of a graded algebra built from `L` needs: the affine opens
of a scheme form a basis of its topology, and a trivialization restricts along an inclusion of
opens.

## Main definitions

* `Stacks.SheafOfModules.isoUnitOverOfHom`: **a trivialization of a sheaf of modules over an
  object of a site restricts along any morphism into that object.**

## Main results

* `Stacks.LineBundle.Situation.exists_trivializing_affineOpen`: **every point of the scheme has
  an affine open neighbourhood over which the line bundle is isomorphic to the structure
  sheaf.**
* `Stacks.LineBundle.Situation.exists_affine_trivializing_cover`: **the affine opens over which
  the line bundle is isomorphic to the structure sheaf cover the scheme.**

## Implementation notes

The restriction of a trivialization is the composite of three canonical isomorphisms:
`SheafOfModules.overFunctorMap`, which says that restricting to the slice over the target and
then extending along the morphism is restricting to the slice over the source; the image of the
given trivialization under that extension; and `SheafOfModules.overMapUnitIso`, which says the
extension carries the structure sheaf of the target slice to that of the source slice. All three
are supplied by Mathlib, so no sectionwise computation appears.

The cover is indexed by the affine opens carrying a trivialization, as a subtype of
`AlgebraicGeometry.Scheme.affineOpens`, rather than by an abstract index type; the existential
form is then immediate and the index type stays in the universe of the scheme.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u v₁ u₁

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  (M : _root_.SheafOfModules.{u} R)

/-- **A trivialization of a sheaf of modules over an object of a site restricts along any
morphism into that object.** Restricting to the slice over the source is restricting to the
slice over the target followed by extension along the morphism, and that extension carries the
structure sheaf to the structure sheaf. -/
def isoUnitOverOfHom {W V : C} (f : W ⟶ V)
    (e : M.over V ≅ _root_.SheafOfModules.unit (R.over V)) :
    M.over W ≅ _root_.SheafOfModules.unit (R.over W) :=
  ((_root_.SheafOfModules.overFunctorMap R f).app M).symm ≪≫
    (_root_.SheafOfModules.overMap.{u} R f).mapIso e ≪≫
      _root_.SheafOfModules.overMapUnitIso f

end Stacks.SheafOfModules

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **Every point of the scheme on which the line bundle lives has an affine open neighbourhood
over which the line bundle is isomorphic to the structure sheaf.** The line bundle is locally
trivial, and the affine opens form a basis of the topology, so an affine open neighbourhood of
the point can be chosen inside a member of a trivializing cover. -/
@[ega "IV 21.13.16" "partial"]
theorem Situation.exists_trivializing_affineOpen (x : D.X) :
    ∃ U : D.X.affineOpens, x ∈ U.1 ∧
      Nonempty (D.L.over U.1 ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U.1)) := by
  obtain ⟨I, V, hV, e⟩ :=
    Stacks.SheafOfModules.Invertible.IsLocallyTrivial.exists_trivializing_cover (M := D.L)
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff (↥D.X) V).mp hV).exists_mem x
  obtain ⟨W, hW, hxW, hWV⟩ :=
    Opens.isBasis_iff_nbhd.mp D.X.isBasis_affineOpens (show x ∈ V i from hxi)
  exact ⟨⟨W, hW⟩, hxW, ⟨Stacks.SheafOfModules.isoUnitOverOfHom D.L (homOfLE hWV) (e i).some⟩⟩

/-- **The affine opens over which the line bundle is isomorphic to the structure sheaf cover the
scheme on which it lives.** This is the trivializing cover of Tag 01CS, refined so that every
member is affine. -/
theorem Situation.exists_affine_trivializing_cover :
    ∃ (I : Type u) (U : I → D.X.affineOpens), (⨆ i, (U i).1) = ⊤ ∧
      ∀ i, Nonempty (D.L.over (U i).1 ≅
        SheafOfModules.unit (D.X.ringCatSheaf.over (U i).1)) := by
  refine ⟨{ U : D.X.affineOpens //
      Nonempty (D.L.over U.1 ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U.1)) },
    Subtype.val, eq_top_iff.mpr fun x _ => ?_, fun U => U.2⟩
  obtain ⟨U, hxU, hU⟩ := D.exists_trivializing_affineOpen x
  exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩

end Stacks.LineBundle

end
