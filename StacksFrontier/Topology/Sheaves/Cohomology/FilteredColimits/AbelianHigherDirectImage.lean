module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.FilteredColimits
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology and higher direct images of abelian sheaves on a topological space

Let `X` and `Y` be topological spaces and `f : X ⟶ Y` a continuous map. This file names the two
right derived functors that Section 20.19 of the Stacks Project works with for *abelian*
sheaves — cohomology over an open subset, the right derived functor of the sections functor
`Γ(U, -)`, and the degree-`p` higher direct image `R^p f_*`, the right derived functor of the
pushforward of abelian sheaves — and proves Stacks 0H7A: if cohomology over the inverse images
of the opens of a basis of `Y` commutes with a colimit of abelian sheaves, then so does
`R^p f_*`.

## Main definitions

* `Stacks.Cohomology.AbelianSheaf.sectionsOver`: sections of an abelian sheaf over an open
  subset.
* `Stacks.Cohomology.AbelianSheaf.cohomologyOver`: its right derived functors, i.e.
  `H^p(U, -)`.
* `Stacks.Cohomology.AbelianSheaf.higherDirectImage`: the right derived functors of the
  pushforward, i.e. `R^p f_*`.

## Main results

* `Stacks.Cohomology.AbelianSheaf.preservesColimit_higherDirectImage_of_isBasis`
  (Stacks 0H7A): `R^p f_*` commutes with a colimit as soon as cohomology over the inverse
  images of a basis of `Y` does.

## Implementation notes

Both functors are additive — sections and pushforward of abelian sheaves are computed on the
underlying presheaves, where addition of morphisms is defined objectwise — and the additivity
instances are supplied locally inside each definition, since they are needed to form the right
derived functor and are not found by instance search through `TopCat.Sheaf.forget`.

The proof of 0H7A is one application of the local criterion Stacks 0H7B,
`Stacks.Cohomology.HigherDirectImage.preservesColimit_rightDerived_sheafPushforwardContinuous`,
to the continuous functor `Opens.map f`: a basis of `Y` supplies, for every open `V`, a
covering of `V` by members of the basis, which is the `PreZeroHypercover` that criterion asks
for. The source states its conclusion as an equality
`R^p f_* (colim F_i) = colim R^p f_* F_i`; it is rendered as
`CategoryTheory.Limits.PreservesColimit`, which says exactly that the canonical comparison is
invertible, so no colimit of an unrelated diagram has to exist.

The `have : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) Ab)` in that proof is not a
new hypothesis: `TopCat.Sheaf AddCommGrpCat X` *is* that category, but instance search does not
unfold `TopCat.Sheaf` to connect the two spellings.

For sheaves of *modules* on a ringed space the corresponding higher direct images are developed
in `StacksDraft.Ch20.Sec14` under the namespace `Stacks.Cohomology.HigherDirectImage`, and for
schemes in `StacksDraft.AlgebraicGeometry.F3.HigherDirectImage`; neither covers the
abelian-sheaf case named here.

## References

* [Stacks Project, Tag 0H7A](https://stacks.math.columbia.edu/tag/0H7A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace Stacks.Cohomology.AbelianSheaf

variable {X Y : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{v}]
variable [EnoughInjectives (X.Sheaf AddCommGrpCat.{v})]

/-- The sections functor for abelian sheaves over an open subset. -/
noncomputable abbrev sectionsOver (U : Opens X) :
    X.Sheaf AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v} :=
  TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{v}).obj (op U)

/-- Sheaf cohomology over `U`, the degree-`p` right derived functor of sections over `U`. -/
noncomputable def cohomologyOver (U : Opens X) (p : ℕ) :
    X.Sheaf AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v} := by
  letI : (sectionsOver U).Additive :=
    { map_add := by
        intros
        change ((TopCat.Sheaf.forget AddCommGrpCat.{v} X).map (_ + _)).app (op U) = _
        rw [Functor.map_add (TopCat.Sheaf.forget AddCommGrpCat.{v} X)]
        rfl }
  exact (sectionsOver U).rightDerived p

/-- The degree-`p` higher direct image functor of a continuous map. -/
noncomputable def higherDirectImage (f : X ⟶ Y) (p : ℕ) :
    X.Sheaf AddCommGrpCat.{v} ⥤ Y.Sheaf AddCommGrpCat.{v} := by
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).Additive :=
    { map_add := by intros; rfl }
  exact (TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).rightDerived p

/-- **Stacks 0H7A.** If cohomology over the inverse images of the opens of a basis of `Y`
commutes with a colimit of abelian sheaves on `X`, then so does the degree-`p` higher direct
image along `f`.

This is the local criterion of Stacks 0H7B for the morphism of sites given by the continuous
functor `Opens.map f`, together with the observation that a basis of `Y` supplies, for every
open `V`, a covering of `V` by members of the basis — which is what 0H7B asks for. -/
@[stacks 0H7A]
theorem preservesColimit_higherDirectImage_of_isBasis
    {I : Type v} [SmallCategory I] (f : X ⟶ Y)
    (F : I ⥤ X.Sheaf AddCommGrpCat.{v}) (p : ℕ)
    (h : Opens.IsBasis {V : Opens Y |
      PreservesColimit F (cohomologyOver ((Opens.map f).obj V) p)}) :
    PreservesColimit F (higherDirectImage f p) := by
  classical
  -- The two spellings `X.Sheaf AddCommGrpCat` and `Sheaf (Opens.grothendieckTopology X) Ab`
  -- are the same category, but instance search does not connect them.
  have : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) (Ab.{v})) := by
    change EnoughInjectives (X.Sheaf AddCommGrpCat.{v}); infer_instance
  apply Stacks.Cohomology.HigherDirectImage.preservesColimit_rightDerived_sheafPushforwardContinuous
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (u := Opens.map f) (p := p) (F := F)
  intro V
  obtain ⟨Us, hUs, hV⟩ := Opens.isBasis_iff_cover.mp h V
  let E : PreZeroHypercover V :=
    { I₀ := Us
      X i := i.1
      f i := homOfLE (by rw [hV]; exact le_sSup i.2) }
  refine ⟨E, ?_, fun i => hUs i.2⟩
  intro x hx
  rw [hV, sSup_eq_iSup' Us, Opens.mem_iSup] at hx
  obtain ⟨i, hxi⟩ := hx
  exact ⟨E.X i, E.f i, E.sieve₀_f i, hxi⟩

end Stacks.Cohomology.AbelianSheaf
