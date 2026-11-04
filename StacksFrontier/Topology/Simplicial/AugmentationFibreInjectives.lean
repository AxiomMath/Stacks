module

public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactnessFlat
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianUnivLE
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Cohomology
public import StacksFrontier.Topology.Simplicial.AugmentationFibre

/-!
# Restriction to the fibre preserves injective abelian sheaves

Let `X` be a simplicial topological space, let `a : X ⟶ Y` be an augmentation and let `V` be an
open of `Y`.  Restriction of abelian sheaves along the comparison of total sites
`(X ×_Y V)_Zar ⥤ X_Zar` has a left adjoint `j_!`, the lower shriek of [Stacks, Tag 04BF]; that
left adjoint is exact, and therefore restriction carries injective abelian sheaves on `X_Zar`
to injective abelian sheaves on `(X ×_Y V)_Zar`.

This is **part (1) of the proof of [Stacks, Tag 0D84]**.

## Main definitions

* `Stacks.Topology.Simplicial.fibreRestrictionAb`: restriction of abelian sheaves from `X_Zar`
  to `(X ×_Y V)_Zar`.
* `Stacks.Topology.Simplicial.fibreLowerShriekAb`: its left adjoint, extension by zero.

## Main results

* `Stacks.Topology.Simplicial.enoughInjectives_sheaf_simplicialOpen_ab`: abelian sheaves on the
  total site of a simplicial space have enough injectives.
* `Stacks.Topology.Simplicial.isCofilteredOrEmpty_structuredArrow_fibreImage`: every comma
  category of the comparison of total sites is cofiltered or empty.
* `Stacks.Topology.Simplicial.fibreLowerShriekAb_adjunction`: the adjunction `j_! ⊣ -|`.
* `Stacks.Topology.Simplicial.fibreLowerShriekAb_preservesFiniteLimits`: `j_!` is left exact.
* `Stacks.Topology.Simplicial.fibreRestrictionAb_preservesInjectiveObjects` and
  `Stacks.Topology.Simplicial.injective_fibreRestrictionAb_obj`: **restriction to the fibre
  preserves injective abelian sheaves**.

## Implementation notes

The Stacks Project constructs the exact left adjoint by hand, as extension by zero.  Here it is
Mathlib's lower shriek — the sheafification of the left Kan extension along the comparison —
and its exactness comes from the pointwise description of that Kan extension: the comma
category over an object `(n, U)` of `X_Zar` has an initial object when `U ⊆ a_n⁻¹(V)`, because
the comparison is fully faithful and `(n, U)` is then in its image, and is empty otherwise,
because an arrow out of `(n, U)` into the fibre forces `U ⊆ a_n⁻¹(V)`.  A category with an
initial object is cofiltered, and the empty category is vacuously cofiltered-or-empty, so the
colimits computing the Kan extension are pseudofiltered and hence exact in abelian groups.
That is `Stacks.Sites.LowerShriek.preservesInjectiveObjects_sheafPushforward_of_cofilteredOrEmpty`.

The functor is *not* representably flat — the comma categories over objects outside the fibre
are empty, not cofiltered — so
`Stacks.Sites.LowerShriek.preservesInjectiveObjects_sheafPushforward_of_representablyFlat` does
not apply.

## References

* [Stacks Project, Tag 0D84](https://stacks.math.columbia.edu/tag/0D84)
* [Stacks Project, Tag 01DU](https://stacks.math.columbia.edu/tag/01DU)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 04BF](https://stacks.math.columbia.edu/tag/04BF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial

variable (X : SimplicialObject TopCat.{u}) (Y : TopCat.{u})
  (a : X ⟶ (SimplicialObject.const TopCat).obj Y) (V : Opens Y)

/-- A category with an initial object is cofiltered: the initial object is a cone over any pair
of objects, and composing with the unique arrow out of it equalizes any parallel pair. -/
private theorem isCofilteredOrEmpty_of_isInitial {J : Type*} [Category J] {i : J}
    (hi : IsInitial i) : IsCofilteredOrEmpty J where
  cone_objs A B := ⟨i, hi.to A, hi.to B, trivial⟩
  cone_maps A _ _ _ := ⟨i, hi.to A, hi.hom_ext _ _⟩

/-- **Every comma category of the comparison of total sites is cofiltered or empty.** Over an
object `(n, U)` of `X_Zar` with `U ⊆ a_n⁻¹(V)` the comma category has an initial object, the
identity of `(n, U)` read through the comparison; over any other object it is empty. -/
instance isCofilteredOrEmpty_structuredArrow_fibreImage (U : SimplicialOpen X) :
    IsCofilteredOrEmpty (StructuredArrow U (fibreImage X Y a V)) := by
  by_cases hU : U.toOpens ≤ fibreOpens X Y a V U.degree
  · exact fibreImage_obj_eq_of_le X Y a V hU ▸
      isCofilteredOrEmpty_of_isInitial
        (StructuredArrow.mkIdInitial (T := fibreImage X Y a V)
          (Y := ⟨U.degree, Fibre.preimageOpens X Y a V U.toOpens⟩))
  · exact
      { cone_objs := fun A _ => absurd (le_fibreOpens_of_hom X Y a V A.hom) hU
        cone_maps := fun A _ _ _ => absurd (le_fibreOpens_of_hom X Y a V A.hom) hU }

/-- Sheaves of abelian groups on the total site of a simplicial space admit sheafification. -/
instance hasSheafify_simplicialOpen_ab (Z : SimplicialObject TopCat.{u}) :
    HasSheafify (SimplicialOpen.grothendieckTopology Z) Ab.{u} :=
  Stacks.CategoryTheory.Hypercovering.hasSheafify_addCommGrpCat.{u} _

/-- **Abelian sheaves on the total site of a simplicial space have enough injectives**
([Stacks, Tag 01DU]): the site `Z_Zar` is small, its objects being the opens of the spaces `Z_n`,
so its abelian sheaves form a Grothendieck abelian category. -/
instance enoughInjectives_sheaf_simplicialOpen_ab (Z : SimplicialObject TopCat.{u}) :
    EnoughInjectives (Sheaf (SimplicialOpen.grothendieckTopology Z) Ab.{u}) :=
  CategoryTheory.Sheaf.enoughInjectives_of_small.{u, u} _ _

/-- **Restriction of abelian sheaves from `X_Zar` to `(X ×_Y V)_Zar`**: the direct image along
the comparison of total sites, which on sections is `W ↦ F(W)` for an open `W` of a space
`a_n⁻¹(V)`, read as an open of `X_n`. -/
noncomputable def fibreRestrictionAb :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u} ⥤
      Sheaf (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V)) Ab.{u} :=
  (fibreImage X Y a V).sheafPushforwardContinuous Ab.{u}
    (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V))
    (SimplicialOpen.grothendieckTopology X)

/-- **Extension by zero**, the left adjoint `j_!` of restriction to the fibre. -/
noncomputable def fibreLowerShriekAb :
    Sheaf (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V)) Ab.{u} ⥤
      Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u} :=
  (fibreImage X Y a V).sheafPullback Ab.{u}
    (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V))
    (SimplicialOpen.grothendieckTopology X)

/-- **Stacks 0D84, part (1) of the proof.** Extension by zero is left adjoint to restriction to
the fibre. -/
noncomputable def fibreLowerShriekAb_adjunction :
    fibreLowerShriekAb X Y a V ⊣ fibreRestrictionAb X Y a V :=
  (fibreImage X Y a V).sheafAdjunctionContinuous Ab.{u} _ _

/-- **Stacks 0D84, part (1) of the proof.** Extension by zero is left exact. -/
theorem fibreLowerShriekAb_preservesFiniteLimits :
    PreservesFiniteLimits (fibreLowerShriekAb X Y a V) :=
  Stacks.Sites.LowerShriek.preservesFiniteLimits_sheafPullback_of_cofilteredOrEmpty.{u}
    (fibreImage X Y a V) _ _

/-- **Stacks 0D84, part (1) of the proof.** The restriction of an abelian sheaf on `X_Zar` to
`(X ×_Y V)_Zar` preserves injective objects: its left adjoint, extension by zero, is exact, and
a right adjoint of a functor preserving monomorphisms preserves injectives
([Stacks, Tag 015Z]). -/
@[stacks 0D84 "part (1) of the proof: restriction to the fibre preserves injectives"]
theorem fibreRestrictionAb_preservesInjectiveObjects :
    (fibreRestrictionAb X Y a V).PreservesInjectiveObjects :=
  Stacks.Sites.LowerShriek.preservesInjectiveObjects_sheafPushforward_of_cofilteredOrEmpty.{u}
    (fibreImage X Y a V) _ _

/-- **Stacks 0D84, part (1) of the proof.** The restriction to `(X ×_Y V)_Zar` of an injective
abelian sheaf on `X_Zar` is an injective abelian sheaf. -/
@[stacks 0D84 "part (1) of the proof: the restriction of an injective is injective"]
theorem injective_fibreRestrictionAb_obj
    (I : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) [Injective I] :
    Injective ((fibreRestrictionAb X Y a V).obj I) :=
  (fibreRestrictionAb_preservesInjectiveObjects X Y a V).injective_obj
    (inferInstanceAs (Injective I))

end Stacks.Topology.Simplicial

end
