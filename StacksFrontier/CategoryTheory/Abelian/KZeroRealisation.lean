module

public import StacksCore.CategoryTheory.GrothendieckGroup.PeriodicComplex
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroup

/-!
# The realisation theorem for `K₀` of an abelian category

Two constructions of the Grothendieck group of an abelian category live in this repository:
`KZero`, the quotient of the free abelian group on the objects by the relations of the short
exact sequences, and `CategoryTheory.GrothendieckGroup`, the same quotient taken over the
inductively presented set of those relations. They are canonically isomorphic, and this file
builds the two homomorphisms between them in order to transport one statement: the *realisation
theorem*, the key step of [Stacks, Tag 02MX] part (2), which says that two objects have the same
class exactly when they are the two homology objects of a `(2, 1)`-periodic complex. That is the
form in which [Stacks, Tag 02SC] uses 02MX (2), and it is stated for
`CategoryTheory.GrothendieckGroup` as
`CategoryTheory.GrothendieckGroup.of_eq_of_iff_exists_homology_iso`.

## Main definitions

* `KZero.toGrothendieckGroup` and `KZero.ofGrothendieckGroup` — the two comparison
  homomorphisms, mutually inverse.

## Main results

* `KZero.mk_eq_mk_iff_of_eq_of` — two objects have the same class in `K₀` for one construction
  exactly when they do for the other.
* `KZero.mk_eq_mk_iff_exists_homology_iso` — the realisation theorem, [Stacks, Tag 02MX] part
  (2), for `KZero`.
* `KZero.exists_eq_mk_sub_mk` — every element of `K₀(𝒜)` is a difference of the classes of two
  objects.

## Implementation notes

Only the two homomorphisms are built, not the bundled `AddEquiv`: each direction is produced by
the universal property of its source, and the two round trips are checked on the classes of
objects. That is all three statements below need.

## References

* [Stacks Project, Tag 02MU](https://stacks.math.columbia.edu/tag/02MU)
* [Stacks Project, Tag 02MX](https://stacks.math.columbia.edu/tag/02MX)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace KZero

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The comparison homomorphism from `KZero 𝒜` to `CategoryTheory.GrothendieckGroup 𝒜`. -/
def toGrothendieckGroup : KZero 𝒜 →+ GrothendieckGroup 𝒜 :=
  lift (fun X => GrothendieckGroup.of X) fun _ hS => GrothendieckGroup.additivity hS

@[simp]
theorem toGrothendieckGroup_mk (X : 𝒜) :
    toGrothendieckGroup (mk 𝒜 X) = GrothendieckGroup.of X :=
  lift_mk _ _ X

/-- The comparison homomorphism from `CategoryTheory.GrothendieckGroup 𝒜` to `KZero 𝒜`. -/
def ofGrothendieckGroup : GrothendieckGroup 𝒜 →+ KZero 𝒜 :=
  GrothendieckGroup.lift (mk 𝒜) fun _ hS => mk_of_shortExact _ hS

@[simp]
theorem ofGrothendieckGroup_of (X : 𝒜) :
    ofGrothendieckGroup (GrothendieckGroup.of X) = mk 𝒜 X :=
  rfl

/-- The two comparison homomorphisms compose to the identity of `KZero 𝒜`. -/
theorem ofGrothendieckGroup_toGrothendieckGroup (x : KZero 𝒜) :
    ofGrothendieckGroup (toGrothendieckGroup x) = x :=
  DFunLike.congr_fun
    (hom_ext (F := (ofGrothendieckGroup (𝒜 := 𝒜)).comp toGrothendieckGroup)
      (F' := AddMonoidHom.id (KZero 𝒜)) fun X => by simp) x

/-- Two objects have the same class in `KZero 𝒜` exactly when they have the same class in
`CategoryTheory.GrothendieckGroup 𝒜`. -/
theorem mk_eq_mk_iff_of_eq_of {X Y : 𝒜} :
    mk 𝒜 X = mk 𝒜 Y ↔ GrothendieckGroup.of X = GrothendieckGroup.of Y := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using congrArg toGrothendieckGroup h
  · simpa using congrArg ofGrothendieckGroup h

/-- **[Stacks, Tag 02MX] part (2), the realisation theorem, for `KZero`.** Two objects `X` and `Y`
of an abelian category have the same class in `K₀` if and only if there is a `(2, 1)`-periodic
complex `M --φ--> M --ψ--> M` whose homology objects `H⁰ = Ker ψ / Im φ` and `H¹ = Ker φ / Im ψ`
are isomorphic to `X` and to `Y`. [Stacks, Tag 02SC] uses 02MX (2) in this form. -/
@[stacks 02MX "(2), key step, for `KZero`: `[X] = [Y]` iff `X ≅ H⁰`, `Y ≅ H¹` for some `(M, φ, ψ)`"]
theorem mk_eq_mk_iff_exists_homology_iso {X Y : 𝒜} :
    mk 𝒜 X = mk 𝒜 Y ↔ ∃ (M : 𝒜) (φ ψ : M ⟶ M) (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0),
      Nonempty ((ShortComplex.mk φ ψ hφψ).homology ≅ X) ∧
        Nonempty ((ShortComplex.mk ψ φ hψφ).homology ≅ Y) :=
  mk_eq_mk_iff_of_eq_of.trans GrothendieckGroup.of_eq_of_iff_exists_homology_iso

/-- Every element of `K₀(𝒜)` is a difference `[X] - [Y]` of the classes of two objects. -/
theorem exists_eq_mk_sub_mk (x : KZero 𝒜) : ∃ X Y : 𝒜, x = mk 𝒜 X - mk 𝒜 Y := by
  obtain ⟨X, Y, hXY⟩ := GrothendieckGroup.exists_eq_of_sub_of (toGrothendieckGroup x)
  refine ⟨X, Y, ?_⟩
  have := congrArg ofGrothendieckGroup hXY
  rwa [ofGrothendieckGroup_toGrothendieckGroup, map_sub, ofGrothendieckGroup_of,
    ofGrothendieckGroup_of] at this

end KZero

end
