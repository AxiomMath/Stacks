module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Stalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical

/-!
# Representable sheaves on the small étale site

The small étale topology of a scheme `S` is subcanonical, so the étale `S`-schemes embed
fully faithfully into the small étale topos of `S` as the representable sheaves, and the
stalk at a geometric point `s` of the sheaf represented by `X` is the set of lifts of `s`
to `X`, the germ at a pointed étale neighbourhood `(U, p)` of `t : U ⟶ X` corresponding to
the lift `p ≫ t`.

These are the two ingredients of the proof of [Stacks, Tag 03QT] that pass from étale
schemes to sheaves.  Over a field `K` that theorem says that taking stalks at a geometric
point is an equivalence from the small étale topos of `Spec K` onto the continuous sets over
the absolute Galois group; its proof constructs the inverse by representing a Galois set by
an étale `K`-scheme ([Stacks, Tag 03QR]) and taking the sheaf of morphisms into it.  What is
not proved here, and is what the source leaves out, is that every sheaf on `Spec(K)_ét` is
representable; no declaration carries the tag 03QT.

## References

* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
-/
