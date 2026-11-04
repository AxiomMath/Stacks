module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Constant sheaves on a site

On a site, the constant sheaf with a given value is the sheafification of the corresponding
constant presheaf. In particular, this construction applied to `ZMod n` gives the constant sheaf
with that value.

## Main definitions

* `CategoryTheory.constantSheaf` is the constant-sheaf functor on a site.
* `Stacks.Sites.constantSheafZMod` is that functor at the value `ZMod n`, which is the sheaf
  written `\(\underline{\mathbf Z/n\mathbf Z}\)` in the source.

## Implementation notes

Mathlib defines `CategoryTheory.constantSheaf J D` as the constant-presheaf functor followed by
sheafification, and we adopt this existing definition in its natural generality for an arbitrary
target category admitting sheafification. Applying it to the abelian group `ZMod n` gives the
constant sheaf denoted `\(\underline{\mathbf Z/n\mathbf Z}\)` in the source.

The group `ZMod n` lives in `Type 0`, while the value category of the sheaf is a category of
abelian groups in whichever universe the site's cohomology is computed in, so the value is
lifted with `ULift`. Lifting does not change the group: `ULift.ringEquiv` is an isomorphism onto
`ZMod n`.

## References

* [Stacks Project, Tag 03P4](https://stacks.math.columbia.edu/tag/03P4)
-/

@[expose] public section

add_to_stacks 03P4 "constant_sheaf" CategoryTheory.constantSheaf
add_to_sga "4 IV 11.1.5" CategoryTheory.constantSheaf
add_to_sga "4 IV 2.7.5" CategoryTheory.constantSheaf
add_to_sga "4 IV 4.3.4" CategoryTheory.constantSheaf
add_to_sga "4 IX 2.0" CategoryTheory.constantSheaf
add_to_sga "4 VII 2.1" "partial" CategoryTheory.constantSheaf
add_to_sga "4½ Arcata 2.2.1" CategoryTheory.constantSheaf
add_to_sga "4½ Arcata 4.3.2" CategoryTheory.constantSheaf
add_to_ega "0 15.2.1" "partial" CategoryTheory.constantSheaf
add_to_ega "0 3.6.1" CategoryTheory.constantSheaf

open CategoryTheory

universe w v u

namespace Stacks.Sites

/-- **Stacks 03P4, part (3).** The constant sheaf `ℤ/nℤ` on a site: the sheafification of the
constant presheaf `U ↦ ℤ/nℤ`, formed in abelian groups. -/
@[stacks 03P4 "part (3), the constant sheaf ℤ/nℤ"]
noncomputable abbrev constantSheafZMod {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{w}] (n : ℕ) :
    Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w, 0} (ZMod n)))

end Stacks.Sites

end
