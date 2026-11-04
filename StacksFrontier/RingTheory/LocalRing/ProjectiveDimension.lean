module

import StacksFrontier.Algebra.Homology.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.Projective

public import StacksFrontier.RingTheory.Module.Kaplansky
public import StacksFrontier.Algebra.Homology.ProjectiveDimension.FiniteResolution
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe v u

/-!
# Free resolutions and projective dimension over a local ring

Let `R` be a commutative local ring, let `M` be an `R`-module and let `d : ℕ`. This file proves
that `M` has projective dimension at most `d` if and only if `M` admits a resolution

`0 → P_d → P_{d-1} → ⋯ → P₀ → M → 0`

by *free* modules, that is, a left resolution of `M` by free modules (Stacks 00LQ) whose terms
vanish in degrees `> d`.

Only locality separates this from the resolution by projectives of Stacks 0CXC, and over a local
ring it separates nothing: the class of projective objects of `ModuleCat R` *is* the class of free
modules, a free module being projective over any ring and a projective module over a local ring
being free by Kaplansky's theorem (Stacks 0593). The two conditions are therefore not two
conditions, and Stacks 0CXC already states this one.

## Main results

* `Stacks.LocalRing.ProjectiveIsFree.solution`: Stacks 0CXD, the equivalence of condition `(5)` of
  the source with item 1 of Stacks 0CXC.

## Implementation notes

The equality of the two classes of modules is
`Stacks.LocalRing.ProjectiveIsFree.isProjective_eq_free`. Stating it as an equality of object
properties, rather than as an equivalence for each module, is what makes the resolutions of Stacks
0CXC *be* the resolutions by frees instead of being transported into them: no complex, no
augmentation and no quasi-isomorphism is rebuilt, in either direction.

## References

* [StacksProject 0CXD](https://stacks.math.columbia.edu/tag/0CXD)
* [StacksProject 0CXC](https://stacks.math.columbia.edu/tag/0CXC)
* [StacksProject 0593](https://stacks.math.columbia.edu/tag/0593)
* [StacksProject 00LQ](https://stacks.math.columbia.edu/tag/00LQ)
-/

namespace Stacks.LocalRing.ProjectiveIsFree



open CategoryTheory Limits

/-- Over a commutative local ring `R`, the projective objects of `ModuleCat R` are exactly the
free modules: an equality of classes of objects, by `Module.Projective.of_free` one way and by
Kaplansky's theorem `Module.free_of_projective_of_isLocalRing` (Stacks 0593) the other. -/
@[sga "3 VIA 2.1.3" "more general"]
private lemma isProjective_eq_free (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R] :
    isProjective (ModuleCat.{v} R) = fun N : ModuleCat.{v} R => Module.Free R N := by
  ext N
  constructor
  · intro _
    exact Module.free_of_projective_of_isLocalRing
  · intro _
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R N)

@[expose] public section

/-- **Stacks 0CXD.** Let `R` be a commutative local ring, let `M` be an `R`-module and let `d : ℕ`.
Then `M` has projective dimension at most `d` — equivalently, by Stacks 0CXC, `M` admits a
resolution of length `d` by projectives — if and only if `M` admits a resolution
`0 → P_d → ⋯ → P₀ → M → 0` by free modules. -/
@[ega "0 17.2.1" "partial"]
public theorem solution {R : Type u}
    [CommRing R] [IsLocalRing R] [Small.{v} R] (M : ModuleCat.{v} R) (d : ℕ) :
    HasProjectiveDimensionLE M d ↔
      ∃ F : ObjectProperty.LeftResolution (fun N : ModuleCat.{v} R => Module.Free R N) M,
        ∀ i, d < i → IsZero (F.complex.X i) := by
  rw [← isProjective_eq_free R]
  exact (hasProjectiveDimensionLE_tfae_leftResolution M d).out 1 2

end

end Stacks.LocalRing.ProjectiveIsFree

/-!
# Free resolutions and projective dimension over a local ring

Let `R` be a local ring, let `M` be an `R`-module and let `d : ℕ`. The four equivalent conditions
of Lemma 0CXC — that `M` has projective dimension at most `d`, that `M` admits a resolution
`0 → P_d → ⋯ → P₀ → M → 0` by projectives, and the two conditions on the `d`-th syzygy of a
resolution by projectives — are, over a local ring, also equivalent to

`(5)` there is a resolution `0 → P_d → P_{d-1} → ⋯ → P₀ → M → 0` with all `Pᵢ` free.

Only locality separates `(5)` from item 2 of Lemma 0CXC: a free module is projective, so `(5)`
implies item 2 over any ring, and over a local ring every projective module is free by Kaplansky's
theorem (Stacks 0593, `Module.free_of_projective_of_isLocalRing`), so a resolution by projectives
of length `d` already is one by frees.

## Main results

* `ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_free`: over a commutative local
  ring, a module has projective dimension at most `d` if and only if it admits a resolution of
  length `d` by free modules.

## Implementation notes

The source adds `(5)` to a list of four conditions already known to be equivalent, so what is
stated here is the equivalence of `(5)` with the first of them,
`CategoryTheory.HasProjectiveDimensionLE M d`. Together with
`CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution` (Stacks 0CXC) this is the source's
five-fold equivalence; restating the other three items would only duplicate that lemma's `TFAE`.

A resolution by free modules is the resolution of Stacks 00LQ for the class of free objects: a
`CategoryTheory.ObjectProperty.LeftResolution (fun N => Module.Free R N) M`, that is, an
`ℕ`-indexed chain complex `F.complex` of free modules together with a quasi-isomorphism
`F.π` to `M` placed in degree `0`, which is exactness of `⋯ → P₁ → P₀ → M → 0`. This is the shape
in which Stacks 0CXC and 00O7 state resolutions. That the resolution has
*length `d`* is the vanishing of its terms in degrees `> d`; exactness in degree `d` then makes
`P_d → P_{d-1}` a monomorphism, which is the source's leading `0 →`, and `P_d` is allowed to be
zero, so `≤ d` is the source's assertion and not a weakening of it.

Freeness is `Module.Free R N` for the module underlying the object `N : ModuleCat.{v} R`, over the
same ring `R`; there is no named object property for it in Mathlib. A free object of
`ModuleCat R` is projective, by `ModuleCat.projective_of_free (Module.Free.chooseBasis R N)`.

Modules are objects of `ModuleCat.{v} R` for `R : Type u` and `Small.{v} R`, which is where
Mathlib puts the smallness needed for `ModuleCat.enoughProjectives`, hence for free covers to
exist in that universe. The source's situation is `v = u`, where `Small.{u} R` is automatic.
Commutativity of `R` is the source's, and is what Kaplansky's theorem is available for here
(Stacks 0593 discusses weakening it).

Faithfulness. (1) No hypothesis is dead. Locality is used already at `d = 0`: over the non-local
ring `ZMod 6` the ideal `(2) = {0, 2, 4}` is a direct summand, `ZMod 6 = (2) ⊕ (3)`, hence a
projective module of projective dimension `0`; but a resolution `0 → P₀ → (2) → 0` by frees would
exhibit `(2)` as a free `ZMod 6`-module, and a free `ZMod 6`-module has either one element or at
least six, while `(2)` has three. Smallness is what makes free modules available in the category
at all, so without it the forward implication has nothing to build a resolution from; and `d` and
`M` are used by both sides. (2) The scalars and the base are the source's: `M` is a module over the
local ring `R` itself, the resolving modules are free over that same `R`, the differentials are
`R`-linear and the `Ext` groups behind `HasProjectiveDimensionLE` are computed in `ModuleCat R`; no
localisation or change of rings occurs. (3) The map the source names is pinned: a `LeftResolution`
carries its augmentation `P₀ → M` as the field `F.π`, and exactness of `⋯ → P₁ → P₀ → M → 0` is a
condition on that map, so the complex resolves `M` along a given morphism rather than being merely
exact. (4) The instantiation is not degenerate: for `M` free and `d = 0` both sides hold, the
resolution being `M` itself in degree `0` and zero above it; whereas over the local ring
`k[x]/(x²)` the module `k = R/(x)` satisfies neither side for any `d`, having no finite resolution
by projectives (Stacks 0A5Q). So neither direction is vacuous.

## References

* [StacksProject 0CXD](https://stacks.math.columbia.edu/tag/0CXD)
* [StacksProject 0CXC](https://stacks.math.columbia.edu/tag/0CXC)
* [StacksProject 0593](https://stacks.math.columbia.edu/tag/0593)
* [StacksProject 00LQ](https://stacks.math.columbia.edu/tag/00LQ)
-/

@[expose] public section



open CategoryTheory Limits in
/-- **Stacks 0CXD.** Let `R` be a commutative local ring, let `M` be an `R`-module and let
`d : ℕ`. Then `M` has projective dimension at most `d` — equivalently, by Stacks 0CXC, `M` has a
resolution of length `d` by projectives — if and only if `M` has a resolution
`0 → P_d → ⋯ → P₀ → M → 0` by *free* modules, that is, a left resolution `F` of `M` by free
modules with `F.complex.X i = 0` for `i > d`. -/
@[stacks 0CXD "Condition (5) is added to Lemma 0CXC by stating its equivalence with item 1 of
that lemma's `TFAE`. A resolution `0 → P_d → ⋯ → P₀ → M → 0` by frees is an
`ObjectProperty.LeftResolution` for the class of free modules (00LQ), the notion 0CXC and 00O7
use, vanishing in degrees `> d`; see the module docstring."]
public theorem ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_free {R : Type u}
    [CommRing R] [IsLocalRing R] [Small.{v} R] (M : ModuleCat.{v} R) (d : ℕ) :
    HasProjectiveDimensionLE M d ↔
      ∃ F : ObjectProperty.LeftResolution (fun N : ModuleCat.{v} R => Module.Free R N) M,
        ∀ i, d < i → IsZero (F.complex.X i) :=
          by apply Stacks.LocalRing.ProjectiveIsFree.solution

end

/-!
# Finite free resolutions and projective dimension over a local Noetherian ring

Let `R` be a local Noetherian ring, let `M` be a finite `R`-module and let `d : ℕ`. This file
proves that `M` has projective dimension at most `d` if and only if `M` admits a resolution

`0 → F_d → F_{d - 1} → ⋯ → F₀ → M → 0`

by *finite free* modules, that is, a left resolution of `M` (Stacks 00LQ) by modules that are free
and finite over `R` and whose terms vanish in degrees `> d`.

Both adjectives are free of charge. Over a Noetherian ring a finite module has projective
dimension at most `d` exactly when it admits a resolution of length `d` by *finite projective*
modules (Stacks 0CXE), and over a local ring a projective module is free by Kaplansky's theorem
(Stacks 0593), a free module being projective over any ring. So the finite projective modules are
the finite free ones, the resolutions of Stacks 0CXE are the resolutions asked for here, and the
two conditions are not two conditions.

## Main results

* `Stacks.LocalRing.FiniteFreeResolution.solution`: Stacks 0CXF, the equivalence of condition `(7)`
  of the source with item 1 of Stacks 0CXC.

## Implementation notes

Over a local ring projectivity and freeness cut out the same objects of `ModuleCat R`, hence so do
projectivity and freeness conjoined with any further property: that is
`Stacks.LocalRing.FiniteFreeResolution.projective_and_eq_free_and`, an equality of classes of
objects. Stating it as an equality, rather than as an equivalence for each module, is what makes
the resolutions by finite projectives of Stacks 0CXE *be* the resolutions by finite frees: the
class they resolve by is rewritten, and no complex, no augmentation and no quasi-isomorphism is
rebuilt, in either direction. Both implications of the source therefore come from the single
equivalence of Stacks 0CXE, and the further property is left arbitrary because finiteness plays no
part in the equality.

The passage from projective to free is the unrestricted Kaplansky theorem
`Module.free_of_projective_of_isLocalRing` (Stacks 0593), which the source's Lemma 00NX invokes for
a finite module; no finiteness is needed for it, so `Module.Finite R N` is carried along untouched
rather than used. Consequently the resolution of the source's condition `(6)` by finite projectives
*is* its resolution `(7)` by finite frees, and Stacks 0CXD, the source's `(5)`, is not needed.

## References

* [StacksProject 0CXF](https://stacks.math.columbia.edu/tag/0CXF)
* [StacksProject 0CXC](https://stacks.math.columbia.edu/tag/0CXC)
* [StacksProject 0CXD](https://stacks.math.columbia.edu/tag/0CXD)
* [StacksProject 0CXE](https://stacks.math.columbia.edu/tag/0CXE)
* [StacksProject 0593](https://stacks.math.columbia.edu/tag/0593)
* [StacksProject 00LQ](https://stacks.math.columbia.edu/tag/00LQ)
-/

namespace Stacks.LocalRing.FiniteFreeResolution



open CategoryTheory Limits

/-- Over a commutative local ring `R`, the projective objects of `ModuleCat R` are exactly the free
modules — `Module.Projective.of_free` one way and Kaplansky's theorem
`Module.free_of_projective_of_isLocalRing` (Stacks 0593) the other — so for any class of objects
`P`, the projective objects satisfying `P` are exactly the free ones satisfying `P`. -/
@[ega "0 17.2.2" "more general", sga "3 VIA 2.1.3" "more general"]
private lemma projective_and_eq_free_and (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R]
    (P : ObjectProperty (ModuleCat.{v} R)) :
    (fun N : ModuleCat.{v} R => Projective N ∧ P N)
      = fun N : ModuleCat.{v} R => Module.Free R N ∧ P N := by
  ext N
  rw [← congr_fun (Stacks.LocalRing.ProjectiveIsFree.isProjective_eq_free R) N]

@[expose] public section

/-- **Stacks 0CXF.** Let `R` be a local Noetherian ring, let `M` be a finite `R`-module and let
`d : ℕ`. Then `M` has projective dimension at most `d` — equivalently, by Stacks 0CXC, 0CXD and
0CXE, `M` admits a resolution of length `d` by projectives, by frees, or by finite projectives —
if and only if `M` admits a resolution `0 → F_d → ⋯ → F₀ → M → 0` by finite free modules. -/
@[ega "0 17.2.1" "partial", ega "0 17.2.2"]
public theorem solution {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] (M : ModuleCat.{v} R) [Module.Finite R M] (d : ℕ) :
    HasProjectiveDimensionLE M d ↔
      ∃ F : ObjectProperty.LeftResolution
          (fun N : ModuleCat.{v} R => Module.Free R N ∧ Module.Finite R N) M,
        ∀ i, d < i → IsZero (F.complex.X i) := by
  rw [← projective_and_eq_free_and R _]
  exact ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite M d

end

end Stacks.LocalRing.FiniteFreeResolution

/-!
# Finite free resolutions and projective dimension over a local Noetherian ring

Let `R` be a local Noetherian ring, let `M` be a finite `R`-module and let `d : ℕ`. The four
equivalent conditions of Lemma 0CXC — that `M` has projective dimension at most `d`, that `M`
admits a resolution `0 → P_d → ⋯ → P₀ → M → 0` by projectives, and the two conditions on the
`d`-th syzygy of a resolution by projectives — together with condition `(5)` of Lemma 0CXD
(a resolution of length `d` by free modules) and condition `(6)` of Lemma 0CXE (a resolution of
length `d` by finite projective modules), are, for a finite module over a local Noetherian ring,
also equivalent to

`(7)` there is a resolution `0 → F_d → F_{d-1} → ⋯ → F₀ → M → 0` with all `Fᵢ` finite free.

Both extra adjectives come for free over such a ring: Noetherianness makes the syzygies of `M`
finite, so `M` has a resolution of length `d` by *finite projective* modules (Lemma 0CXE), and a
finite projective module over a local ring is finite free (Lemma 00NX, in Mathlib Kaplansky's
theorem `Module.free_of_projective_of_isLocalRing` of Stacks 0593). Conversely a finite free
module is projective, so `(7)` implies item 2 of Lemma 0CXC over any ring.

## Main results

* `ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_free_finite`: over a local
  Noetherian ring, a finite module has projective dimension at most `d` if and only if it admits
  a resolution of length `d` by finite free modules.

## Implementation notes

The source adds `(7)` to a list of six conditions already known to be equivalent, so what is
stated here is the equivalence of `(7)` with the first of them,
`CategoryTheory.HasProjectiveDimensionLE M d`. Together with
`CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution` (Stacks 0CXC),
`ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_free` (Stacks 0CXD) and
`ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite` (Stacks 0CXE)
this is the source's seven-fold equivalence; restating the other six items would only duplicate
those lemmas.

A resolution by finite free modules is the resolution of Stacks 00LQ for the class of objects of
`ModuleCat R` that are free and finite over `R`: a
`CategoryTheory.ObjectProperty.LeftResolution (fun N => Module.Free R N ∧ Module.Finite R N) M`,
that is, an `ℕ`-indexed chain complex `F.complex` of finite free modules together with a
quasi-isomorphism `F.π` to `M` placed in degree `0`, which is exactness of `⋯ → F₁ → F₀ → M → 0`.
This is the shape and the very object property in which Stacks 00O7 states
resolutions by finite free modules, with `Module.Free R N` alone in Stacks 0CXD and
`Projective N ∧ Module.Finite R N` in Stacks 0CXE. That the resolution has *length `d`* is the
vanishing of its terms in degrees `> d`; exactness in degree `d` then makes `F_d → F_{d-1}` a
monomorphism, which is the source's leading `0 →`, and `F_d` is allowed to be zero, so `≤ d` is
the source's assertion and not a weakening of it.

Modules are objects of `ModuleCat.{v} R` for `R : Type u` and `Small.{v} R`, which is where
Mathlib puts the smallness needed for `ModuleCat.enoughProjectives`, hence for finite free covers
to exist in that universe; the source's situation is `v = u`, where `Small.{u} R` is automatic.

Commutativity is the source's hypothesis and is kept, although the sibling Stacks 0CXE is stated
for an arbitrary (left Noetherian) ring: what is special here is the passage from finite
projective to finite free, and the form of that passage available here — Kaplansky's theorem
`Module.free_of_projective_of_isLocalRing`, and `Module.free_of_flat_of_isLocalRing` for the
finite case — is commutative. `IsLocalRing R` is Mathlib's spelling of the source's "local ring".

Faithfulness. (1) No hypothesis is dead: `Module.Finite R M` is needed for the forward
implication already at `d = 0`, an infinite-dimensional vector space over a field being projective
yet admitting no resolution of length `0` by finite modules; `IsNoetherianRing R` is what makes
the syzygies of `M` finite in that implication, the right-hand side forcing
`Module.FinitePresentation R M` since the kernel of `F₀ → M` is the image of the finite `F₁`;
`IsLocalRing R` is what turns the finite projectives of Stacks 0CXE into finite frees, and is
already needed at `d = 0`, where over `ZMod 6` the projective module `(2)` has three elements
while a free `ZMod 6`-module has one or at least six; `Small.{v} R` is what makes finite free
modules available in the category at all; and `d` and `M` are used by both sides. (2) The scalars
and the base are the source's: `M` is a module over the local Noetherian ring `R` itself, the
resolving modules are free and finite over that same `R`, the differentials are `R`-linear and
the `Ext` groups behind `HasProjectiveDimensionLE` are computed in `ModuleCat R`; no localisation
or change of rings occurs. (3) The map the source names is pinned: a `LeftResolution` carries its
augmentation `F₀ → M` as the field `F.π`, and exactness of `⋯ → F₁ → F₀ → M → 0` is a condition
on that map, so the complex resolves `M` along a given morphism rather than being merely exact.
(4) The instantiation is not degenerate: for `R` a discrete valuation ring with uniformiser `p`,
`M = R ⧸ (p)` and `d = 1` both sides hold, the resolution being `0 → R → R → M → 0` with the
first map multiplication by `p`, which is injective as `R` is a domain; whereas over the local
Noetherian ring `k[x]/(x²)` the finite module `k = R/(x)` satisfies neither side for any `d`,
having no finite resolution by projectives (Stacks 0A5Q). So neither direction is vacuous.

## References

* [StacksProject 0CXF](https://stacks.math.columbia.edu/tag/0CXF)
* [StacksProject 0CXC](https://stacks.math.columbia.edu/tag/0CXC)
* [StacksProject 0CXD](https://stacks.math.columbia.edu/tag/0CXD)
* [StacksProject 0CXE](https://stacks.math.columbia.edu/tag/0CXE)
* [StacksProject 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [StacksProject 00LQ](https://stacks.math.columbia.edu/tag/00LQ)
-/

@[expose] public section



open CategoryTheory Limits in
/-- **Stacks 0CXF.** Let `R` be a local Noetherian ring, let `M` be a finite `R`-module and let
`d : ℕ`. Then `M` has projective dimension at most `d` — equivalently, by Stacks 0CXC, 0CXD and
0CXE, `M` has a resolution of length `d` by projectives, by frees, or by finite projectives — if
and only if `M` has a resolution `0 → F_d → ⋯ → F₀ → M → 0` by *finite free* modules, that is, a
left resolution `F` of `M` by free modules that are finite over `R`, with `F.complex.X i = 0` for
`i > d`. -/
@[stacks 0CXF "Condition (7) is added to Lemmas 0CXC, 0CXD and 0CXE by stating its equivalence
with item 1 of 0CXC's `TFAE`. A resolution `0 → F_d → ⋯ → F₀ → M → 0` by finite frees is an
`ObjectProperty.LeftResolution` for the class of finite free modules (00LQ), the notion 00O7 uses,
vanishing in degrees `> d`; see the module docstring.", ega "0 17.2.2"]
public theorem ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_free_finite
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] (d : ℕ) :
    HasProjectiveDimensionLE M d ↔
      ∃ F : ObjectProperty.LeftResolution
          (fun N : ModuleCat.{v} R => Module.Free R N ∧ Module.Finite R N) M,
        ∀ i, d < i → IsZero (F.complex.X i) :=
          by apply Stacks.LocalRing.FiniteFreeResolution.solution

end
