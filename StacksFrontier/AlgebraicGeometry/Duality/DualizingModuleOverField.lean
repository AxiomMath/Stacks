module

public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingTransitivity
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# The dualizing module of a scheme of finite type over a field

Let `X` be an equidimensional scheme of finite type over a field `k`. The convention of
[Stacks, Tag 0AWJ] is to take for `ω_X^•` the dualizing complex normalized relative to `k[0]`
and to call

`ω_X = H^{-dim(X)}(ω_X^•)`

the *dualizing module* of `X`. This file carries that definition, together with the
identification `ω_X^• = f^! 𝒪_{Spec(k)}` which the example records for `X` separated over `k`,
`f : X ⟶ Spec(k)` being the structure morphism.

Normalization relative to a complex on the base is `Stacks.Duality.Normalized`, the pair
`(K, α_i)` of [Stacks, Tag 0AU5]; `k[0]` is
`Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec k)`, the structure sheaf placed in
degree zero. The upper shriek is the parameter `Stacks.Duality.UpperShriek`, as everywhere in
this chapter: `f^!` is built in [Stacks, Tag 0A9Y] out of the right adjoint of `Rf_*` and Nagata
compactification, which this repository does not carry, so the formalism is bundled and taken as
input.

## Main definitions

* `Stacks.Duality.normalizedDualizingModule` — `ω_X = H^{-dim(X)}(ω_X^•)`, the dualizing module
  of a complex normalized relative to a chosen complex on the base.
* `Stacks.Duality.upperShriekLocalIso` — the comparison `(p^!ω_S^•)|_U ≅ (U → S)^!ω_S^•` on an
  open subscheme separated over the base.
* `Stacks.Duality.SeparatedCovering.top` — the covering of `X` by `X` itself, available when `X`
  is separated and of finite type over the base.

## Main results

* `Stacks.Duality.normalizedUpperShriek` — for `X` separated and of finite type over a
  Noetherian base `S` with structure morphism `p`, the complex `p^!ω_S^•` is normalized relative
  to `ω_S^•`. This is the separated case of [Stacks, Tag 0AUE].
* `Stacks.Duality.normalizedUpperShriekOverField` — the same over a field, where it is the
  identification `ω_X^• = f^!𝒪_{Spec(k)}` of [Stacks, Tag 0AWJ].
* `Stacks.Duality.restrictLocalIso_upperShriekLocalIso` — the comparisons
  `Stacks.Duality.upperShriekLocalIso` restrict to one another, which is what makes `p^!ω_S^•`
  normalized. It is one application of the coherence of [Stacks, Tag 0ATY].

## Implementation notes

Equidimensionality, `TopologicalSpace.Equidimensional`, is the standing hypothesis of
[Stacks, Tag 0AWJ] and enters neither of its two assertions: the convention places the dualizing
module in degree `-dim(X)` whatever `X` is, and the separated identification is a statement
about `f^!`. What equidimensionality buys is that `ω_X` is the *first* nonvanishing cohomology
sheaf of `ω_X^•`, which is asserted by [Stacks, Tag 0AWI] and not here.

`ENat.toNat ((topologicalKrullDim X).getD 0)` is `dim(X)` as a natural number; it is the
spelling `Stacks.Duality.relativeDualizingModule` uses for the same degree, and it is `0` on the
empty scheme, all of whose cohomology sheaves vanish.

*Which clause of [Stacks, Tag 0AUE] is carried here.* That lemma asserts six numbered parts and
then closes with a remark about the separated case. Parts (2) and (4) are
`Stacks.Duality.fNewShriekStructureObjIsoDualizing` and
`Stacks.Duality.fNewShriekObjIsoDualizing` of
`StacksFrontier/AlgebraicGeometry/Duality/NewShriekNormalizedComplex.lean`, and both are about
`f_new^! = D_X ∘ Lf^* ∘ D_Y`, the formula of part (5) taken as a definition in
`StacksFrontier/AlgebraicGeometry/Duality/GlueingDualizingComplexes.lean`. The closing remark is
about the genuine `f^!` of [Stacks, Tag 0A9Y] instead, and it is the half of it reading
`ω_X^• = (X → S)^! ω_S^•` that `Stacks.Duality.normalizedUpperShriek` carries; the other half of
the remark, `f_new^! K ≅ f^! K`, is not proved here, and neither is any of parts (1), (3), (5)
and (6).

The third sentence of the example, that the proper case is a special case of
[Stacks, Tag 0AWI], is a cross-reference and gets no declaration of its own. Nothing below
depends on that tag: `Stacks.Duality.relativeDualizingModule`, which carries its definitional
clause and that clause only, already is `H^{-dim(X)}` of the twisted inverse image of the base
complex.

## References

* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0AU5](https://stacks.math.columbia.edu/tag/0AU5)
* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AWJ](https://stacks.math.columbia.edu/tag/0AWJ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v' w

namespace Stacks.Duality

/-! ### The dualizing module -/

section Module

variable {A : UpperShriek fun X : Scheme.{u} => DerivedCategory X.Modules}
  {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS : DerivedCategory S.Modules} {ι : Type w} {𝒰 : SeparatedCovering p ι}

/-- **The dualizing module `ω_X = H^{-dim(X)}(ω_X^•)`** of [Stacks, Tag 0AWJ]: the cohomology
sheaf in degree minus the dimension of `X` of a complex normalized relative to a chosen complex
on the base. Over a field, with `ω_S^• = k[0]`, this is the customary dualizing module of an
equidimensional scheme of finite type over `k`. -/
@[stacks 0AWJ "the definition: omega_X = H^{-dim X}(omega_X^bullet) for the complex \
normalized relative to k[0]"]
def normalizedDualizingModule (𝒩 : Normalized A hp ωS 𝒰) : X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules
    (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ))).obj 𝒩.complex

end Module

/-! ### The separated case: `ω_X^• = p^! ω_S^•` -/

section Separated

variable {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)]
  (A : UpperShriek 𝒟) {X S : Scheme.{u}} {p : X ⟶ S}
  (hp : IsFiniteTypeOverNoetherian p) (hps : IsShriekable p) (ωS : 𝒟 S)

/-- The canonical comparison `(p^!ω_S^•)|_U ≅ (U → S)^!ω_S^•` on an open subscheme separated and
of finite type over the base: the comparison of [Stacks, Tag 0ATX] for the factorization
`U → X → S`. -/
def upperShriekLocalIso {U : X.Opens} (hU : IsShriekable (U.ι ≫ p)) :
    A.restrictTo hp U ((A.shriek p hps).obj ωS) ≅ A.localModel hU ωS :=
  ((A.factorIso rfl (hp.isShriekable_ι U) hps hU).app ωS).symm

/-- The comparisons of `Stacks.Duality.upperShriekLocalIso` restrict to one another: on a
smaller open `W ≤ U` the restriction of the comparison at `U` is the comparison at `W`. This is
one application of the coherence of [Stacks, Tag 0ATY]. -/
theorem restrictLocalIso_upperShriekLocalIso {W U : X.Opens} (hle : W ≤ U)
    (hU : IsShriekable (U.ι ≫ p)) :
    A.restrictLocalIso hp ωS ((A.shriek p hps).obj ωS) hle hU
        (upperShriekLocalIso A hp hps ωS hU) =
      upperShriekLocalIso A hp hps ωS (hp.isShriekable_le hle hU) := by
  have key := A.factorIso_assoc (X.homOfLE_ι hle) (rfl : U.ι ≫ p = U.ι ≫ p)
    (rfl : W.ι ≫ p = W.ι ≫ p)
    (show X.homOfLE hle ≫ U.ι ≫ p = W.ι ≫ p by rw [← Category.assoc, X.homOfLE_ι])
    (hp.isShriekable_homOfLE hle) (hp.isShriekable_ι U) hps (hp.isShriekable_ι W) hU
    (hp.isShriekable_le hle hU) ωS
  refine Iso.ext ((Iso.inv_eq_inv _ _).mp ?_)
  simp only [UpperShriek.restrictLocalIso, upperShriekLocalIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← Category.assoc, key, Category.assoc, Iso.hom_inv_id_app]
  simp

/-- **[Stacks, Tag 0AUE], the closing remark on the separated case.** Let `X` be separated and
of finite type over a Noetherian scheme `S` with structure morphism `p`, and let `ω_S^•` be a
complex on `S`. Then `p^!ω_S^•` is normalized relative to `ω_S^•`: its restriction to each
member of a covering of `X` by opens separated over `S` is canonically the local model there,
compatibly on overlaps. -/
@[stacks 0AUE "the closing remark, first half only: for X separated over the base the complex \
p^! omega_S^bullet is normalized relative to omega_S^bullet. The second half of the remark, \
f_new^! K = f^! K, is NOT carried, and neither are parts (1), (3), (5), (6); parts (2) and (4) \
are elsewhere. RESTRICTED: the upper-shriek formalism of Stacks 0A9Y/0ATX/0ATY is the parameter \
UpperShriek, pending its landing"]
def normalizedUpperShriek {ι : Type w} (𝒰 : SeparatedCovering p ι) : Normalized A hp ωS 𝒰 where
  complex := (A.shriek p hps).obj ωS
  localIso i := upperShriekLocalIso A hp hps ωS (𝒰.shriekable i)
  compat i j := by
    rw [restrictLocalIso_upperShriekLocalIso, restrictLocalIso_upperShriekLocalIso]

/-- The complex of `Stacks.Duality.normalizedUpperShriek` is `p^!ω_S^•`. -/
@[simp]
theorem normalizedUpperShriek_complex {ι : Type w} (𝒰 : SeparatedCovering p ι) :
    (normalizedUpperShriek A hp hps ωS 𝒰).complex = (A.shriek p hps).obj ωS :=
  rfl

/-- The covering of `X` by `X` itself, available exactly when `X` is separated and of finite
type over the base. It is the covering for which [Stacks, Tag 0AU5] reads `ω_X^• = p^!ω_S^•`. -/
def SeparatedCovering.top : SeparatedCovering p Unit where
  U _ := ⊤
  finite := inferInstance
  covers := by simp
  shriekable _ := (hp.isShriekable_ι ⊤).comp hps

end Separated

/-! ### The base `Spec(k)` -/

section Field

variable (k : Type u) [Field k]

/-- The spectrum of a field is a Noetherian scheme. -/
theorem isNoetherian_spec_of_field : AlgebraicGeometry.IsNoetherian (Spec (.of k)) :=
  AlgebraicGeometry.isNoetherian_Spec.mpr inferInstance

variable {k} {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- A scheme of finite type over a field is of finite type over a Noetherian base. -/
theorem isFiniteTypeOverNoetherian_of_field [LocallyOfFiniteType p] [QuasiCompact p] :
    IsFiniteTypeOverNoetherian p where
  base_noetherian := isNoetherian_spec_of_field k
  locallyOfFiniteType := inferInstance
  quasiCompact := inferInstance

/-- The structure morphism of a scheme separated and of finite type over a field admits an upper
shriek functor. -/
theorem isShriekable_of_field [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] :
    IsShriekable p where
  target_noetherian := isNoetherian_spec_of_field k
  separatedFiniteType := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

variable (A : UpperShriek fun X : Scheme.{u} => DerivedCategory X.Modules)
  [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]

/-- **[Stacks, Tag 0AWJ]** For `X` separated and of finite type over a field `k` with structure
morphism `f : X ⟶ Spec(k)`, the complex `f^!𝒪_{Spec(k)}` is normalized relative to `k[0]`: this
is the identification `ω_X^• = f^!𝒪_{Spec(k)}` the example records, by [Stacks, Tag 0AUE]. -/
@[stacks 0AWJ "the second assertion: for X separated over k the normalized complex is \
f^! O_{Spec k}. RESTRICTED: the upper-shriek formalism of Stacks 0A9Y/0ATX/0ATY is the \
parameter UpperShriek, pending its landing"]
def normalizedUpperShriekOverField {ι : Type w} (𝒰 : SeparatedCovering p ι) :
    Normalized A (isFiniteTypeOverNoetherian_of_field p)
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k))).obj 𝒰 :=
  normalizedUpperShriek A (isFiniteTypeOverNoetherian_of_field p) (isShriekable_of_field p)
    (DerivedPushforward.derivedStructureSheaf (Spec (.of k))).obj 𝒰

/-- The dualizing module of `X` separated and of finite type over `k` is the cohomology sheaf of
`f^!𝒪_{Spec(k)}` in degree minus the dimension of `X`. -/
theorem normalizedDualizingModule_normalizedUpperShriekOverField {ι : Type w}
    (𝒰 : SeparatedCovering p ι) :
    normalizedDualizingModule (normalizedUpperShriekOverField p A 𝒰) =
      (DerivedCategory.homologyFunctor X.Modules
          (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ))).obj
        ((A.shriek p (isShriekable_of_field p)).obj
          (DerivedPushforward.derivedStructureSheaf (Spec (.of k))).obj) :=
  rfl

end Field

end Stacks.Duality

end
