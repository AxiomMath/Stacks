module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.UniversalProperty
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The symmetric algebra of a module sheaf on a scheme

`PresheafOfModules.symmetricAlgebraSheafify` builds the symmetric algebra of a presheaf of
modules over a site, as a sheaf of graded algebras, and
`PresheafOfModules.isSymmetricAlgebra_symmetricAlgebraSheafify` proves its universal property.
This file instantiates both for a module sheaf `F` on a scheme `X`, over the scheme's own sheaf
of rings `X.ringCatSheaf`: the result is `Sym(F)` in the shape
`Stacks.ProjectiveBundle.Situation` and `Stacks.RelativeProj.Situation` take as data.

The instantiation is at the *identity* ring map: `X.ringCatSheaf.obj` is already a sheaf, so it
is its own sheafification, and the sheafification functor on modules is then inverted on `F`
itself by the counit of `PresheafOfModules.sheafificationAdjunction`, which is an isomorphism.
That counit is why the degree-one generator can be taken out of `F` rather than out of its
sheafification, and `SheafOfModules.GradedAlgebra.isSymmetricAlgebra_of_iso_source` is what
carries the universal property across it.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra`: **`Sym(F)` for a module sheaf `F` on a
  scheme `X`**, as a `SheafOfModules.GradedAlgebra X.ringCatSheaf`.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGen`: its degree-one generator `F ⟶ Sym¹ F`.
* `SheafOfModules.GradedAlgebra.isSymmetricAlgebra_of_iso_source`: the universal property of the
  symmetric algebra transported along an isomorphism of the generating module sheaf.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra`: **the universal
  property**, `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra (symmetricAlgebra X F)
  (symmetricAlgebraGen X F)`.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra_mul_comm`: homogeneous multiplication is
  commutative, in every pair of degrees.
* `AlgebraicGeometry.Scheme.Modules.isZero_symmetricAlgebra_piece`: the negative-degree pieces
  are zero.

Together these are five of the seven fields of `Stacks.ProjectiveBundle.Situation` — `algebra`,
`gen`, `isSymmetricAlgebra`, `mul_comm` and `negative_isZero`. The two that remain are
`isQuasicoherent` (Stacks 01CK) and `bijective_smul_one`; see the implementation notes.

## Implementation notes

**Why the instance arguments are passed positionally.** Every call below writes the four
instance arguments of `PresheafOfModules.symmetricAlgebraSheafify` out explicitly, the two on the
ring map by name (`isLocallyInjective_id_ringCatSheaf`, `isLocallySurjective_id_ringCatSheaf`)
and the two on the site of opens, `WEqualsLocallyBijective` and `HasWeakSheafify` for
`AddCommGrpCat.{u}`, as `inferInstance` in their slots, and pins the four universe parameters.
Left to instance search they are *not* found: `symmetricAlgebraSheafify` takes the
sheaf of rings as `{R : Sheaf J RingCat.{w}}` and the ring map as
`α : (O ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj`, so supplying `α := 𝟙 X.ringCatSheaf.obj` asks
the elaborator to solve `?R.obj ≟ X.ringCatSheaf.obj` — a projection it cannot invert — and
`Presheaf.IsLocallyInjective J α` is then synthesized against a goal still carrying `?R`. The
reported error names the fully instantiated goal, so it looks like a missing instance when it is
an ordering problem: `inferInstance` discharges that very goal when stated on its own. This is
the same device as the one recorded for `Category (SheafOfModules R)` at a concrete site — name
the instance instead of letting search find it.

**What `bijective_smul_one` still needs.** `Stacks.ProjectiveBundle.Situation.bijective_smul_one`
asks that `r ↦ r • 1` be a bijection onto the degree-zero local sections, and
`Stacks.ProjectiveBundle.Situation.bijective_smul_one_of_isoUnit` produces it from an isomorphism
`(symmetricAlgebra X F).piece 0 ≅ SheafOfModules.unit X.ringCatSheaf`. The presheaf-level half of
that isomorphism is `PresheafOfModules.symPowIntZeroIso`; what is missing is
`(PresheafOfModules.sheafification α).obj (PresheafOfModules.unit R₀) ≅ SheafOfModules.unit R`,
which is absent from the library.

**Universes.** A scheme fixes every universe to `u`, so the independent module universe of the
site-level development is specialized here, and the universe arguments are written out for the
reason given above.

**No `@[stacks]` tag.** Tag 01CG is the symmetric-power sheafification statement and is not
proved here; the material below is the instantiation of Section 17.21's symmetric algebra to a
scheme.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite PresheafOfModules TopologicalSpace

universe u

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M N : SheafOfModules.{u} R} {A : GradedAlgebra.{u, u} R}

/-- **The universal property of the symmetric algebra, transported along an isomorphism of the
generating module sheaf.** If `A` with `ι : M ⟶ A.piece 1` is the symmetric algebra of `M` and
`e : M ≅ N`, then `A` with `e.inv ≫ ι` is the symmetric algebra of `N`.

Both halves are formal: the commutation condition on a generator is a condition on its values at
local sections, so it passes through a precomposition in either direction, and the extension of a
generator `κ : N ⟶ B.piece 1` is the extension of `e.hom ≫ κ`. In particular no surjectivity of
`e` on sections is used. -/
theorem isSymmetricAlgebra_of_iso_source (e : M ≅ N) {ι : M ⟶ A.piece 1}
    (h : IsSymmetricAlgebra A ι) : IsSymmetricAlgebra A (e.inv ≫ ι) := by
  refine ⟨fun U s u => h.1 U (e.inv.val.app U s) (e.inv.val.app U u), fun B κ hκ => ?_⟩
  obtain ⟨g, hg, hgu⟩ := h.2 B (e.hom ≫ κ)
    fun U s u => hκ U (e.hom.val.app U s) (e.hom.val.app U u)
  refine ⟨g, ?_, fun h' hh' => hgu h' ?_⟩
  · show (e.inv ≫ ι) ≫ g.app 1 = κ
    rw [Category.assoc, hg, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  · have hh'' : (e.inv ≫ ι) ≫ h'.app 1 = κ := hh'
    show ι ≫ h'.app 1 = e.hom ≫ κ
    rw [← hh'', ← Category.assoc, ← Category.assoc, e.hom_inv_id, Category.id_comp]

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf)

/-! ### The two instance arguments on the ring map -/

/-- The identity of the sheaf of rings of a scheme is locally injective. -/
theorem isLocallyInjective_id_ringCatSheaf :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (X : TopCat))
      (𝟙 X.ringCatSheaf.obj) :=
  inferInstance

/-- The identity of the sheaf of rings of a scheme is locally surjective. -/
theorem isLocallySurjective_id_ringCatSheaf :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (X : TopCat))
      (𝟙 X.ringCatSheaf.obj) :=
  inferInstance

/-! ### The symmetric algebra -/

/-- **The symmetric algebra `Sym(F)` of a module sheaf on a scheme**, as a sheaf of graded
algebras over the scheme's sheaf of rings: the degreewise sheafification of the presheaf
`U ↦ Symⁿ_{𝒪_X(U)}(F(U))`. -/
@[ega "II 1.7.4" "special case"]
noncomputable def symmetricAlgebra : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf :=
  @PresheafOfModules.symmetricAlgebraSheafify.{u, u, u, u} _ _ _ X.sheaf.obj X.ringCatSheaf
    (𝟙 X.ringCatSheaf.obj) (isLocallyInjective_id_ringCatSheaf X)
    (isLocallySurjective_id_ringCatSheaf X) inferInstance inferInstance F.val

/-- The sheafification of `F` along the identity ring map is `F`: the counit of
`PresheafOfModules.sheafificationAdjunction` is an isomorphism, and `F` is already a sheaf. This
is what lets the degree-one generator of `Sym(F)` be taken out of `F` itself. -/
noncomputable def sheafificationIso :
    (PresheafOfModules.sheafification (α := 𝟙 X.ringCatSheaf.obj)).obj F.val ≅ F :=
  (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app F

/-- The degree-one generator of `Sym(F)`, out of `F` itself: the sheafified generator of the
sectionwise symmetric algebra, precomposed with `sheafificationIso`. -/
noncomputable def symmetricAlgebraGen : F ⟶ (symmetricAlgebra X F).piece 1 :=
  (sheafificationIso X F).inv ≫
    @PresheafOfModules.symmetricAlgebraSheafifyGen.{u, u, u, u} _ _ _ X.sheaf.obj X.ringCatSheaf
      (𝟙 X.ringCatSheaf.obj) (isLocallyInjective_id_ringCatSheaf X)
      (isLocallySurjective_id_ringCatSheaf X) inferInstance inferInstance F.val

/-- **`Sym(F)` is the symmetric algebra of `F`.** This is the `isSymmetricAlgebra` field of
`Stacks.ProjectiveBundle.Situation`: `Sym(F)` with its degree-one generator is universal among
sheaves of graded algebras over `𝒪_X` carrying a pairwise-commuting degree-one generator
of `F`. -/
theorem isSymmetricAlgebra_symmetricAlgebra :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra (symmetricAlgebra X F)
      (symmetricAlgebraGen X F) :=
  SheafOfModules.GradedAlgebra.isSymmetricAlgebra_of_iso_source (sheafificationIso X F)
    (@PresheafOfModules.isSymmetricAlgebra_symmetricAlgebraSheafify.{u, u, u, u} _ _ _
      X.sheaf.obj X.ringCatSheaf (𝟙 X.ringCatSheaf.obj) (isLocallyInjective_id_ringCatSheaf X)
      (isLocallySurjective_id_ringCatSheaf X) inferInstance inferInstance F.val)

/-- **Homogeneous multiplication in `Sym(F)` is commutative**, in every pair of degrees. This is
the `mul_comm` field of `Stacks.ProjectiveBundle.Situation`. -/
theorem symmetricAlgebra_mul_comm (i j : ℤ) (W : (Opens X)ᵒᵖ)
    (a : ((symmetricAlgebra X F).piece i).val.obj W)
    (b : ((symmetricAlgebra X F).piece j).val.obj W) :
    HEq (((symmetricAlgebra X F).mul i j).app W a b)
      (((symmetricAlgebra X F).mul j i).app W b a) :=
  @PresheafOfModules.symmetricAlgebraSheafify_mul_comm.{u, u, u, u} _ _ _ X.sheaf.obj
    X.ringCatSheaf (𝟙 X.ringCatSheaf.obj) (isLocallyInjective_id_ringCatSheaf X)
    (isLocallySurjective_id_ringCatSheaf X) inferInstance inferInstance F.val i j W a b

/-- **The negative-degree pieces of `Sym(F)` are zero.** This is the `negative_isZero` field of
`Stacks.ProjectiveBundle.Situation`. -/
theorem isZero_symmetricAlgebra_piece (n : ℤ) (hn : n < 0) :
    IsZero ((symmetricAlgebra X F).piece n) :=
  @PresheafOfModules.isZero_symmetricAlgebraSheafify_piece.{u, u, u, u} _ _ _ X.sheaf.obj
    X.ringCatSheaf (𝟙 X.ringCatSheaf.obj) (isLocallyInjective_id_ringCatSheaf X)
    (isLocallySurjective_id_ringCatSheaf X) inferInstance inferInstance F.val n hn

/-- A local section of `Sym(F)` in a negative degree vanishes. -/
theorem symmetricAlgebra_piece_eq_zero (n : ℤ) (hn : n < 0) (W : (Opens X)ᵒᵖ)
    (x : ((symmetricAlgebra X F).piece n).val.obj W) : x = 0 :=
  @PresheafOfModules.symmetricAlgebraSheafify_piece_eq_zero.{u, u, u, u} _ _ _ X.sheaf.obj
    X.ringCatSheaf (𝟙 X.ringCatSheaf.obj) (isLocallyInjective_id_ringCatSheaf X)
    (isLocallySurjective_id_ringCatSheaf X) inferInstance inferInstance F.val n hn W x

end AlgebraicGeometry.Scheme.Modules
