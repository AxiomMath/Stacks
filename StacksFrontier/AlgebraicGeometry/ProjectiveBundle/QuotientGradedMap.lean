module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.SymmetricToLaurentEpi
public import StacksFrontier.AlgebraicGeometry.SymmetricAlgebraFunctorial.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded map attached to a quotient by an invertible module

Tag 01O4's datum on a test scheme, and therefore the inverse direction of Tag 0B3V's bijection,
is a homomorphism of graded algebras

  `ψ : Sym(ℰ) ⟶ ⨁_{n ≥ 0} ℒ^{⊗ n}`

whose degree-one part is a given map `q : ℰ ⟶ ℒ`. **This file constructs it, for every module `ℰ`
and every invertible `ℒ` on every scheme, with no cover and no affineness**, and records that it
is the unique such.

It is a composite of two existing homomorphisms and introduces no new mathematics:

* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraMap q : Sym(ℰ) ⟶ Sym(ℒ)` is the functoriality
  of the symmetric algebra, and
* `Stacks.LineBundle.Situation.symmetricToLaurent : Sym(ℒ) ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}` compares the
  symmetric algebra of an invertible module with its Laurent algebra. That comparison is an
  isomorphism in *every* non-negative degree
  (`Stacks.LineBundle.Situation.isIso_symmetricToLaurent_app_natCast`), which is the content
  `Symⁿ ℒ ≅ ℒ^{⊗ n}` that a reader might otherwise expect to have to prove here.

The second of those is stated for a `Stacks.LineBundle.Situation`, a scheme carrying an
invertible module *together with a structure morphism to a base* used for the relative total
space. The Laurent algebra, the symmetric algebra and the comparison between them do not depend
on that morphism, so `Stacks.RelativeProj.invertibleSituation` supplies it as the identity.

## Main definitions

* `Stacks.RelativeProj.invertibleSituation`: a scheme with an invertible module, read as a line
  bundle situation over itself.
* `Stacks.RelativeProj.quotientLaurentAlgebra`: `⨁_{n ∈ ℤ} ℒ^{⊗ n}`, the target.
* `Stacks.RelativeProj.quotientGradedMap`: **the graded map `ψ` of Tag 01O4's datum**, for a map
  `q : ℰ ⟶ ℒ` into an invertible module.

## Main results

* `Stacks.RelativeProj.symmetricAlgebraGen_comp_quotientGradedMap`: **the degree-one
  normalisation** — `ψ` extends `q`, read through the two degree-one generators. This is the
  square that pins `ψ` down and the clause Tag 01O4's datum carries.
* `Stacks.RelativeProj.quotientGradedMap_unique`: it is the only unital homomorphism which does,
  so `ψ` is canonical rather than chosen.
* `Stacks.RelativeProj.quotientGradedMap_id`: at `q = 𝟙 ℒ` it is the comparison
  `symmetricToLaurent` itself, so the construction extends that one rather than competing
  with it.
* `Stacks.RelativeProj.quotientGradedMap_app_eq_zero`: it vanishes in negative degrees, where
  `Sym(ℰ)` is zero.
* `Stacks.RelativeProj.quotientGradedMap_comp`: functoriality in `q`, for a composite whose
  second factor is a map of invertible modules.

## Implementation notes

**Why the situation's base morphism is the identity.** `Stacks.LineBundle.Situation` bundles
`X`, a base `S`, a morphism `f : X ⟶ S` and the invertible module `L`. Of the four, only `X` and
`L` occur in `Situation.symmetricAlgebra`, `Situation.laurentAlgebra` and
`Situation.symmetricToLaurent`; `f` is what the *total space* of the line bundle is taken
relative to. Taking `S := X` and `f := 𝟙 X` therefore changes none of the three, and
`invertibleSituation_symmetricAlgebra` below is `rfl`, so no transport is introduced at any call
site.

**The degree index is `ℤ`.** `SheafOfModules.GradedAlgebra` is graded by `ℤ` and the Laurent
algebra is genuinely two-sided, while `Sym(ℰ)` vanishes below degree zero. The map therefore
exists in every integer degree and is zero in the negative ones
(`quotientGradedMap_app_eq_zero`); a consumer wanting Tag 01O4's `⨁_{n ≥ 0}` reads off the
non-negative components, as `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`
does with `sectionPieces`.

**No quasi-coherence is needed, and none is assumed.** The universal property of the symmetric
algebra of a sheaf of modules,
`AlgebraicGeometry.Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra`, holds over an arbitrary
base for an arbitrary module, and the Laurent algebra needs only invertibility of `ℒ`.
Quasi-coherence of `ℰ` is what the *projective bundle* of `ℰ` needs in order to exist, not what
this map needs, so it is left to the consumer.

No `@[stacks]` attribute is attached. Tag 01O4 is the representability assertion and Tag 0B3V the
bijection; this file supplies one input of the datum those are stated about and asserts neither.
Tag 01CG's symmetric algebra and Tag 01CU's tensor powers are registered where they are built.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules (symmetricAlgebra symmetricAlgebraGen symmetricAlgebraMap)
open SheafOfModules.GradedAlgebra (UnitalHom)

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **A scheme carrying an invertible module, read as a line bundle situation over itself.** The
structure morphism is the identity: the symmetric algebra, the Laurent algebra and the comparison
between them do not involve it, so this choice is invisible downstream. -/
def invertibleSituation : Stacks.LineBundle.Situation.{u} where
  X := X
  S := X
  f := 𝟙 X
  L := L

/-- The underlying scheme of `invertibleSituation L` is `X`. -/
@[simp]
theorem invertibleSituation_X : (invertibleSituation L).X = X := rfl

/-- The invertible module of `invertibleSituation L` is `L`. -/
@[simp]
theorem invertibleSituation_L : (invertibleSituation L).L = L := rfl

/-- The symmetric algebra of the situation is the symmetric algebra of `L`, on the nose. -/
theorem invertibleSituation_symmetricAlgebra :
    (invertibleSituation L).symmetricAlgebra = symmetricAlgebra X L := rfl

/-- **The Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of an invertible module**, the target of the graded
map of Tag 01O4's datum. -/
abbrev quotientLaurentAlgebra := (invertibleSituation L).laurentAlgebra

variable {F : X.Modules}

/-- The degree-one generator of the Laurent algebra, precomposed with `q`, still has pairwise
commuting image; this is `Stacks.LineBundle.Situation.pairwiseCommutes_laurentGen` carried along
`q` by `SheafOfModules.GradedAlgebra.pairwiseCommutes_comp`. -/
theorem pairwiseCommutes_comp_laurentGen (q : F ⟶ L) :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (q ≫ (invertibleSituation L).laurentGen) :=
  SheafOfModules.GradedAlgebra.pairwiseCommutes_comp q
    (invertibleSituation L).pairwiseCommutes_laurentGen

/-- **The graded map `ψ : Sym(ℰ) ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}` attached to a map `q : ℰ ⟶ ℒ` into an
invertible module.** This is the datum Tag 01O4 classifies morphisms into the projective bundle
by, and the inverse direction of Tag 0B3V's bijection consumes it at a surjective `q`.

It is the extension of `q ≫ laurentGen` along the universal property of `Sym(ℰ)`;
`quotientGradedMap_eq_comp` identifies it with the composite of `Sym(q)` and the
comparison `Stacks.LineBundle.Situation.symmetricToLaurent`. -/
@[ega "II 4.2.1" "partial"]
def quotientGradedMap (q : F ⟶ L) :
    UnitalHom (symmetricAlgebra X F) (quotientLaurentAlgebra L) :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F).isUniversal.desc
    (quotientLaurentAlgebra L) (q ≫ (invertibleSituation L).laurentGen)
    (pairwiseCommutes_comp_laurentGen L q)

/-- **The degree-one normalisation**: `ψ` extends `q`, read through the degree-one generator of
`Sym(ℰ)` and that of the Laurent algebra. This is the square of Tag 01O4's datum. -/
theorem symmetricAlgebraGen_comp_quotientGradedMap (q : F ⟶ L) :
    symmetricAlgebraGen X F ≫ (quotientGradedMap L q).app 1
      = q ≫ (invertibleSituation L).laurentGen :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F).isUniversal.desc_extends _ _ _

/-- **`ψ` is the only unital homomorphism with that degree-one part**, so it is canonical. -/
theorem quotientGradedMap_unique (q : F ⟶ L)
    {g : UnitalHom (symmetricAlgebra X F) (quotientLaurentAlgebra L)}
    (hg : symmetricAlgebraGen X F ≫ g.app 1 = q ≫ (invertibleSituation L).laurentGen) :
    g = quotientGradedMap L q :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F).isUniversal.desc_unique _ _ _ hg

/-- **At `q = 𝟙 L` the graded map is the comparison of `Sym(L)` with its Laurent
algebra**, so this construction extends `Stacks.LineBundle.Situation.symmetricToLaurent` rather
than coining a second comparison. -/
theorem quotientGradedMap_id :
    quotientGradedMap L (𝟙 L) = (invertibleSituation L).symmetricToLaurent :=
  (invertibleSituation L).symmetricToLaurent_unique
    (show symmetricAlgebraGen X L ≫ (quotientGradedMap L (𝟙 L)).app 1
        = (invertibleSituation L).laurentGen from
      (symmetricAlgebraGen_comp_quotientGradedMap L (𝟙 L)).trans (Category.id_comp _))

/-- **`ψ` vanishes in negative degrees**, where `Sym(ℰ)` is zero while the Laurent algebra is
not. -/
theorem quotientGradedMap_app_eq_zero (q : F ⟶ L) (n : ℤ) (hn : n < 0) :
    (quotientGradedMap L q).app n = 0 :=
  (Scheme.Modules.isZero_symmetricAlgebra_piece X F n hn).eq_of_src _ _

/-- **Functoriality in `q`.** Precomposing the quotient map with a map of modules precomposes the
graded map with `Sym` of it. -/
theorem quotientGradedMap_comp {E : X.Modules} (p : E ⟶ F) (q : F ⟶ L) :
    quotientGradedMap L (p ≫ q) = (symmetricAlgebraMap p).comp (quotientGradedMap L q) :=
  (quotientGradedMap_unique L (p ≫ q)
    (show symmetricAlgebraGen X E
          ≫ ((symmetricAlgebraMap p).app 1 ≫ (quotientGradedMap L q).app 1)
        = (p ≫ q) ≫ (invertibleSituation L).laurentGen from
      ((Category.assoc (symmetricAlgebraGen X E) ((symmetricAlgebraMap p).app 1)
            ((quotientGradedMap L q).app 1)).symm.trans
        ((congrArg (fun z => z ≫ (quotientGradedMap L q).app 1)
            (Scheme.Modules.symmetricAlgebraGen_comp_symmetricAlgebraMap p)).trans
          ((Category.assoc p (symmetricAlgebraGen X F)
              ((quotientGradedMap L q).app 1)).trans
            ((congrArg (fun z => p ≫ z)
                (symmetricAlgebraGen_comp_quotientGradedMap L q)).trans
              (Category.assoc p q (invertibleSituation L).laurentGen).symm)))))).symm

/-- **`ψ` is `Sym(q)` followed by the comparison of `Sym(ℒ)` with the Laurent algebra.** This is
the description the module docstring gives, obtained from functoriality at `q = 𝟙 ℒ`. -/
theorem quotientGradedMap_eq_comp (q : F ⟶ L) :
    quotientGradedMap L q
      = (symmetricAlgebraMap q).comp (invertibleSituation L).symmetricToLaurent := by
  rw [← quotientGradedMap_id L, ← quotientGradedMap_comp L q (𝟙 L), Category.comp_id]

end Stacks.RelativeProj

end
