module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtaleAlgebra

/-!
# The two remaining inputs of flat base change for the extension algebra are one input

Let `g : X' ⟶ X` be a morphism of schemes and let `W` be a scheme over `X` with structure
morphism `f`.  The base-change clause of [Stacks, Tag 0EY6] asks that the square
```
g⁻¹𝒪_X ⟶ g⁻¹(f_* 𝒪_W)
   ↓              ↓
 𝒪_{X'} ⟶  f'_* 𝒪_{W ×_X X'}
```
be a pushout, i.e. that `f'_* 𝒪_{W ×_X X'}` be the extension of scalars
`g⁻¹(f_* 𝒪_W) ⊗_{g⁻¹𝒪_X} 𝒪_{X'}`.  That it is a pushout as soon as the canonical comparison
`Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHom` is invertible is
`Stacks.FundamentalGroup.isPushout_pushforwardBaseChangeMap_of_isIso`.  This file proves the
converse, and draws the consequence that the two outstanding inputs of Tag 0EY6 are the same
input.

**The converse.**  The abstract algebra pullback sits in a pushout square with the same span
(`Stacks.AffineAlgebraEquivalence.algebraPullback_isPushout`), and `baseChangeAlgebraHom` is a
morphism of cocones over that span: it matches the two left-hand legs by
`algebraPullbackMap_comp_baseChangeAlgebraHom` and the two structure morphisms because it is a
morphism of algebras.  A morphism of cocones between two colimits of one diagram is invertible,
so the pushout property of the displayed square is *equivalent* to invertibility of the
comparison.

**One input, not two.**  Quasi-coherence of the algebra pullback — the
`algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA], which is what makes the
pulled-back extension algebra of Tag 0EY6 statable at all — was reduced in
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_isIso` to invertibility of
`baseChangeAlgebraHom` at the structure morphism of the relative spectrum, a morphism which is
affine and hence quasi-compact and quasi-separated.  Combining that with the converse above:
the base-change clause of Tag 0EY6, applied to the relative spectrum of a quasi-coherent
algebra, *implies* quasi-coherence of the algebra pullback along a flat morphism.  So the
two apparently independent gaps — the pushout square, and quasi-coherence of the pullback — are
one statement, namely flat base change for the direct image, [Stacks, Tag 02KH].

## Main results

* `Stacks.FundamentalGroup.isIso_baseChangeAlgebraHom_of_isPushout` — the converse of
  `isPushout_pushforwardBaseChangeMap_of_isIso`.
* `Stacks.FundamentalGroup.isPushout_pushforwardBaseChangeMap_iff_isIso` — the two are
  equivalent, for an arbitrary morphism and an arbitrary scheme over the base.
* `Stacks.FundamentalGroup.isQuasicoherent_algebraPullback_of_isPushout` — the pushout square
  at the structure morphism of the relative spectrum of a quasi-coherent algebra `A` implies
  that `g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'}` is quasi-coherent.
* `Stacks.FundamentalGroup.isQuasicoherent_algebraPullback_of_flatBaseChange` — the same with
  the hypothesis in the shape in which [Stacks, Tag 0EY6] states it, for flat `g`.

## Implementation notes

The inverse comparison is `CategoryTheory.IsPushout.desc` of the span's legs into the abstract
algebra pullback, and the two identities are
`CategoryTheory.IsPushout.hom_ext` for the two squares.  Invertibility is then transferred from
the underlying sheaf of rings to the algebra by `CategoryTheory.isIso_of_reflects_iso` along
`CategoryTheory.Under.forget`, which reflects isomorphisms; no inverse morphism of algebras has
to be written down.

`isQuasicoherent_algebraPullback_of_flatBaseChange` takes the base-change clause of Tag 0EY6 as
a hypothesis rather than proving it:  no declaration on this branch carries it, and it is not
proved here.  Its hypothesis is stated with exactly the binders, instance arguments and
universe of the statement of Tag 0EY6, so that a proof of that statement discharges it by
`exact`.  Note
that flatness of `g` is used only to instantiate that hypothesis; the clause of Tag 01SA is
asserted for an arbitrary morphism, and nothing here gets it for one.

**No `@[stacks]` attribute is placed in this file.**  Tag 0EY6 is carried by several declarations
whose clause labels are free text, so a tag here would mark the whole of 0EY6 as formalized
while the base-change clause and the reflexivity clause are both open; and the
clause of Tag 01SA that this file is about is not proved either, only reduced.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.FundamentalGroup

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (W : Over X)

/-- The sheaf of rings underlying the canonical base-change comparison of algebras is
invertible as soon as the extension-of-scalars square for the direct image is a pushout: it is
a morphism of cocones between two colimits of one span. -/
public theorem isIso_right_baseChangeAlgebraHom_of_isPushout
    (h : IsPushout
      ((TopCat.Sheaf.pullback CommRingCat g.base).map (pushforwardAlgebra W.hom).hom)
      (inverseImageStructureMap g)
      (pushforwardBaseChangeMap g W)
      (pushforwardAlgebra ((Over.pullback g).obj W).hom).hom) :
    IsIso (baseChangeAlgebraHom g W).right := by
  have hp := algebraPullback_isPushout g (pushforwardAlgebra W.hom)
  have hinl : (algebraPullbackMap g).app (pushforwardAlgebra W.hom) ≫
      (baseChangeAlgebraHom g W).right = pushforwardBaseChangeMap g W :=
    algebraPullbackMap_comp_baseChangeAlgebraHom g W
  have hinr : ((algebraPullback g).obj (pushforwardAlgebra W.hom)).hom ≫
      (baseChangeAlgebraHom g W).right =
      (pushforwardAlgebra ((Over.pullback g).obj W).hom).hom :=
    Under.w (baseChangeAlgebraHom g W)
  set ψ := h.desc ((algebraPullbackMap g).app (pushforwardAlgebra W.hom))
    ((algebraPullback g).obj (pushforwardAlgebra W.hom)).hom hp.w with hψ
  refine ⟨ψ, hp.hom_ext ?_ ?_, h.hom_ext ?_ ?_⟩
  · erw [← Category.assoc, hinl, h.inl_desc, Category.comp_id]
  · erw [← Category.assoc, hinr, h.inr_desc, Category.comp_id]
  · erw [← Category.assoc, h.inl_desc, hinl, Category.comp_id]
  · erw [← Category.assoc, h.inr_desc, hinr, Category.comp_id]

/-- **The converse of `isPushout_pushforwardBaseChangeMap_of_isIso`.**  If the
extension-of-scalars square for the direct image of the structure sheaf is a pushout, then the
canonical base-change comparison of algebras is an isomorphism. -/
public theorem isIso_baseChangeAlgebraHom_of_isPushout
    (h : IsPushout
      ((TopCat.Sheaf.pullback CommRingCat g.base).map (pushforwardAlgebra W.hom).hom)
      (inverseImageStructureMap g)
      (pushforwardBaseChangeMap g W)
      (pushforwardAlgebra ((Over.pullback g).obj W).hom).hom) :
    IsIso (baseChangeAlgebraHom g W) :=
  have : IsIso ((Under.forget X'.sheaf).map (baseChangeAlgebraHom g W)) :=
    isIso_right_baseChangeAlgebraHom_of_isPushout g W h
  isIso_of_reflects_iso (baseChangeAlgebraHom g W) (Under.forget X'.sheaf)

/-- **The base-change clause of [Stacks, Tag 0EY6] is equivalent to invertibility of the
canonical comparison.**  For an arbitrary morphism `g : X' ⟶ X` and an arbitrary scheme `W`
over `X`, the square exhibiting `f'_* 𝒪_{W ×_X X'}` as the extension of scalars of
`f_* 𝒪_W` is a pushout precisely when `baseChangeAlgebraHom g W` is an isomorphism. -/
public theorem isPushout_pushforwardBaseChangeMap_iff_isIso :
    IsPushout
      ((TopCat.Sheaf.pullback CommRingCat g.base).map (pushforwardAlgebra W.hom).hom)
      (inverseImageStructureMap g)
      (pushforwardBaseChangeMap g W)
      (pushforwardAlgebra ((Over.pullback g).obj W).hom).hom ↔
      IsIso (baseChangeAlgebraHom g W) :=
  ⟨isIso_baseChangeAlgebraHom_of_isPushout g W,
    isPushout_pushforwardBaseChangeMap_of_isIso g W⟩

/-- **Quasi-coherence of the algebra pullback follows from the base-change clause of
[Stacks, Tag 0EY6] at the relative spectrum.**  Let `A` be a quasi-coherent sheaf of
commutative `𝒪_X`-algebras and let `f` be the structure morphism of its relative spectrum.  If
the extension-of-scalars square for `f_* 𝒪` is a pushout, then `g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'}` is
quasi-coherent.  This is the `algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA]
at `g`. -/
public theorem isQuasicoherent_algebraPullback_of_isPushout (A : AlgebraSheaf X)
    [A.IsQuasicoherent]
    (h : IsPushout
      ((TopCat.Sheaf.pullback CommRingCat g.base).map
        (pushforwardAlgebra (Over.mk (relativeSpecToBase A)).hom).hom)
      (inverseImageStructureMap g)
      (pushforwardBaseChangeMap g (Over.mk (relativeSpecToBase A)))
      (pushforwardAlgebra ((Over.pullback g).obj (Over.mk (relativeSpecToBase A))).hom).hom) :
    AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) :=
  isQuasicoherent_algebraPullback_of_isIso g A
    (isIso_baseChangeAlgebraHom_of_isPushout g (Over.mk (relativeSpecToBase A)) h)

/-- **The two outstanding inputs of flat base change for the extension algebra are one
input.**  Granting the base-change clause of [Stacks, Tag 0EY6] — that the extension of
scalars of a direct image along a quasi-compact quasi-separated morphism is the direct image of
the base-changed scheme, for a flat morphism of bases — the pullback of a quasi-coherent
algebra along a flat morphism is quasi-coherent.  The latter is the
`algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA], and is what makes the pulled-back
extension algebra of Tag 0EY6 statable.  Neither statement is proved on this branch; what is
proved here is that the first gives the second, so that there is one remaining mathematical
input and not two. -/
public theorem isQuasicoherent_algebraPullback_of_flatBaseChange
    (hbc : ∀ {V Y Y' : Scheme.{u}} (f : V ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      (q : Y' ⟶ Y) [Flat q],
      IsPushout
        ((TopCat.Sheaf.pullback CommRingCat q.base).map (pushforwardAlgebra f).hom)
        (inverseImageStructureMap q)
        (pushforwardBaseChangeMap q (Over.mk f))
        (pushforwardAlgebra ((Over.pullback q).obj (Over.mk f)).hom).hom)
    [Flat g] (A : AlgebraSheaf X) [A.IsQuasicoherent] :
    AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) :=
  have : IsAffineHom (relativeSpecToBase A) := isAffineHom_relativeSpecToBase A
  isQuasicoherent_algebraPullback_of_isPushout g A (hbc (relativeSpecToBase A) g)

end Stacks.FundamentalGroup

end
