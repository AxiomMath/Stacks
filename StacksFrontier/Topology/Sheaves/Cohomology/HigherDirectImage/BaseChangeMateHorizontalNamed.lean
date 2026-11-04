module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.BaseChangeMateHorizontalPasting

/-!
# Horizontal pasting of the base change mate, read through three given names

Two commutative squares sharing a vertical edge paste to a commutative rectangle:

```
        g''        g'
  X'' ———→ X' ———→ X
   | f''     | f'    | f
   v         v       v
  Y'' ———→ Y' ———→ Y
         h         g
```

`Stacks.Cohomology.BaseChange.mate_horizontal` is the pasting law of **Stacks 0E47** for the
base change mate, with each of the three base change maps written as the mate of its square.
This file restates it with the three maps supplied as morphisms together with an equation
identifying each with the mate of its square.

## Main results

* `Stacks.Cohomology.BaseChange.mate_horizontal_of_eq`: the pasting law, read through three
  given names for its base change maps.

## Implementation notes

*Why a geometric instance of the law needs this.*  Nothing is added to the mathematics:  the
proof substitutes the three equations and applies `mate_horizontal`.  What it buys is that the
law can be *stated* at a seating where the mate cannot be written three times in one
proposition.  At the one **Stacks 073K**, part (1) needs — the six categories the `𝒪`-modules of
the small étale ringed topoi of six algebraic spaces — the statement of the law with its three
base change maps spelled as `Stacks.Cohomology.ToposBaseChange.moduleBaseChange` is a
`(deterministic) timeout at isDefEq` at 200,000 heartbeats with the proof stubbed out, so that
only the statement is elaborated (12.0s to fail);  the same statement with
each of the three written as the named
`AlgebraicGeometry.Space.toposModuleBaseChangeMap`, and nothing else changed, elaborates in
3.8s.  Taking the three as variables puts each occurrence of the mate in an equation of its own,
where one at a time it is affordable, and leaves the law's statement free.

*Why this is the generic engine and not the ringed-topoi one that gets generalized.*  The
geometric application reads the nine inverse images at the spelling of the modules development —
`AlgebraicGeometry.Space.modulePullback` — and the nine direct images at the spelling of the
ringed topoi.  Here all eighteen are variables, so that mixed reading is available;  in the
ringed-topoi law
`Stacks.Cohomology.ToposBaseChange.moduleBaseChange_horizontal_of_eq` the inverse images are
`Stacks.Sheaves.RingedToposModules.pullbackModules` of the given morphisms of ringed topoi,
and re-spelling the cocycle condition of **Stacks 03LU** into that form is a `maximum recursion
depth` even as its own isolated lemma (10.0s to fail), whereas at the mixed
reading the cocycle condition is accepted with nothing done to it.

*Where a direct geometric instance of this law stalls.*  Not the
engine, and not any of its hypotheses.  At the mixed seating the whole application elaborates —
nine adjunctions `AlgebraicGeometry.Space.toposModulePullbackAdjunction`, the three comparisons
of composite direct images, the two comparisons of composite inverse images, the three square
comparisons, three names for the base change maps, the three equations identifying them, the
three **Stacks 03D8** identifications and the cocycle condition — in 4.3s, *provided it is
elaborated with no expected type*.  Its inferred conclusion then prints as exactly the wanted
law.  Matching it against a written statement of that law does not finish:  `timeout at whnf` at
200,000 heartbeats, 7.6s to fail, both with the three maps written as
`toposModuleBaseChangeMap` and with them written as `mate` of the named adjunctions, and both
when the term is elaborated against the goal and when it is elaborated first and matched with
`exact`.  Since the printed type is what is written, the difference is in implicit arguments the
two elaborations choose differently.

*Which implicit arguments they are, and the law's geometric instance.*  They are not the
objects of the four-fold composite, where the two vocabularies for the *inverse* image disagree,
`pullbackModules` of the morphism of
ringed topoi against `AlgebraicGeometry.Space.modulePullback`: that divergence is
real, but removing it leaves the timeout exactly where it was.  The arguments that differ are
the **categories**:  this engine takes its six from the adjunctions it is given, so a geometric
instance gets the modules development's `AlgebraicGeometry.Space.Modules`, whereas
`Stacks.Sheaves.RingedToposModules.pushforwardModules` is itself typed at
`SheafOfModules (structureRingSheaf …)`, so a written statement mentioning one gets the
ringed-topoi spelling and the comparison has to unfold the small étale ringed topos at every
occurrence — ninety-two of them against the engine's ten.  Giving the direct images their
categories positionally rather than letting them be inferred removes the divergence, and a type
ascription does *not* do it, being discharged by a defeq check after which the term keeps its own
type.  The law's geometric instance is then this engine applied once, and is
`AlgebraicGeometry.Space.toposModuleBaseChangeMap_horizontal`.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Cohomology.BaseChange

section HorizontalNamed

variable {A B C D C₂ D₂ : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* C₂] [Category* D₂]
    {Lf : B ⥤ A} {F : A ⥤ B} (adjf : Lf ⊣ F)
    {Lf' : D ⥤ C} {F' : C ⥤ D} (adjf' : Lf' ⊣ F')
    {Lf'' : D₂ ⥤ C₂} {F'' : C₂ ⥤ D₂} (adjf'' : Lf'' ⊣ F'')
    {G : B ⥤ D} {P : D ⥤ B} (adjg : G ⊣ P)
    {G' : A ⥤ C} {P' : C ⥤ A} (adjg' : G' ⊣ P')
    {H : D ⥤ D₂} {Q : D₂ ⥤ D} (adjh : H ⊣ Q)
    {H' : C ⥤ C₂} {Q' : C₂ ⥤ C} (adjh' : H' ⊣ Q')
    {G₀ : B ⥤ D₂} {P₀ : D₂ ⥤ B} (adjg₀ : G₀ ⊣ P₀)
    {G'₀ : A ⥤ C₂} {P'₀ : C₂ ⥤ A} (adjg'₀ : G'₀ ⊣ P'₀)
    (e : P' ⋙ F ≅ F' ⋙ P) (e₂ : Q' ⋙ F' ≅ F'' ⋙ Q) (e₀ : P'₀ ⋙ F ≅ F'' ⋙ P₀)
    (eH : G ⋙ H ≅ G₀) (eG : G' ⋙ H' ≅ G'₀)
    (α : TwoSquare G Lf Lf' G') (α₂ : TwoSquare H Lf' Lf'' H')
    (α₀ : TwoSquare G₀ Lf Lf'' G'₀)

/-- **Horizontal pasting of the base change mate, read through three given names**:
`Stacks.Cohomology.BaseChange.mate_horizontal`, the pasting law of **Stacks 0E47**, with each of
the three base change maps supplied as a morphism `τ₀`, `τ`, `τ₂` together with an equation
identifying it with the mate of its square.

The content is `mate_horizontal`;  the three equations are substituted and it is applied.  What
the restatement is for is that a geometric instance of the law can be stated at all — see the
implementation notes of this file. -/
theorem mate_horizontal_of_eq
    (τ₀ : F ⋙ G₀ ⟶ G'₀ ⋙ F'') (τ : F ⋙ G ⟶ G' ⋙ F') (τ₂ : F' ⋙ H ⟶ H' ⋙ F'')
    (hτ₀ : τ₀ = mate adjg₀ adjg'₀ F F'' e₀)
    (hτ : τ = mate adjg adjg' F F' e)
    (hτ₂ : τ₂ = mate adjh adjh' F' F'' e₂)
    (hα : conjugateEquiv (adjf.comp adjg') (adjg.comp adjf') α = e.hom)
    (hα₂ : conjugateEquiv (adjf'.comp adjh') (adjh.comp adjf'') α₂ = e₂.hom)
    (hα₀ : conjugateEquiv (adjf.comp adjg'₀) (adjg₀.comp adjf'') α₀ = e₀.hom)
    (hs : ∀ M : B, Lf''.map (eH.inv.app M) ≫ α₂.app (G.obj M) ≫
      H'.map (α.app M) ≫ eG.hom.app (Lf.obj M) = α₀.app M)
    (K : A) :
    τ₀.app K =
      eH.inv.app (F.obj K) ≫ H.map (τ.app K) ≫ τ₂.app (G'.obj K) ≫ F''.map (eG.hom.app K) := by
  subst hτ₀
  subst hτ
  subst hτ₂
  exact (mate_horizontal adjf adjf' adjf'' adjg adjg' adjh adjh' adjg₀ adjg'₀ e e₂ e₀ eH eG
    α α₂ α₀ hα hα₂ hα₀ hs K).symm

end HorizontalNamed

end Stacks.Cohomology.BaseChange

end
