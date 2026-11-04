module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSmooth

/-!
# The Picard stack is smooth in relative dimension one (Stacks 0DPJ)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` which is flat, proper and of
finite presentation (the standing assumptions of Section 0DM9), and of relative dimension `≤ 1`.
Then the structure morphism `Picardstack_{X/B} ⟶ B` is smooth ([Stacks, Tag 0DPJ]).

The statement is read in the 2-category of algebraic stacks, so it presupposes that
`Picardstack_{X/B}` is algebraic; this is Stacks 0D04,
`AlgebraicGeometry.Space.isAlgebraicStack_picardCFG`, which holds under the same standing
assumptions. The proof is
`AlgebraicGeometry.Space.isSmooth_picardStructureMorphism_of_isAlgebraicStack`, which carries out
the source's argument with the algebraicity as its only input.

## Main results

* `AlgebraicGeometry.Space.isSmooth_picardStructureMorphism`: **Stacks 0DPJ**.

## References

* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
-/

@[expose] public section

namespace AlgebraicGeometry.Space

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0DPJ: the Picard stack is smooth in relative dimension `≤ 1`.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` which is flat, proper, of finite presentation (a field of the
standing datum `D`) and of relative dimension `≤ 1`. Then the structure morphism
`Picardstack_{X/Y} ⟶ Y` is smooth, as a 1-morphism of algebraic stacks; the Picard stack is
algebraic by Stacks 0D04. -/
@[stacks 0DPJ "the full statement: f flat (hflat), proper (hproper), of finite presentation (the \
field of D) and of relative dimension ≤ 1 (hd); Picardstack_{X/B} → B is smooth; the algebraicity \
of Picardstack_{X/B} is Stacks 0D04, proved, not assumed"]
theorem isSmooth_picardStructureMorphism (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    (hd : HasRelativeDimensionLE 1 B S hS D.f.hom) :
    Stack.AlgebraicStacks.IsSmooth B S hS
      (picardStructureMorphism D (isAlgebraicStack_picardCFG.{u, w} D hflat hproper)) :=
  isSmooth_picardStructureMorphism_of_isAlgebraicStack D hflat hproper hd
    (isAlgebraicStack_picardCFG D hflat hproper)

end AlgebraicGeometry.Space

end
