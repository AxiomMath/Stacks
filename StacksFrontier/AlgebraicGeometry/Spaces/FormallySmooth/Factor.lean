module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formal properties of the first factor of a composite transformation

Let `a : F ⟶ G` and `b : G ⟶ H` be transformations of set-valued functors on the big fppf
site over a scheme, and assume `b` is formally unramified. Then each of the three formal
properties of the composite `a ≫ b` is inherited by `a`, and formal unramifiedness of `a`
already follows from formal unramifiedness of `b` and of the composite.

## Main results

* `AlgebraicGeometry.Space.liftingSet_comp_eq` says that composing with a formally
  unramified transformation does not change the set of lifts of a fixed section.
* `AlgebraicGeometry.Space.formallySmooth_of_comp_of_formallyUnramified`,
  `AlgebraicGeometry.Space.formallyEtale_of_comp_of_formallyUnramified` and
  `AlgebraicGeometry.Space.formallyUnramified_left_of_comp` give the three conclusions about
  the first factor.

## Implementation notes

Composition of transformations is categorical composition, so `a ≫ b` denotes the composite
called `b ∘ a` in the source. The sections and the closed immersion are objects and a
morphism in the big fppf slice over the base scheme, and all lifting conditions are those of
Tag 049S.

## References

* [Stacks Project, Tag 04G5](https://stacks.math.columbia.edu/tag/04G5)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}

/-- A lift for `a` is a lift for `a ≫ b` of the postcomposed square. -/
private theorem isLift_comp_of_isLift {a : F ⟶ G} (b : G ⟶ H) {T T' : BigFppfOver B S hS}
    {i : T ⟶ T'} {x : F.obj (op T)} {y : G.obj (op T')} {z : F.obj (op T')}
    (h : IsLift a i x y z) : IsLift (a ≫ b) i x (b.app (op T') y) z :=
  ⟨h.1, by simpa using congrArg (b.app (op T')) h.2⟩

/-- Composing with a formally unramified transformation does not change the
set of lifts of a fixed section over an affine square-zero thickening. -/
public lemma liftingSet_comp_eq (a : F ⟶ G) (b : G ⟶ H)
    (hb : FormallyUnramified b)
    (T T' : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)
    (x : F.obj (op T)) (y : G.obj (op T'))
    (hxy : a.app (op T) x = G.map i.op y) :
    {z : F.obj (op T') | IsLift a i x y z} =
      {z : F.obj (op T') | IsLift (a ≫ b) i x (b.app (op T') y) z} := by
  ext z
  refine ⟨fun h => isLift_comp_of_isLift b h, fun ⟨hres, hcomp⟩ => ⟨hres, ?_⟩⟩
  have hrestr : G.map i.op (a.app (op T') z) = a.app (op T) x := by
    simpa [hres] using (a.naturality_apply i.op z).symm
  exact hb T T' hT hT' i hi (a.app (op T) x) (b.app (op T') y)
    (by simp [hxy]) (a.app (op T') z) y
    ⟨hrestr, by simpa using hcomp⟩ ⟨hxy.symm, rfl⟩

/-- **Stacks 04G5, smooth.** Formal smoothness of a composite descends to its
first factor when the second factor is formally unramified. -/
@[stacks 04G5 "smooth", ega "IV 17.1.4" "formally smooth case", ega "IV 17.1.5" "necessity, smooth"]
public theorem formallySmooth_of_comp_of_formallyUnramified (a : F ⟶ G) (b : G ⟶ H)
    (hb : FormallyUnramified b)
    (hba : FormallySmooth (a ≫ b)) :
    FormallySmooth a := by
  intro T T' hT hT' i hi x y hxy
  change Set.Nonempty {z : F.obj (op T') | IsLift a i x y z}
  rw [liftingSet_comp_eq a b hb T T' hT hT' i hi x y hxy]
  exact hba T T' hT hT' i hi x (b.app (op T') y) (by simp [hxy])

/-- **Stacks 04G5, étale case.** A first factor of a formally étale
transformation is formally étale if the second factor is formally unramified. -/
@[stacks 04G5 "etale", ega "IV 17.1.4" "formally étale case", ega "IV 17.1.5" "necessity, étale"]
public theorem formallyEtale_of_comp_of_formallyUnramified (a : F ⟶ G) (b : G ⟶ H)
    (hb : FormallyUnramified b)
    (hba : FormallyEtale (a ≫ b)) :
    FormallyEtale a := by
  intro T T' hT hT' i hi x y hxy
  change ∃! z, z ∈ {z | IsLift a i x y z}
  rw [liftingSet_comp_eq a b hb T T' hT hT' i hi x y hxy]
  exact hba T T' hT hT' i hi x (b.app (op T') y) (by simp [hxy])

/-- **Stacks Project, Tag 04G5, unramified case.** If a transformation and a
composite ending in it are formally unramified, so is the first factor. -/
@[stacks 04G5 "unramified",
  ega "IV 17.1.3" "(v), b fmly unramified",
  ega "IV 17.1.5" "necessity, unramified"]
public theorem formallyUnramified_left_of_comp (a : F ⟶ G) (b : G ⟶ H)
    (_hb : FormallyUnramified b)
    (hba : FormallyUnramified (a ≫ b)) :
    FormallyUnramified a := by
  intro T T' hT hT' i hi x y hxy z₁ z₂ hz₁ hz₂
  exact hba T T' hT hT' i hi x (b.app (op T') y)
    (by simp [hxy]) z₁ z₂
    (isLift_comp_of_isLift b hz₁) (isLift_comp_of_isLift b hz₂)

end AlgebraicGeometry.Space

end
