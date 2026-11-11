module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackHom
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenCoarserSites
public import StacksFrontier.Examples.Spaces.DoubledOriginGroupSpace

/-!
# The classifying stack of `(ℤ/2)_S` is quasi-compact and quasi-separated over `S`

Let `S` be a scheme of a big fppf site and `G` a smooth group algebraic space over `S`. The
classifying stack `BG = [S/G]` receives the surjective atlas `S ⟶ BG`, so it is quasi-compact as
soon as `S` is, and then its structure 1-morphism `BG ⟶ S` is quasi-compact when `S` is moreover
quasi-separated (Stacks 050X along the atlas). When `G ⟶ S` is proper, flat and locally of finite
presentation, `BG` is separated over `S` (Stacks 0DTY, part (6), at the trivial action), hence
quasi-separated over `S` (Stacks 050E).

We apply this to `S = 𝔸¹_k = Spec k[x]` for a field `k` and `G = (ℤ/2)_S`, the constant group
`S ⊔ S`, which is finite étale over `S`: the structure 1-morphism of `B(ℤ/2)_S` is quasi-compact
and quasi-separated.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactStack_classifyingAlgebraicStack`: `BG` is quasi-compact
  when `S` is.
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_structureMorphism_classifyingAlgebraicStack`:
  `BG ⟶ S` is quasi-compact when `S` is quasi-compact and quasi-separated.
* `AlgebraicGeometry.Stack.isQuasiSeparated_structureMorphism_classifyingAlgebraicStack`:
  `BG ⟶ S` is quasi-separated when `G ⟶ S` is proper, flat and locally of finite presentation.
* `Stacks.Examples.isQuasiCompactMorphism_structureMorphism_classifyingStack_constantZ2GroupSpace`
  and
  `Stacks.Examples.isQuasiSeparated_structureMorphism_classifyingStack_constantZ2GroupSpace`:
  the two statements for `B(ℤ/2)_S` over the affine line.
* `Stacks.Examples.isQuasiCompactMorphism_structureMorphism_classifyingStack_trivialDoubleCover`
  and
  `Stacks.Examples.isQuasiSeparated_structureMorphism_classifyingStack_trivialDoubleCover`:
  the same two statements for `(ℤ/2)_S = S ⊔ S` over any quasi-compact and quasi-separated `S`
  (any `S` for quasi-separatedness).
* `Stacks.Examples.exists_bigFppfSite_bigEtaleSite_contains`: a big fppf site containing the
  affine line together with a big étale site of the same size cutoff.

## References

* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 050X](https://stacks.math.columbia.edu/tag/050X)
* [Stacks Project, Tag 0DTY](https://stacks.math.columbia.edu/tag/0DTY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **The classifying stack of a smooth group over a quasi-compact base is quasi-compact**: it is
the image of the quasi-compact scheme `S` under its surjective atlas `S ⟶ BG` (Stacks 044R). -/
theorem isQuasiCompactStack_classifyingAlgebraicStack [CompactSpace S]
    (G : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
      (Space.terminalSpace C S hS).property)
    (hG : Space.IsSmooth C S hS G.obj.X.hom) :
    IsQuasiCompactStack.{u, w} C S hS (classifyingAlgebraicStack.{u, w} G hG).val
      (classifyingAlgebraicStack.{u, w} G hG).property := by
  have hc : CompactSpace ((BigFppfOver.toScheme C S hS).obj (Space.baseTerminal C S hS)) :=
    inferInstanceAs (CompactSpace S)
  exact isQuasiCompactStack_of_isSurjective C S hS (classifyingAtlas.{u, w} G hG)
    (isQuasiCompactStack_fibredCategory C S hS (Space.terminalSpace C S hS).obj
      (Space.terminalSpace C S hS).property (Space.isQuasiCompactSpace_yoneda_obj C S hS hc) _)
    (classifyingAtlas_fppf.{u, w} G hG).2.1

/-- **The structure morphism of the classifying stack of a smooth group over a quasi-compact and
quasi-separated base is quasi-compact** (Stacks 050U): the classifying stack is quasi-compact, and
a quasi-compact algebraic stack over a quasi-separated base has quasi-compact structure
morphism. -/
theorem isQuasiCompactMorphism_structureMorphism_classifyingAlgebraicStack [CompactSpace S]
    [QuasiSeparatedSpace S]
    (G : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
      (Space.terminalSpace C S hS).property)
    (hG : Space.IsSmooth C S hS G.obj.X.hom) :
    IsQuasiCompactMorphism.{u, w} C S hS
      (structureMorphism.{u, w} C S hS (classifyingAlgebraicStack.{u, w} G hG)) :=
  isQuasiCompactMorphism_structureMorphism C S hS inferInstance _
    (isQuasiCompactStack_classifyingAlgebraicStack G hG)

/-- **The structure morphism of `BG` is quasi-separated when `G ⟶ S` is proper, flat and locally
of finite presentation** (Stacks 04YW): `BG` is then separated over `S`, and a separated
1-morphism of algebraic stacks is quasi-separated (Stacks 050E). -/
theorem isQuasiSeparated_structureMorphism_classifyingAlgebraicStack
    (G : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
      (Space.terminalSpace C S hS).property)
    (hG : Space.IsSmooth C S hS G.obj.X.hom)
    (hproper : Space.IsProper C S hS G.obj.X.hom) (hflat : Space.IsFlat C S hS G.obj.X.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS G.obj.X.hom) :
    AlgebraicStacks.IsQuasiSeparated C S hS
      (structureMorphism.{u, w} C S hS (classifyingAlgebraicStack.{u, w} G hG)) :=
  AlgebraicStacks.isQuasiSeparated_of_isSeparated C S hS
    (isSeparatedOver_classifyingAlgebraicStack.{u, w} G hG hproper hflat hlfp)

end AlgebraicGeometry.Stack

open AlgebraicGeometry

namespace Stacks.Examples

section ConstantZModTwo

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} (hS : 𝒞.Contains S)

/-- `(ℤ/2)_S = S ⊔ S ⟶ S` is proper, for any scheme `S` of the site. -/
theorem isProper_trivialDoubleCover_groupSpace :
    Space.IsProper 𝒞 S hS
      ((trivialDoubleCover S).groupSpace hS (contains_trivialDoubleCover_total hS)).obj.X.hom :=
  SectionCoverData.isProper_groupSpace_hom hS _ _ inferInstance

/-- `(ℤ/2)_S = S ⊔ S ⟶ S` is flat, for any scheme `S` of the site. -/
theorem isFlat_trivialDoubleCover_groupSpace :
    Space.IsFlat 𝒞 S hS
      ((trivialDoubleCover S).groupSpace hS (contains_trivialDoubleCover_total hS)).obj.X.hom :=
  SectionCoverData.isFlat_groupSpace_hom hS _ _

/-- `(ℤ/2)_S = S ⊔ S ⟶ S` is locally of finite presentation, for any scheme `S` of the site. -/
theorem isLocallyOfFinitePresentation_trivialDoubleCover_groupSpace :
    Space.IsLocallyOfFinitePresentation 𝒞 S hS
      ((trivialDoubleCover S).groupSpace hS (contains_trivialDoubleCover_total hS)).obj.X.hom :=
  SectionCoverData.isLocallyOfFinitePresentation_groupSpace_hom hS _ _

/-- **The structure morphism `B(ℤ/2)_S ⟶ S` is quasi-compact** for `S` quasi-compact and
quasi-separated, in particular for `S` affine. -/
theorem isQuasiCompactMorphism_structureMorphism_classifyingStack_trivialDoubleCover
    [CompactSpace S] [QuasiSeparatedSpace S]
    (hG : Space.IsSmooth 𝒞 S hS
      ((trivialDoubleCover S).groupSpace hS (contains_trivialDoubleCover_total hS)).obj.X.hom) :
    Stack.IsQuasiCompactMorphism.{u, w} 𝒞 S hS
      (Stack.structureMorphism.{u, w} 𝒞 S hS (Stack.classifyingAlgebraicStack.{u, w} _ hG)) :=
  Stack.isQuasiCompactMorphism_structureMorphism_classifyingAlgebraicStack _ _

/-- **The structure morphism `B(ℤ/2)_S ⟶ S` is quasi-separated** for every scheme `S` of the
site, `(ℤ/2)_S ⟶ S` being proper, flat and locally of finite presentation. -/
theorem isQuasiSeparated_structureMorphism_classifyingStack_trivialDoubleCover
    (hG : Space.IsSmooth 𝒞 S hS
      ((trivialDoubleCover S).groupSpace hS (contains_trivialDoubleCover_total hS)).obj.X.hom) :
    Stack.AlgebraicStacks.IsQuasiSeparated 𝒞 S hS
      (Stack.structureMorphism.{u, w} 𝒞 S hS (Stack.classifyingAlgebraicStack.{u, w} _ hG)) :=
  Stack.isQuasiSeparated_structureMorphism_classifyingAlgebraicStack _ _
    (isProper_trivialDoubleCover_groupSpace hS) (isFlat_trivialDoubleCover_groupSpace hS)
    (isLocallyOfFinitePresentation_trivialDoubleCover_groupSpace hS)

end ConstantZModTwo

section AffineLine

variable {𝒞 : BigFppfSite.{u}} (k : Type u) [Field k]
  (hS : 𝒞.Contains (Spec (.of (Polynomial k))))

/-- **The structure morphism `B(ℤ/2)_S ⟶ S` over the affine line `S = Spec k[x]` is
quasi-compact**, `S` being affine. -/
theorem isQuasiCompactMorphism_structureMorphism_classifyingStack_constantZ2GroupSpace :
    Stack.IsQuasiCompactMorphism.{u, w} 𝒞 _ hS
      (Stack.structureMorphism.{u, w} 𝒞 _ hS
        (Stack.classifyingAlgebraicStack.{u, w} _ (isSmooth_constantZ2GroupSpace k hS))) :=
  Stack.isQuasiCompactMorphism_structureMorphism_classifyingAlgebraicStack _ _

/-- **The structure morphism `B(ℤ/2)_S ⟶ S` over the affine line `S = Spec k[x]` is
quasi-separated**, `(ℤ/2)_S ⟶ S` being proper, flat and locally of finite presentation. -/
theorem isQuasiSeparated_structureMorphism_classifyingStack_constantZ2GroupSpace :
    Stack.AlgebraicStacks.IsQuasiSeparated 𝒞 _ hS
      (Stack.structureMorphism.{u, w} 𝒞 _ hS
        (Stack.classifyingAlgebraicStack.{u, w} _ (isSmooth_constantZ2GroupSpace k hS))) :=
  Stack.isQuasiSeparated_structureMorphism_classifyingAlgebraicStack _ _
    (isProper_constantZ2GroupSpace k hS) (isFlat_constantZ2GroupSpace k hS)
    (isLocallyOfFinitePresentation_constantZ2GroupSpace k hS)

/-- There is a big fppf site containing the affine line `Spec k[x]` together with a big étale
site of the same size cutoff: the big étale site carried by the fppf site. -/
theorem exists_bigFppfSite_bigEtaleSite_contains :
    ∃ (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}), E.cutoff = B.cutoff ∧
      B.Contains (Spec (.of (Polynomial k))) := by
  obtain ⟨B, hB, -, -⟩ := exists_bigFppfSite_contains k
  exact ⟨B, B.toBigEtaleSite, BigFppfSite.toBigEtaleSite_cutoff B, hB⟩

end AffineLine

end Stacks.Examples

end
