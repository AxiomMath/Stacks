module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SingletonFibreGeometricPoint

/-!
# A vanishing germ, and shrinking the base until the section itself vanishes

Two steps of the injectivity half of Stacks 0F6P are isolated here.

The first is the exact criterion for a germ at a geometric point to vanish: not merely that the
section restricts to zero on *some* étale neighbourhood of the lift, which is the general
description of a stalk as a filtered colimit and is already available as
`AlgebraicGeometry.SmallEtale.etaleGerm_eq_zero_iff`, but that the lift lands in the maximal
Zariski open zero locus of the section. That equivalence is **Stacks 04FR part (3)**: for a
geometric point `ū` of `U` and `s̄ = (U → S) ∘ ū`, the triple `(U, ū, σ)` is zero in `F_s̄`
exactly when `ū` lies in the open `W` of part (1). The two criteria agree because vanishing after
an arbitrary arrow of the small étale site is detected by the image of that arrow, which is
Stacks 04FR part (2). This is the form in which a vanishing germ is usable, because it locates the
obstruction as a *closed subset of the object itself*.

The second is the consequence: if the support lives on an open of a base change `X_V` which is
finite over `V`, then the closed complement of the zero locus has closed image in `V`, and
discarding that image from `V` leaves an open neighbourhood of the chosen point of `V` over which
the section vanishes outright. In the source this is the closing move of the injectivity argument,
"shrinking `V` once more gives `t_j = 0`".

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.SmallEtale.etaleGerm_eq_zero_iff_mem_zeroOpen` — Stacks 04FR part (3): a germ
  vanishes exactly when the lift lands in the maximal open zero locus.
* `AlgebraicGeometry.SmallEtale.exists_opens_map_openObjectι_eq_zero` — shrinking the base of an
  open support finite over it until the section vanishes.

## Implementation notes

The shrinking statement is phrased with the smaller open taken inside the support itself, as the
preimage of an open of `V` under the structure morphism of the support, rather than as an open of a
base change of `X_V` along a shrinking of `V`. Both describe the same subscheme, but the former
needs no identification of `X_{V'}` with an open of `X_V` and no transport of the section along
such an identification: everything stays inside the one object `openObject (baseChange f V) O` of
the small étale site of `X`.

Finiteness of the support over `V` enters only through
`AlgebraicGeometry.exists_opens_preimage_subset_of_isFinite`, i.e. only through the structure
morphism being a closed map.

## References

* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
* [Stacks Project, Tag 04FR](https://stacks.math.columbia.edu/tag/04FR)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section Germ

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (t : GeometricPoint S)
  [UnivLE.{u, v}] (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
  [HasColimit (etaleStalkDiagram B S hS t F.obj)]

/-- **Stacks 04FR, part (3).** A germ vanishes exactly when the lift lands in the maximal open
zero locus of the section.

A geometric point `ū` of the object `W` of the small étale site is a lift `q` to `W` of a geometric
point `t` of `S`, the relation `t = (W → S) ∘ ū` of the source being the defining condition on a
lift; so quantifying over `t` and over `q` is quantifying over the geometric points of `W`. The
germ `etaleGerm … t F.obj W q a` is the source's class of `(U, ū, σ)` in `F_s̄`, and
`zeroOpen … W a` is the source's `W`, so this is the asserted equivalence
`(U, ū, σ) = 0 in F_s̄ ↔ ū ∈ W`.

The coefficient universe `v` is free, which is more general than the source; `UnivLE.{u, v}` and
the existence of the colimit are what that extra generality costs, and both are automatic
instances at `v = u`, so at the source's generality the statement carries no hypothesis. They are
size conditions for the stalk to be formed at all, not mathematical hypotheses: `etaleGerm` is a
colimit injection and does not typecheck without the colimit. -/
@[stacks 04FR "part (3): a germ vanishes exactly when the lift lands in the zero locus"]
public theorem etaleGerm_eq_zero_iff_mem_zeroOpen (W : SmallEtale B S hS)
    (q : (geometricPointFiber B S hS t).obj W) (a : F.obj.obj (op W)) :
    etaleGerm B S hS t F.obj W q a = 0 ↔
      q.1.base default ∈
        (zeroOpen B S hS F W a : Set ((SmallEtale.toScheme B S hS).obj W)) := by
  refine ⟨fun h => ?_, fun h => etaleGerm_eq_zero_of_notMem_supportSection B S hS t F W q a
    (by simpa only [supportSection, Set.mem_compl_iff, not_not] using h)⟩
  obtain ⟨W', j, q', hq, hzero⟩ := (etaleGerm_eq_zero_iff B S hS t F.obj W q a).1 h
  have hq₁ : q'.1 ≫ (SmallEtale.toScheme B S hS).map j = q.1 := congrArg Subtype.val hq
  exact (map_eq_zero_iff_range_subset_zeroOpen B S hS F W a W' j).1 hzero
    ⟨q'.1.base default, congrArg (fun m => m.base (default : ↥t.source)) hq₁⟩

end Germ

section Shrink

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})

/-- **Shrinking the base until a section over an open support vanishes.** Let `O` be an open of a
base change `X_V` whose structure morphism to `V` is finite, and let `b` be a section of `F` over
it whose zero locus contains the whole fibre of `O` over a point `v` of `V`. Then an open
neighbourhood of `v` in `V` has `b` vanishing on the part of `O` lying over it.

The complement of the zero locus is closed in `O`, so its image in `V` is closed and misses `v`;
discarding that image is the required shrinking, and vanishing on the preimage is Stacks 04FR
part (2). -/
public theorem exists_opens_map_openObjectι_eq_zero (V : SmallEtale B Y.obj Y.property)
    (O : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)).Opens)
    (hfin : IsFinite (O.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f)))
    (b : F.obj.obj (op (openObject B X.obj X.property (baseChange B f V) O)))
    (v : (SmallEtale.toScheme B Y.obj Y.property).obj V)
    (hfib : (O.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f)).base ⁻¹' {v} ⊆
      (zeroOpen B X.obj X.property F
        (openObject B X.obj X.property (baseChange B f V) O) b :
          Set ((SmallEtale.toScheme B X.obj X.property).obj
            (openObject B X.obj X.property (baseChange B f V) O)))) :
    ∃ V' : ((SmallEtale.toScheme B Y.obj Y.property).obj V).Opens, v ∈ V' ∧
      F.obj.map (openObjectι B X.obj X.property
        (openObject B X.obj X.property (baseChange B f V) O)
        ((O.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f)) ⁻¹ᵁ V')).op b = 0 := by
  have := hfin
  obtain ⟨V', hvV', hsub⟩ := exists_opens_preimage_subset_of_isFinite
    (O.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f))
    (zeroOpen B X.obj X.property F
      (openObject B X.obj X.property (baseChange B f V) O) b) v hfib
  refine ⟨V', hvV', ?_⟩
  refine (map_eq_zero_iff_range_subset_zeroOpen B X.obj X.property F
    (openObject B X.obj X.property (baseChange B f V) O) b _
    (openObjectι B X.obj X.property
      (openObject B X.obj X.property (baseChange B f V) O)
      ((O.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f)) ⁻¹ᵁ V'))).2 ?_
  rwa [openObjectι_range]

end Shrink

end AlgebraicGeometry.SmallEtale

end
