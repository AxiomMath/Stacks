module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.LocalStructure.ConormalGeometricStalk

/-!
# The kernel of the map of étale local rings along a closed immersion

Let `i : W ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `z̄` be a geometric point of `W` and let `x̄ = i(z̄)` be its image.  Write
`A = 𝒪_{X, x̄}` for the étale local ring of the ambient space.

This file computes the kernel of the homomorphism of étale local rings
`A = 𝒪_{X, x̄} ⟶ 𝒪_{W, z̄}` of [Stacks Project, Tag 04NG]: it consists of the germs of those
regular functions which vanish after pullback to the base-changed chart, that is, of the germs
of the sections of the defining ideal of `W`.  Together with the germ description
`AlgebraicGeometry.Space.mem_conormalGeometricStalkIdeal_iff` of the ideal `K ⊆ A` cut out by
the geometric stalk of the conormal module of a *first-order* thickening, this identifies `K`
with that kernel, and with surjectivity along a closed immersion
(`AlgebraicGeometry.Space.surjective_etaleLocalRingMap_of_isClosedImmersion`) it gives

`A / K ≅ 𝒪_{W, z̄}`.

## Main results

* `AlgebraicGeometry.Space.mem_ker_etaleLocalRingMap_iff`: an element of `A` is killed by the
  map to `𝒪_{W, z̄}` exactly when it is the germ of a regular function whose pullback to the
  base-changed chart vanishes.
* `AlgebraicGeometry.Space.mem_ker_etaleLocalRingMap_iff_mem_definingIdealAt`: the same statement
  with the vanishing condition read as membership in
  `AlgebraicGeometry.Space.definingIdealAt`, for a closed subspace.
* `AlgebraicGeometry.Space.ker_etaleLocalRingMap_eq_conormalGeometricStalkIdeal`: for a
  first-order thickening the kernel is the ideal `K` of
  `AlgebraicGeometry.Space.conormalGeometricStalkIdeal`.
* `AlgebraicGeometry.Space.quotientConormalGeometricStalkIdealEquiv`: **`A / K ≅ 𝒪_{W, z̄}`.**

## Implementation notes

Both inclusions run through `AlgebraicGeometry.Space.etaleLocalRingGerm_baseChange`, which says
that the germ at `z̄` over the base-changed chart `W ×_X N` of the pullback of a regular function
on `N` is the image of its germ at `x̄`.  The inclusion of the ideal of germs into the kernel is
then immediate.

For the reverse inclusion an element of the kernel is written as a germ over some small étale
neighbourhood `N` of `x̄`; its pullback to `W ×_X N` then has vanishing germ at `z̄`, so it
already vanishes over some refinement `M ⟶ W ×_X N` of pointed charts of `W`, the small étale
neighbourhoods of a geometric point being cofiltered and the étale local ring the filtered
colimit of their sections.  That refinement has to be replaced by one of the form `W ×_X V` with
`V ⟶ N` a morphism of pointed charts of `X`, which is what cover density and local fullness of
base change along a closed immersion provide, in the pointed form
`AlgebraicGeometry.Space.SmallEtaleNeighborhood.exists_baseChange_hom` and
`AlgebraicGeometry.Space.SmallEtaleNeighborhood.exists_baseChange_factorization`; the restriction
of the function to `V` is then the required section.  Taking an arbitrary refinement and
intersecting charts later on does not work: two composites of chart morphisms into `N` need not
agree, and it is the factorization statement that produces the single morphism making them agree.

The closed immersion and the geometric point are kept as variables rather than extracted from a
`AlgebraicGeometry.Space.ClosedSubspaces` inside the proof.  Introducing them with `set` instead
makes the elaboration of the base-changed pointed chart inside a germ run into a `whnf`
heartbeat timeout, the hazard the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/StructureSheafGeometricStalk.lean` describe.

**No `@[stacks]` attribute is placed.**  The surjectivity half of the comparison carries the tag
of [Stacks Project, Tag 04NG] where it is proved; the kernel computation is a reading of the
defining ideal at a geometric point and is not a clause of any tag, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/LocalStructure/ConormalGeometricStalk.lean`.

## References

* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W X : AlgebraicSpaces B S hS}

private theorem Γ_toScheme_comp {T₁ T₂ T₃ : BigFppfOver B S hS} (g : T₁ ⟶ T₂)
    (h : T₂ ⟶ T₃) (c : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T₃))) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (g ≫ h)).op).hom c =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h).op).hom c) := by
  rw [Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp]
  rfl

/-- An element of the kernel of the map of étale local rings along a closed immersion is the germ
of a regular function whose pullback to the base-changed chart vanishes. -/
theorem exists_germ_of_mem_ker_etaleLocalRingMap (i : W ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (z : GeometricPoint B S hS W.1)
    (a : etaleLocalRing B S hS X.1 (geometricPointMap i.hom z))
    (ha : a ∈ RingHom.ker (etaleLocalRingMap W.2 i.hom z)) :
    ∃ (N : SmallEtaleNeighborhood (geometricPointMap i.hom z))
      (y : (structurePresheaf B S hS X.1).obj (op N.chart)),
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hi.rep.snd N.chart.1.hom)).op).hom y = 0
        ∧ etaleLocalRingGerm B S hS X.1 (geometricPointMap i.hom z) (op N) y = a := by
  classical
  obtain ⟨N, f, hNf⟩ :=
    (spaceGerms_isColimit (x := geometricPointMap i.hom z) X.2).ι_jointly_surjective a
  have hNf' : etaleLocalRingGerm B S hS X.1 (geometricPointMap i.hom z) N f = a := hNf
  have hzero : etaleLocalRingGerm B S hS W.1 z
      (op ((SmallEtaleNeighborhood.baseChange B S hS i hi.rep z).obj N.unop))
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (hi.rep.snd N.unop.chart.1.hom)).op).hom f) =
      etaleLocalRingGerm B S hS W.1 z
        (op ((SmallEtaleNeighborhood.baseChange B S hS i hi.rep z).obj N.unop)) 0 :=
    (etaleLocalRingGerm_baseChange B S hS i hi z N.unop f).trans
      ((congrArg (etaleLocalRingMap W.2 i.hom z) hNf').trans
        ((RingHom.mem_ker.1 ha).trans (map_zero _).symm))
  have : IsCofiltered (SmallEtaleNeighborhood z) :=
    isCofiltered_smallEtaleNeighborhood B S hS W.1 W.2 z
  obtain ⟨M, ψ, hψ⟩ :=
    (Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered'
      (CommRingCat.coconeTypesOfRingHoms (spaceSections (x := z))
        (etaleLocalRingGerm B S hS W.1 z) (fun k ↦ spaceGerm_naturality k))).mp
      (spaceGerms_isColimit (x := z) W.2).bijective.1
      (op ((SmallEtaleNeighborhood.baseChange B S hS i hi.rep z).obj N.unop)) _ 0 hzero
  obtain ⟨V₀, ⟨k⟩⟩ := SmallEtaleNeighborhood.exists_baseChange_hom B S hS i hi z M.unop
  obtain ⟨V, α, β, hαβ⟩ := SmallEtaleNeighborhood.exists_baseChange_factorization
    B S hS i hi z V₀ N.unop (k ≫ ψ.unop)
  refine ⟨V, (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map β.hom)).op).hom f, ?_,
    (DFunLike.congr_fun (etaleLocalRingGerm_comp_map B S hS β) f).trans hNf'⟩
  have hψ0 : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ψ.unop.hom.hom.left).op).hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (hi.rep.snd N.unop.chart.1.hom)).op).hom f) = 0 := by
    change ((spaceSections (x := z)).map ψ).hom _ =
      ((spaceSections (x := z)).map ψ).hom 0 at hψ
    rwa [map_zero] at hψ
  have hbc : ((smallBaseChange B S hS i hi.rep).map β.hom).hom.left =
      ((smallBaseChange B S hS i hi.rep).map α.hom).hom.left ≫
        k.hom.hom.left ≫ ψ.unop.hom.hom.left :=
    congrArg (fun m : (SmallEtaleNeighborhood.baseChange B S hS i hi.rep z).obj V ⟶
        (SmallEtaleNeighborhood.baseChange B S hS i hi.rep z).obj N.unop =>
      m.hom.hom.left) hαβ.symm
  refine Eq.trans
    ((Γ_toScheme_comp B S hS (hi.rep.snd V.chart.1.hom) β.hom.hom.left f).symm.trans
      (congrArg (fun m => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op).hom f)
        (smallBaseChange_map_snd B S hS i hi.rep β.hom).symm)) ?_
  refine (Γ_toScheme_comp B S hS ((smallBaseChange B S hS i hi.rep).map β.hom).hom.left
    (hi.rep.snd N.unop.chart.1.hom) f).trans ?_
  refine (congrArg (fun m => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op).hom
    ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (hi.rep.snd N.unop.chart.1.hom)).op).hom f)) hbc).trans ?_
  refine (Γ_toScheme_comp B S hS ((smallBaseChange B S hS i hi.rep).map α.hom).hom.left
    (k.hom.hom.left ≫ ψ.unop.hom.hom.left) _).trans ?_
  refine Eq.trans (congrArg (fun c => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    ((smallBaseChange B S hS i hi.rep).map α.hom).hom.left).op).hom c)
    ((Γ_toScheme_comp B S hS k.hom.hom.left ψ.unop.hom.hom.left _).trans
      ((congrArg (fun c => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        k.hom.hom.left).op).hom c) hψ0).trans (map_zero _)))) (map_zero _)

/-- **The kernel of the map of étale local rings along a closed immersion.**  An element of
`A = 𝒪_{X, x̄}` is killed by the homomorphism of [Stacks Project, Tag 04NG] to `𝒪_{W, z̄}`
exactly when it is the germ of a regular function over some small étale neighbourhood `N` of
`x̄` whose pullback to the base-changed chart `W ×_X N` vanishes. -/
theorem mem_ker_etaleLocalRingMap_iff (i : W ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (z : GeometricPoint B S hS W.1) (a : etaleLocalRing B S hS X.1 (geometricPointMap i.hom z)) :
    a ∈ RingHom.ker (etaleLocalRingMap W.2 i.hom z) ↔
      ∃ (N : SmallEtaleNeighborhood (geometricPointMap i.hom z))
        (y : (structurePresheaf B S hS X.1).obj (op N.chart)),
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hi.rep.snd N.chart.1.hom)).op).hom y = 0
          ∧ etaleLocalRingGerm B S hS X.1 (geometricPointMap i.hom z) (op N) y = a := by
  refine ⟨exists_germ_of_mem_ker_etaleLocalRingMap B S hS i hi z a, ?_⟩
  rintro ⟨N, y, hy, rfl⟩
  exact RingHom.mem_ker.2 ((etaleLocalRingGerm_baseChange B S hS i hi z N y).symm.trans
    ((congrArg (etaleLocalRingGerm B S hS W.1 z
      (op ((SmallEtaleNeighborhood.baseChange B S hS i hi.rep z).obj N))) hy).trans (map_zero _)))

/-- **The kernel of the map of étale local rings along the inclusion of a closed subspace.**  An
element of `A = 𝒪_{X, x̄}` is killed by the homomorphism to `𝒪_{Z, z̄}` exactly when it is the
germ of a regular function lying in the defining ideal of `Z` over some small étale
neighbourhood of `x̄`.

This is `AlgebraicGeometry.Space.mem_ker_etaleLocalRingMap_iff` with the vanishing of the
pullback to the base-changed chart read as membership in
`AlgebraicGeometry.Space.definingIdealAt`, which is
`AlgebraicGeometry.Space.definingIdealAt_eq_ker`. -/
theorem mem_ker_etaleLocalRingMap_iff_mem_definingIdealAt
    (Z : ClosedSubspaces B S hS X.1)
    (z : GeometricPoint B S hS (closedSubspaceToSpace B S hS X Z).1)
    (a : etaleLocalRing B S hS X.1
      (geometricPointMap (closedSubspaceInclusion B S hS X Z).hom z)) :
    a ∈ RingHom.ker (etaleLocalRingMap (closedSubspaceToSpace B S hS X Z).2
        (closedSubspaceInclusion B S hS X Z).hom z) ↔
      ∃ (N : SmallEtaleNeighborhood
          (geometricPointMap (closedSubspaceInclusion B S hS X Z).hom z))
        (y : (structurePresheaf B S hS X.1).obj (op N.chart)),
        y ∈ definingIdealAt B S hS X Z (op N.chart) ∧
          etaleLocalRingGerm B S hS X.1
            (geometricPointMap (closedSubspaceInclusion B S hS X Z).hom z) (op N) y = a := by
  refine (mem_ker_etaleLocalRingMap_iff B S hS (closedSubspaceInclusion B S hS X Z) Z.2.2
    z a).trans (exists_congr fun N => exists_congr fun y => and_congr_left' ?_)
  exact ⟨fun h => (definingIdealAt_eq_ker B S hS X Z N.chart).ge (RingHom.mem_ker.2 h),
    fun h => RingHom.mem_ker.1 ((definingIdealAt_eq_ker B S hS X Z N.chart).le h)⟩

/-- **The ideal `K` is the kernel.**  For a first-order thickening `Z ⊆ X` the ideal `K ⊆ A` cut
out by the geometric stalk of the conormal module is exactly the kernel of the homomorphism of
étale local rings `A = 𝒪_{X, x̄} ⟶ 𝒪_{Z, z̄}` of [Stacks Project, Tag 04NG].

Both sides are described by the same germs:
`AlgebraicGeometry.Space.mem_conormalGeometricStalkIdeal_iff` for `K` and
`AlgebraicGeometry.Space.mem_ker_etaleLocalRingMap_iff_mem_definingIdealAt` for the kernel. -/
theorem ker_etaleLocalRingMap_eq_conormalGeometricStalkIdeal
    (Z : ClosedSubspaces B S hS X.1) (hZ : IsFirstOrderThickening B S hS X Z.1)
    (z : GeometricPoint B S hS (closedSubspaceToSpace B S hS X Z).1) :
    RingHom.ker (etaleLocalRingMap (closedSubspaceToSpace B S hS X Z).2
        (closedSubspaceInclusion B S hS X Z).hom z) =
      conormalGeometricStalkIdeal B S hS Z hZ
        (geometricPointMap (closedSubspaceInclusion B S hS X Z).hom z) :=
  Ideal.ext fun a =>
    (mem_ker_etaleLocalRingMap_iff_mem_definingIdealAt B S hS Z z a).trans
      (mem_conormalGeometricStalkIdeal_iff B S hS Z hZ _ a).symm

/-- **`A / K ≅ 𝒪_{Z, z̄}`.**  For a first-order thickening `Z ⊆ X` with geometric point `z̄` above
`x̄`, the quotient of the étale local ring `A = 𝒪_{X, x̄}` by the ideal `K` cut out by the
geometric stalk of the conormal module is the étale local ring of `Z` at `z̄`.

The homomorphism of étale local rings along a closed immersion is surjective by
`AlgebraicGeometry.Space.surjective_etaleLocalRingMap_of_isClosedImmersion`, and its kernel is
`K` by `AlgebraicGeometry.Space.ker_etaleLocalRingMap_eq_conormalGeometricStalkIdeal`. -/
def quotientConormalGeometricStalkIdealEquiv
    (Z : ClosedSubspaces B S hS X.1) (hZ : IsFirstOrderThickening B S hS X Z.1)
    (z : GeometricPoint B S hS (closedSubspaceToSpace B S hS X Z).1) :
    (etaleLocalRing B S hS X.1
          (geometricPointMap (closedSubspaceInclusion B S hS X Z).hom z) ⧸
        conormalGeometricStalkIdeal B S hS Z hZ
          (geometricPointMap (closedSubspaceInclusion B S hS X Z).hom z)) ≃+*
      etaleLocalRing B S hS (closedSubspaceToSpace B S hS X Z).1 z :=
  (Ideal.quotEquivOfEq
        (ker_etaleLocalRingMap_eq_conormalGeometricStalkIdeal B S hS Z hZ z).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (surjective_etaleLocalRingMap_of_isClosedImmersion B S hS
        (closedSubspaceInclusion B S hS X Z) Z.2.2 z))

end AlgebraicGeometry.Space

end
