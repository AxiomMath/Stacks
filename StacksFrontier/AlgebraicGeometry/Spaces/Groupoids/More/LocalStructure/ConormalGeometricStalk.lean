module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleChartKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk

/-!
# The geometric stalk of the conormal module of a first-order thickening

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `Z ⊆ X` be
a *first-order* thickening with inclusion `i : Z ⟶ X`, and let `x̄` be a geometric point of `X`.
Write `A = 𝒪_{X, x̄}` for the étale local ring at `x̄`.

This file identifies the geometric stalk at `x̄` of the conormal module `𝒞_{Z/X}`, read on `X` as
`i_*𝒞_{Z/X}`, with an ideal of `A` of square zero:

`(i_*𝒞_{Z/X})_{x̄} ≃ₗ[A] K ⊆ A`,  `K² = 0`.

The inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderIdeal.lean` is a monomorphism, so
it is injective on the stalk at every geometric point; composing with the identification of the
stalk of `𝒪_X` with the étale local ring
(`AlgebraicGeometry.Space.structureSheafGeometricStalkEquiv`) presents the stalk of the conormal
module as the submodule `K` of `A`, which is an ideal because `A` is the scalar ring.  That `K`
has square zero is the square-zero condition of
`AlgebraicGeometry.Space.IsFirstOrderThickening` read on one small étale neighbourhood: two
elements of `K` are germs of regular functions in the defining ideal of the thickening, and after
restriction to a common refinement — the small étale neighbourhoods of a geometric point being
cofiltered — their product is a section of the square of that ideal, which vanishes.

## Main definitions

* `AlgebraicGeometry.Space.ambientConormalModule`: the conormal module of a closed subspace read
  on the ambient space, `i_*i^*𝓘`; this is the source of
  `AlgebraicGeometry.Space.firstOrderConormalModuleι` and, by
  `AlgebraicGeometry.Space.modulePushforward_conormalModule_eq`, the direct image of
  `AlgebraicGeometry.Space.conormalModule`.
* `AlgebraicGeometry.Space.conormalGeometricStalkι`: the `𝒪_{X, x̄}`-linear map
  `(i_*𝒞_{Z/X})_{x̄} ⟶ 𝒪_{X, x̄}` obtained from the inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X` on the stalk at
  `x̄`.
* `AlgebraicGeometry.Space.conormalGeometricStalkIdeal`: **the ideal `K ⊆ A`**, the range of that
  map.
* `AlgebraicGeometry.Space.conormalGeometricStalkEquiv`: **the comparison**,
  `(i_*𝒞_{Z/X})_{x̄} ≃ₗ[A] K`.

## Main results

* `AlgebraicGeometry.Space.structureSheafGeometricStalkEquiv_geometricModuleStalkGerm`: the
  identification of the stalk of `𝒪_X` with the étale local ring carries the germ of a regular
  function to its germ.
* `AlgebraicGeometry.Space.mono_firstOrderConormalModuleι`: the inclusion
  `i_*𝒞_{Z/X} ⟶ 𝒪_X` is a monomorphism.
* `AlgebraicGeometry.Space.injective_conormalGeometricStalkι`: it stays injective on the stalk at
  a geometric point.
* `AlgebraicGeometry.Space.mem_conormalGeometricStalkIdeal_iff`: an element of `A` lies in `K`
  exactly when it is the germ of a regular function in the defining ideal of the thickening over
  some small étale neighbourhood.
* `AlgebraicGeometry.Space.conormalGeometricStalkIdeal_sq_eq_bot`: **`K² = 0`.**

## Implementation notes

**No `@[stacks]` attribute is placed.**  The identification of `𝒞_{Z/X}` with `𝓘/𝓘²` is
[Stacks Project, Tag 04CN], whose square-zero case the imported
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderIdeal.lean` proves while claiming
no tag for it, and the square-zero condition on the defining ideal is the definition
[Stacks Project, Tag 05ZK], part (2).  What is added here is the passage from the sections over a
chart to the germs at a geometric point, which is a reading of those statements and not a clause
of any tag — exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleChartKernel.lean`, which does the same for
the sections over one chart.

**Why the square-zero statement refines to one neighbourhood rather than restricting germs of
regular functions.**  Two elements of `K` are produced as germs over two different small étale
neighbourhoods, and their product has to be read over a single one.  The refinement is taken on
the *module* germs of `AlgebraicGeometry.Space.geometricModuleStalkGerm`, using
`AlgebraicGeometry.Space.geometricModuleStalkGerm_map`, and only then are the two conormal
sections pushed into the structure sheaf and their germs multiplied.  Restricting the regular
functions instead would need the compatibility of `AlgebraicGeometry.Space.etaleLocalRingGerm`
with restriction together with `AlgebraicGeometry.Space.definingIdealAt_map`, and would have to
cross between the two spellings of the structure sheaf of rings that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/StructureSheafGeometricStalk.lean` describe; taking the
refinement upstream avoids that.

**The monomorphism.**  `AlgebraicGeometry.Space.firstOrderConormalModuleι` is by construction the
inverse of an isomorphism followed by the inclusion of a submodule of `𝒪_X`, so it is a
monomorphism with no appeal to the chartwise injectivity
`AlgebraicGeometry.Space.injective_firstOrderConormalModuleι_app`; the latter is what identifies
the range over a chart and is used here through
`AlgebraicGeometry.Space.mem_range_firstOrderConormalModuleι_app_iff`.

## What is not proved

* **`A/K ≅ 𝒪_{Z, z̄}`.**  The quotient of `A` by `K` is the étale local ring of the thickening at
  the geometric point of `Z` above `x̄`.  Surjectivity of the homomorphism of étale local rings
  along a closed immersion is available
  (`AlgebraicGeometry.Space.surjective_etaleLocalRingMap_of_isClosedImmersion`), and a geometric
  point of `Z` above `x̄` exists by
  `AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_mem_range` together with surjectivity
  on points; what is missing is the identification of the *kernel* of that homomorphism with `K`,
  for which this development has no statement — not even a description of
  `AlgebraicGeometry.Space.etaleLocalRingMap` on germs.
* **The stalk form of [Stacks Project, Tag 0CKD].**  It is not proved here, and
  [Stacks Project, Tag 0CKF] does not need it: that tag is proved globally, without passing
  through the geometric points, as
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.unitVAddEquiv_add`.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Germs in the stalk of the structure sheaf -/

section StructureGerm

variable (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)

/-- **The comparison of the étale local ring with the stalk of `𝒪_X` carries a germ to a germ.**
The three steps of `AlgebraicGeometry.Space.etaleLocalRingToStructureSheafStalkAddEquiv` are
computed on the germ of a regular function over a small étale neighbourhood by
`AlgebraicGeometry.Space.pointStalkRingEquiv_germ_neighborhood`, by
`Stacks.unitModuleStalkLargeHom_germ`, and by
`AlgebraicGeometry.Space.geometricModuleStalkGerm_apply`. -/
theorem etaleLocalRingToStructureSheafStalkAddEquiv_etaleLocalRingGerm
    (N : SmallEtaleNeighborhood x)
    (a : (structurePresheaf B S hS X.1).obj (op N.chart)) :
    etaleLocalRingToStructureSheafStalkAddEquiv B S hS X x
        (etaleLocalRingGerm B S hS X.1 x (op N) a) =
      geometricModuleStalkGerm B S hS X x (structureSheafModule B S hS X) N a := by
  have h1 : (pointStalkRingEquiv B S hS X x).symm
        (etaleLocalRingGerm B S hS X.1 x (op N) a) =
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber N.chart ⟨N.point, N.point_comp⟩
        (smallEtaleRingedTopos B S hS X).O.obj a :=
    (RingEquiv.symm_apply_eq _).2 (pointStalkRingEquiv_germ_neighborhood B S hS X x N a).symm
  have h2 : (Stacks.unitModuleStalkLargeEquiv (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O).symm
        ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber N.chart ⟨N.point, N.point_comp⟩
          (smallEtaleRingedTopos B S hS X).O.obj a) =
      Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O (structureSheafModule B S hS X) N.chart
        ⟨N.point, N.point_comp⟩ a :=
    (LinearEquiv.symm_apply_eq _).2
      (Stacks.unitModuleStalkLargeHom_germ (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O N.chart ⟨N.point, N.point_comp⟩ a).symm
  refine Eq.trans (etaleLocalRingToStructureSheafStalkAddEquiv_apply B S hS X x _) ?_
  refine Eq.trans ?_ (geometricModuleStalkGerm_apply B S hS X x
    (structureSheafModule B S hS X) N a).symm
  exact congrArg (geometricModuleStalkAddEquiv B S hS X x (structureSheafModule B S hS X))
    ((congrArg (fun w => (Stacks.unitModuleStalkLargeEquiv (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).symm w) h1).trans h2)

/-- **The stalk of `𝒪_X` at a geometric point, read in the étale local ring, sends the germ of a
regular function to its germ.**  This pins
`AlgebraicGeometry.Space.structureSheafGeometricStalkEquiv` on the germs, which are jointly
surjective, and so determines it. -/
theorem structureSheafGeometricStalkEquiv_geometricModuleStalkGerm
    (N : SmallEtaleNeighborhood x)
    (a : (structurePresheaf B S hS X.1).obj (op N.chart)) :
    structureSheafGeometricStalkEquiv B S hS X x
        (geometricModuleStalkGerm B S hS X x (structureSheafModule B S hS X) N a) =
      etaleLocalRingGerm B S hS X.1 x (op N) a := by
  rw [← etaleLocalRingToStructureSheafStalkAddEquiv_etaleLocalRingGerm B S hS X x N a]
  show (etaleLocalRingToStructureSheafStalkAddEquiv B S hS X x).symm
      (etaleLocalRingToStructureSheafStalkAddEquiv B S hS X x
        (etaleLocalRingGerm B S hS X.1 x (op N) a)) = _
  exact (etaleLocalRingToStructureSheafStalkAddEquiv B S hS X x).symm_apply_apply _

end StructureGerm

/-! ### The conormal module of a closed subspace read on the ambient space -/

variable {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- The conormal module of a closed subspace, read on the ambient space: the inverse image of the
defining ideal sheaf along the inclusion, pushed forward again.  This is the source of
`AlgebraicGeometry.Space.firstOrderConormalModuleι`, and by
`AlgebraicGeometry.Space.modulePushforward_conormalModule_eq` it is the direct image of
`AlgebraicGeometry.Space.conormalModule`.  For a thickening the two small étale topoi are
equivalent, so reading the conormal module on the ambient space loses nothing. -/
abbrev ambientConormalModule : Modules.{u, u} B S hS X.1 X.2 :=
  (modulePullback B S hS (subspaceInclusion B S hS X Z) ⋙
      modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
    (definingIdealSheaf B S hS X Z).toSheafOfModules

/-! ### The stalk of the conormal module of a first-order thickening -/

section FirstOrder

variable (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- **The inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X` of the conormal module of a first-order thickening is a
monomorphism.**  It is by construction the inverse of
`AlgebraicGeometry.Space.submoduleUnitIsoOfEssImage` followed by the inclusion of the submodule
`AlgebraicGeometry.Space.definingIdealSheaf` of `𝒪_X`. -/
theorem mono_firstOrderConormalModuleι : Mono (firstOrderConormalModuleι B S hS Z hZ) := by
  have h : firstOrderConormalModuleι B S hS Z hZ =
      (submoduleUnitIsoOfEssImage B S hS (subspaceInclusion B S hS X Z) Z.2.2
            (definingIdealSheaf B S hS X Z)
            (essImage_modulePushforward_definingIdealSheaf_of_isFirstOrderThickening
              B S hS Z hZ)).inv ≫
        (definingIdealSheaf B S hS X Z).ι := rfl
  rw [h]
  have hmono : Mono ((definingIdealSheaf B S hS X Z).ι) := inferInstance
  exact mono_comp' (IsIso.mono_of_iso _) hmono

variable (x : GeometricPoint B S hS X.1)

/-- **The geometric stalk of the conormal module of a first-order thickening, inside the étale
local ring.**  The inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X` on the stalk at `x̄`, followed by the
identification `AlgebraicGeometry.Space.structureSheafGeometricStalkEquiv` of the stalk of `𝒪_X`
with `𝒪_{X, x̄}`. -/
def conormalGeometricStalkι :
    (geometricModuleStalk B S hS X x (ambientConormalModule B S hS Z) : Type (u + 1)) →ₗ[
        etaleLocalRing B S hS X.1 x] (etaleLocalRing B S hS X.1 x) :=
  (structureSheafGeometricStalkEquiv B S hS X x).toLinearMap.comp
    (geometricModuleStalkLinearMap B S hS X x (firstOrderConormalModuleι B S hS Z hZ))

/-- **The map of the stalk of the conormal module into the étale local ring is injective.**  The
inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X` is a monomorphism, hence injective on every geometric stalk by
[Stacks Project, Tag 04K5]. -/
theorem injective_conormalGeometricStalkι :
    Function.Injective (conormalGeometricStalkι B S hS Z hZ x) := by
  have hmono := mono_firstOrderConormalModuleι B S hS Z hZ
  intro a b hab
  exact injective_geometricModuleStalkMap_of_mono B S hS X x
    (firstOrderConormalModuleι B S hS Z hZ)
    ((structureSheafGeometricStalkEquiv B S hS X x).injective hab)

/-- **The ideal `K ⊆ A`**: the image in the étale local ring `A = 𝒪_{X, x̄}` of the geometric
stalk at `x̄` of the conormal module of a first-order thickening `Z ⊆ X`.  It is an ideal and not
merely a submodule because the scalar ring is `A` itself.

`AlgebraicGeometry.Space.conormalGeometricStalkEquiv` identifies it with that stalk, and
`AlgebraicGeometry.Space.conormalGeometricStalkIdeal_sq_eq_bot` shows it has square zero. -/
def conormalGeometricStalkIdeal : Ideal (etaleLocalRing B S hS X.1 x) :=
  LinearMap.range (conormalGeometricStalkι B S hS Z hZ x)

/-- Membership in `K` is being a value of the map out of the stalk; the defining equation of
`AlgebraicGeometry.Space.conormalGeometricStalkIdeal`. -/
theorem mem_conormalGeometricStalkIdeal_iff_exists (a : etaleLocalRing B S hS X.1 x) :
    a ∈ conormalGeometricStalkIdeal B S hS Z hZ x ↔
      ∃ z, conormalGeometricStalkι B S hS Z hZ x z = a :=
  LinearMap.mem_range

/-- **The comparison.**  The geometric stalk at `x̄` of the conormal module of a first-order
thickening `Z ⊆ X`, read on the ambient space, is the ideal `K` of the étale local ring
`A = 𝒪_{X, x̄}`.

With `X = U` the objects of a groupoid in algebraic spaces, `Z = U₀` an `R`-invariant first-order
thickening and `x̄ = ū` a geometric point, this is the identification `(𝒞_{U₀/U})_{ū} = K ⊆ A`
used by
`StacksFrontier/AlgebraicGeometry/Groupoids/More/LocalStructure/InfinitesimalSections.lean`. -/
def conormalGeometricStalkEquiv :
    (geometricModuleStalk B S hS X x (ambientConormalModule B S hS Z) : Type (u + 1)) ≃ₗ[
        etaleLocalRing B S hS X.1 x] (conormalGeometricStalkIdeal B S hS Z hZ x) :=
  LinearEquiv.ofInjective (conormalGeometricStalkι B S hS Z hZ x)
    (injective_conormalGeometricStalkι B S hS Z hZ x)

/-- **The map into the étale local ring on a germ.**  The germ of a section of the conormal module
over a small étale neighbourhood goes to the germ of the regular function it includes to. -/
theorem conormalGeometricStalkι_geometricModuleStalkGerm (N : SmallEtaleNeighborhood x)
    (c : (ambientConormalModule B S hS Z).val.obj (op N.chart)) :
    conormalGeometricStalkι B S hS Z hZ x
        (geometricModuleStalkGerm B S hS X x (ambientConormalModule B S hS Z) N c) =
      etaleLocalRingGerm B S hS X.1 x (op N)
        (((firstOrderConormalModuleι B S hS Z hZ).val.app (op N.chart)).hom c) :=
  (congrArg (structureSheafGeometricStalkEquiv B S hS X x)
    (geometricModuleStalkMap_germ B S hS X x (firstOrderConormalModuleι B S hS Z hZ) N c)).trans
    (structureSheafGeometricStalkEquiv_geometricModuleStalkGerm B S hS X x N _)

/-- The germ over `N` of a section of the conormal module goes to the germ over a refinement
`M ⟶ N` of the regular function its restriction to `M` includes to. -/
theorem conormalGeometricStalkι_geometricModuleStalkGerm_of_hom
    {M N : SmallEtaleNeighborhood x} (f : M ⟶ N)
    (c : (ambientConormalModule B S hS Z).val.obj (op N.chart)) :
    conormalGeometricStalkι B S hS Z hZ x
        (geometricModuleStalkGerm B S hS X x (ambientConormalModule B S hS Z) N c) =
      etaleLocalRingGerm B S hS X.1 x (op M)
        (((firstOrderConormalModuleι B S hS Z hZ).val.app (op M.chart)).hom
          ((ambientConormalModule B S hS Z).val.map f.hom.op c)) :=
  (congrArg (conormalGeometricStalkι B S hS Z hZ x)
      (geometricModuleStalkGerm_map B S hS X x (ambientConormalModule B S hS Z) f c).symm).trans
    (conormalGeometricStalkι_geometricModuleStalkGerm B S hS Z hZ x M _)

/-- A section of the conormal module over a chart includes into the defining ideal there. -/
private theorem firstOrderConormalModuleι_app_mem_definingIdealAt (N : SmallEtaleNeighborhood x)
    (c : (ambientConormalModule B S hS Z).val.obj (op N.chart)) :
    ((firstOrderConormalModuleι B S hS Z hZ).val.app (op N.chart)).hom c ∈
      definingIdealAt B S hS X Z (op N.chart) :=
  (mem_range_firstOrderConormalModuleι_app_iff B S hS Z hZ (op N.chart) _).1 ⟨c, rfl⟩

/-- **An element of `A` lies in `K` exactly when it is the germ of a regular function in the
defining ideal of the thickening.**  Germs in the stalk of the conormal module are jointly
surjective, and over one chart the range of the inclusion into `𝒪_X` is the defining ideal there
by `AlgebraicGeometry.Space.mem_range_firstOrderConormalModuleι_app_iff`. -/
theorem mem_conormalGeometricStalkIdeal_iff (a : etaleLocalRing B S hS X.1 x) :
    a ∈ conormalGeometricStalkIdeal B S hS Z hZ x ↔
      ∃ (N : SmallEtaleNeighborhood x) (y : (structureRingSheaf B S hS X).obj.obj (op N.chart)),
        y ∈ definingIdealAt B S hS X Z (op N.chart) ∧
          etaleLocalRingGerm B S hS X.1 x (op N) y = a := by
  rw [mem_conormalGeometricStalkIdeal_iff_exists]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨N, c, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x
      (ambientConormalModule B S hS Z) z
    refine ⟨N, ((firstOrderConormalModuleι B S hS Z hZ).val.app (op N.chart)).hom c,
      firstOrderConormalModuleι_app_mem_definingIdealAt B S hS Z hZ x N c,
      (conormalGeometricStalkι_geometricModuleStalkGerm B S hS Z hZ x N c).symm⟩
  · rintro ⟨N, y, hy, rfl⟩
    obtain ⟨c, hc⟩ := (mem_range_firstOrderConormalModuleι_app_iff B S hS Z hZ (op N.chart) y).2 hy
    exact ⟨geometricModuleStalkGerm B S hS X x (ambientConormalModule B S hS Z) N c,
      (conormalGeometricStalkι_geometricModuleStalkGerm B S hS Z hZ x N c).trans
        (congrArg (etaleLocalRingGerm B S hS X.1 x (op N)) hc)⟩

/-- **`K² = 0`.**  The ideal of the étale local ring cut out by the geometric stalk of the
conormal module of a *first-order* thickening has square zero.

Two of its elements are germs of sections of the conormal module over two small étale
neighbourhoods; the small étale neighbourhoods of a geometric point are cofiltered, so after
restriction to a common refinement both are germs over one neighbourhood `M`, where the regular
functions they include to lie in the defining ideal of the thickening at `M`.  The square of that
ideal vanishes, so the product of the two germs is the germ of `0`.

This is the hypothesis `hK : K ^ 2 = ⊥` of
`StacksFrontier/AlgebraicGeometry/Groupoids/More/LocalStructure/InfinitesimalSections.lean`. -/
theorem conormalGeometricStalkIdeal_sq_eq_bot :
    conormalGeometricStalkIdeal B S hS Z hZ x ^ 2 = ⊥ := by
  have hpow : ∀ U : (SmallEtale B S hS X.1)ᵒᵖ,
      definingIdealAt B S hS X Z U * definingIdealAt B S hS X Z U = ⊥ := by
    obtain ⟨_, hp⟩ := id hZ
    intro U
    have hU := hp U.unop
    rwa [Submodule.pow_succ, Submodule.pow_one] at hU
  have hcof : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  refine le_antisymm ?_ bot_le
  rw [pow_two]
  refine Ideal.mul_le.2 fun r hr s hs => ?_
  obtain ⟨z₁, rfl⟩ := (mem_conormalGeometricStalkIdeal_iff_exists B S hS Z hZ x r).1 hr
  obtain ⟨z₂, rfl⟩ := (mem_conormalGeometricStalkIdeal_iff_exists B S hS Z hZ x s).1 hs
  obtain ⟨N₁, c₁, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x
    (ambientConormalModule B S hS Z) z₁
  obtain ⟨N₂, c₂, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x
    (ambientConormalModule B S hS Z) z₂
  obtain ⟨M, f, g, -⟩ := IsCofilteredOrEmpty.cone_objs N₁ N₂
  refine Ideal.mem_bot.2 ?_
  rw [conormalGeometricStalkι_geometricModuleStalkGerm_of_hom B S hS Z hZ x f c₁,
    conormalGeometricStalkι_geometricModuleStalkGerm_of_hom B S hS Z hZ x g c₂]
  refine ((map_mul (etaleLocalRingGerm B S hS X.1 x (op M)) _ _).symm.trans
    (congrArg (etaleLocalRingGerm B S hS X.1 x (op M)) ?_)).trans (map_zero _)
  exact (Submodule.eq_bot_iff _).1 (hpow (op M.chart)) _ (Ideal.mul_mem_mul
    (firstOrderConormalModuleι_app_mem_definingIdealAt B S hS Z hZ x M _)
    (firstOrderConormalModuleι_app_mem_definingIdealAt B S hS Z hZ x M _))

end FirstOrder

end AlgebraicGeometry.Space

end
