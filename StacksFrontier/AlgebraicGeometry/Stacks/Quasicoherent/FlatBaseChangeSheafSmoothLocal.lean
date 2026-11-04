module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent

/-!
# The flat base change property of étale sheaves is smooth local (Stacks 0764, part (3))

Let `𝒳` be an algebraic stack over `S`, `F` an étale sheaf of `𝒪_𝒳`-modules, and
`f j : 𝒵 j ⟶ 𝒳` a family of smooth 1-morphisms of algebraic stacks with
`|𝒳| = ⋃ j, |f j|(|𝒵 j|)`. **Stacks 0764** part (3) says that if every inverse image `f j^* F` has
the flat base change property of **Stacks 0762**, then so does `F`. This file proves it in the
source's ambient category `Mod(𝒳_étale, 𝒪_𝒳)`: the property is
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheafUnivLE` and the inverse image is
`AlgebraicGeometry.Stack.modulePullback`.

The source's proof first reduces, by part (1), to members representable by schemes; then for an
arrow `φ : x ⟶ x'` over a flat morphism `U ⟶ U'` it takes an étale covering `{U'_i ⟶ U'}` over
whose members `x'` comes from some member of the family (**Stacks 06XH**), base-changes it to
`U`, and concludes from the comparison maps over the members, which are restrictions of `c_φ`
(**Stacks 075D**) and comparison maps of the inverse images. The étale covering is supplied here
by `AlgebraicGeometry.Stack.exists_etaleCovering_family_fibre_lift`, which already produces the
lifts through the members of the family, so no reduction to schemes is needed; the remaining
argument is the étale-local criterion
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_etaleLocal`, which is stated for an
arbitrary family of 1-morphisms so that it also serves the localizations used for part (6).

## Main results

* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_etaleLocal`: if every object of `𝒳`
  is covered, étale locally on the scheme below it, by images of objects of members of a family
  of 1-morphisms `g i : 𝒳ᵢ i ⥤ 𝒳`, and every inverse image `g i^* F` has the flat base change
  property, then `F` has it.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_isSmooth_jointlySurjective`:
  **Stacks 0764** part (3).

## Implementation notes

The 1-morphisms are presented strictly, as in **Stacks 06WE** and **Stacks 075Y**: the structure
functor of the source of `g i` is `g i ⋙ p`. Joint surjectivity is expressed with the points of
**Stacks 04XG** as `Set.univ = ⋃ j, Set.range (|f j|)`, as for **Stacks 075Y**.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w v' w' t m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **The flat base change property of an étale sheaf of modules is étale local.** Let
`g i : 𝒳ᵢ i ⥤ 𝒳` be a family of 1-morphisms of categories fibred in groupoids, presented
strictly, such that every object `y` of `𝒳` receives arrows `e j : g (a j) (z j) ⟶ y` lying over
étale morphisms of schemes which are jointly surjective onto the scheme below `y`. If every
inverse image `g i^* F` has the flat base change property, then so does `F`.

At an arrow `φ` lying over a flat morphism this is
`AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_of_etaleCover_of_lift` along the
arrows `e j`: a flat morphism into the scheme below `g (a j) (z j)` lifts to an arrow `ψ` of
`𝒳ᵢ (a j)`, and the comparison map of `F` at `g ψ` is the comparison map of `g^* F` at `ψ`, by
`AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_modulePullback_iff`. -/
theorem hasFlatBaseChangePropertySheaf_of_etaleLocal [UnivLE.{u, m}] {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {ι : Type*}
    {𝒳ᵢ : ι → Type v'} [∀ i, Category.{w'} (𝒳ᵢ i)] (g : ∀ i, 𝒳ᵢ i ⥤ 𝒳)
    (hg : ∀ i, (g i ⋙ p).IsFiberedInGroupoids)
    (hcov : ∀ y : 𝒳, ∃ (I : Type t) (a : I → ι) (z : ∀ j, 𝒳ᵢ (a j))
      (e : ∀ j, (g (a j)).obj (z j) ⟶ y),
      (∀ j, Etale (B.inclusion.map (p.map (e j)).left)) ∧
        ∀ s : B.inclusion.obj (p.obj y).left,
          ∃ j, s ∈ Set.range (B.inclusion.map (p.map (e j)).left))
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hF : ∀ i, HasFlatBaseChangePropertySheafUnivLE B E h S hS (g i ⋙ p) (hg i)
      ((modulePullback B S hS (g i ⋙ p) p (hg i) hp (g i) rfl (etaleTopology B)
        (etaleTopology_le_topology B)).obj F)) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp F := by
  intro x y φ hφ
  obtain ⟨I, a, z, e, het, hcv⟩ := hcov y
  refine isIso_restrictSheafPullbackComparison_of_etaleCover_of_lift B E h S hS p hp φ hφ e
    het hcv F fun j V k hk => ?_
  obtain ⟨w, ψ, hψ⟩ := (hg (a j)).exists_lift k (z j) rfl
  have := hψ
  have : MorphismProperty.RespectsIso @Flat :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Flat)
  have hψ' : p.IsHomLift k ((g (a j)).map ψ) :=
    IsHomLift.of_fac' p k _ (IsHomLift.domain_eq (g (a j) ⋙ p) k ψ)
      (IsHomLift.codomain_eq (g (a j) ⋙ p) k ψ)
      (IsHomLift.fac' (g (a j) ⋙ p) k ψ)
  refine ⟨_, (g (a j)).map ψ, hψ', ?_⟩
  exact (isIso_restrictSheafPullbackComparison_modulePullback_iff B E h S hS (g (a j) ⋙ p) p
    (hg (a j)) hp (g (a j)) rfl F ψ).mp
    (hF (a j) ψ (map_left_of_isHomLift B S hS (g (a j) ⋙ p) (P := @Flat) k hk ψ))

/-- **Stacks 0764, part (3), in the source's ambient category.** Let `f j : 𝒵 j ⟶ 𝒳` be a family
of smooth 1-morphisms of algebraic stacks over `S` with `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be
an étale sheaf of `𝒪_𝒳`-modules. If every inverse image `f j^* F` of sheaves of modules has the
flat base change property of **Stacks 0762**, then so does `F`.

`AlgebraicGeometry.Stack.exists_etaleCovering_family_fibre_lift` covers the scheme below any
object of `𝒳` by étale morphisms over which the object lifts through some `f j`, and
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_etaleLocal` concludes. -/
@[stacks 0764 "part (3), the whole part, in the source's ambient category of étale sheaves of \
  modules (a_small^* the inverse image of sheaves of modules): for a family of smooth \
  1-morphisms f j : 𝒵 j ⟶ 𝒳 of algebraic stacks with |𝒳| = ⋃ j, |f j|(|𝒵 j|), if each inverse \
  image f j^* F has the flat base change property then so does F"]
theorem hasFlatBaseChangePropertySheaf_of_isSmooth_jointlySurjective [UnivLE.{u, m}]
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)))
    (hF : ∀ j, HasFlatBaseChangePropertySheafUnivLE B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((modulePullback B S hS (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
        𝒳.val.val.p (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
        𝒳.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor (f j).hom) rfl
        (etaleTopology B) (etaleTopology_le_topology B)).obj F)) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F := by
  classical
  refine hasFlatBaseChangePropertySheaf_of_etaleLocal B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (fun j => CatFiberedInGroupoids.homFunctor (f j).hom)
    (fun j => isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom) (fun y => ?_) F hF
  obtain ⟨I, W, e, a, hetale, hcov, hlift⟩ :=
    exists_etaleCovering_family_fibre_lift B S hS f hsmooth hjs
      (𝒳.val.val.p.obj y) (Functor.Fiber.mk rfl)
  choose zz αα hαα using hlift
  refine ⟨I, a, zz, αα, fun i => etale_map_left_of_isHomLift B S hS 𝒳.val.val.p _ (hetale i)
    (αα i) (hαα i), fun s => ?_⟩
  obtain ⟨i, hi⟩ := hcov s
  exact ⟨i, range_map_left_of_isHomLift B S hS 𝒳.val.val.p (αα i) (hαα i) hi⟩

end AlgebraicGeometry.Stack

end
