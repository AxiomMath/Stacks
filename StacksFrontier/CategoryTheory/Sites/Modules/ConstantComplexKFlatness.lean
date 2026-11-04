module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfAConstantComplex

/-!
# The complex of constant sheaves on a bounded above complex of finite projectives is K-flat

Let `(C, O)` be a ringed site, `Λ` a ring, and `Φ : Mod(Λ) ⥤ Mod(O)` an additive right exact
functor carrying `Λ` to the unit object -- for instance the constant sheaf of modules functor on
the constant ringed site. If `P^•` is a complex of finite projective `Λ`-modules which vanishes
strictly above some degree, then `Φ(P^•)` is K-flat.

This is the K-flatness that the bounded case of Stacks 094H consumes. There `K` and `L` are
replaced, locally on the site, by complexes of constant sheaves on complexes of finite free
`Λ`-modules; those complexes come from `StacksDraft.PseudoCoherent`, which produces a complex
bounded *above* and in general unbounded below, so the K-flatness already in the library --
`AlgebraicGeometry.RingedSite.kFlat_of_isStrictlyPerfect`, which asks for a *strictly perfect*
complex and hence for boundedness on both sides -- does not reach it.

## Main results

* `Stacks.SheafOfModules.isKFlat_mapHomologicalComplex_of_boundedAbove_finite_projective`: the
  statement above, for an arbitrary such `Φ` on an arbitrary ringed site.
* `AlgebraicGeometry.RingedSite.isKFlat_constantFunctorOver_mapHomologicalComplex`: its instance
  at the functor Stacks 09BD and Stacks 094H are stated over, namely
  `AlgebraicGeometry.RingedSite.constantFunctorOver` on a slice of the constant ringed site.

## Implementation notes

The proof is the composite of three results already in the library and adds no mathematics of
its own; what it adds is the *range*. Each term `Φ(P^i)` is a direct summand of a finite free
`O`-module by `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_obj_of_finite_projective`,
hence flat by `Stacks.SheafOfModules.isFlat_of_isDirectSummandOfFiniteFree`, and a bounded above
complex of flat sheaves of modules is K-flat by Stacks 06YQ,
`Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat`. The only step not already assembled
somewhere is the boundedness of `Φ(P^•)`, which is termwise: `Φ` is additive, so it preserves
zero morphisms and therefore zero objects.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
* [Stacks Project, Tag 09BD](https://stacks.math.columbia.edu/tag/09BD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v d

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

namespace Stacks.SheafOfModules

variable {Λ : Type (max u v)} [Ring Λ] {Y : AlgebraicGeometry.RingedSite.{u, v, max u v}}
  [HasSheafify Y.J AddCommGrpCat.{max u v}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **A bounded above complex of finite projective `Λ`-modules becomes a K-flat complex of
`O`-modules.** Let `Φ` be an additive right exact functor from `Λ`-modules to sheaves of
`O`-modules carrying `Λ` to the unit object, and let `P^•` vanish strictly above `b` and have
finite projective terms. Then `Φ(P^•)` is K-flat. -/
theorem isKFlat_mapHomologicalComplex_of_boundedAbove_finite_projective
    (Φ : ModuleCat.{max u v} Λ ⥤
      _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [Φ.Additive] [PreservesFiniteColimits Φ]
    (e : Φ.obj (ModuleCat.of Λ Λ) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (P : CochainComplex (ModuleCat.{max u v} Λ) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hfin : ∀ i : ℤ, Module.Finite Λ (P.X i))
    (hproj : ∀ i : ℤ, Module.Projective Λ (P.X i)) :
    IsKFlat Y.O ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  refine kFlat_of_boundedAbove_of_flat Y.O _ ⟨b, ?_⟩ fun i =>
    isFlat_of_isDirectSummandOfFiniteFree (Y := Y) _
      (isDirectSummandOfFiniteFree_obj_of_finite_projective Φ e (P.X i) (hfin i) (hproj i))
  exact (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
    Φ.map_isZero (P.isZero_of_isStrictlyLE b i hi)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules Stacks.SheafOfModules.Constant

variable {C : Type} [SmallCategory C] (J : GrothendieckTopology C) (Λ : Type) [CommRing Λ]
  [HasWeakSheafify J CommRingCat.{0}] [HasWeakSheafify J RingCat.{0}]
  (U : C) [HasWeakSheafify (J.over U) RingCat.{0}]
  [(J.over U).WEqualsLocallyBijective RingCat.{0}]
  [HasSheafify (J.over U) AddCommGrpCat.{0}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

omit [HasSheafify (J.over U) AddCommGrpCat] in
/-- For a bounded above complex `P` of finite projective `Λ`-modules, the complex obtained by
applying `AlgebraicGeometry.RingedSite.constantFunctorOver` termwise to `P` is K-flat over the
restriction of the constant ring sheaf `Λ̲` to `U`. -/
theorem isKFlat_constantFunctorOver_mapHomologicalComplex
    (P : CochainComplex (ModuleCat.{0} Λ) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hfin : ∀ i : ℤ, Module.Finite Λ (P.X i))
    (hproj : ∀ i : ℤ, Module.Projective Λ (P.X i)) :
    IsKFlat ((constantRingedSite J Λ).O.over U)
      (((constantFunctorOver J Λ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (constantFunctorOver J Λ U)
  have := Functor.additive_of_preservesBinaryBiproducts (constantFunctorOver J Λ U)
  exact @isKFlat_mapHomologicalComplex_of_boundedAbove_finite_projective Λ _
    ((constantRingedSite J Λ).over U) _ _ (constantFunctorOver J Λ U) this
    (preservesFiniteColimits_constantFunctorOver J Λ U)
    (constantFunctorOverUnitIso J Λ U) P b _ hfin hproj

end AlgebraicGeometry.RingedSite

end
