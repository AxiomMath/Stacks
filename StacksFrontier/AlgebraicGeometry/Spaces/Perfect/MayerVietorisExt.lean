module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ExtSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The Mayer–Vietoris sequence of homomorphisms in the derived category of an algebraic space

Let `j_U : U ⟶ X`, `j_V : V ⟶ X` and `j_P : P ⟶ X` be étale morphisms of algebraic spaces over
a scheme `S`, write `(-)|_Y` for restriction of modules along `j_Y` and `j_{Y!}` for a left
adjoint of it, extension by zero.  For `E` and `F` in the unbounded derived category `D(𝒪_X)`
a distinguished triangle

`j_{P!}E|_P ⟶ j_{U!}E|_U ⊕ j_{V!}E|_V ⟶ E ⟶ (j_{P!}E|_P)[1]`

gives the Mayer–Vietoris long exact sequence

`⋯ ⟶ Ext⁻¹(E|_P, F|_P) ⟶ Hom(E, F) ⟶ Hom(E|_U, F|_U) ⊕ Hom(E|_V, F|_V) ⟶ Hom(E|_P, F|_P) ⟶ ⋯`

running in every integer degree, its terms being the groups of homomorphisms in the derived
categories of `U`, of `V` and of `P`.  For an elementary distinguished square `(U ⊆ X, V ⟶ X)`
with `P = U ×_X V` such a triangle is supplied by Stacks 08GV, and the sequence is Stacks 08H9.

## Main definitions

* `CategoryTheory.Adjunction.shiftedHomMapDerivedCategoryEquiv` identifies the morphisms from
  `j_!A` into a shift of `F` with the morphisms from `A` into the same shift of `F|_Y`, for an
  adjunction between exact functors of abelian categories.

## Main results

* `CategoryTheory.exists_mayerVietoris_shiftedHom_longExactSequence` is the long exact sequence
  attached to a Mayer–Vietoris triangle of three exact adjunctions, exact at each of its three
  kinds of spot and in every integer degree.
* `AlgebraicGeometry.Space.exists_mayerVietoris_derivedHom_longExactSequence` is the same for
  three étale morphisms of algebraic spaces and the restriction of modules along them.
* `AlgebraicGeometry.Space.exists_mayerVietoris_derivedHom_longExactSequence_of_square`: the
  sequence of Stacks 08H9 for an elementary distinguished square, taking part (1) of Stacks 08GV
  as an input.  Untagged, as is everything in this file, and for a second reason as well: the
  three maps of the sequence are quantified over here without being described, which is weaker
  than the tag.  The tag sits on
  `AlgebraicGeometry.Space.mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtTag`, whose maps are named; the
  maps themselves are constructed in
  `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtRestriction`.

## Implementation notes

Restriction of modules along an étale morphism is `AlgebraicGeometry.Space.etaleModulePullback`,
the reading of Stacks 03LV in which the inverse image is restriction of sections along
postcomposition of étale charts, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero`.  Extension by zero is
not constructed here but enters as data: a functor together with an adjunction exhibiting it as
a left adjoint of restriction, which pins it up to a unique compatible isomorphism; its
exactness, Stacks 03DJ, enters through instance arguments on that functor, and it is what makes
the induced functor on derived categories a derived functor of the degreewise one.  For the
extension by zero the library constructs those instances are theorems:
`AlgebraicGeometry.Space.preservesFiniteLimits_etaleModuleLowerShriek` of
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact` and its two companions.

The identification of homomorphism groups is the derived adjunction of Stacks 08FJ, obtained
from the underived one by localizing the degreewise adjunction of cochain complexes
(`CategoryTheory.Adjunction.mapDerivedCategory`), followed by the commutation of the derived
restriction with the shift.  So it is the canonical identification rather than one of several.

The four morphisms into and out of the middle term of the triangle are arbitrary morphisms,
constrained only by the hypothesis that they assemble into a distinguished triangle; the
deduction uses nothing else about them.  The three maps of the resulting sequence are *defined*
in terms of them: the restriction map is composition with the two morphisms to `E`, read through
the identification above, the difference map is the Mayer–Vietoris combination of the two
morphisms out of the intersection term, and the connecting map is composition with the third
morphism of the triangle, which is
`CategoryTheory.Pretriangulated.biprodTriangleShiftedHomδ`.

At an elementary distinguished square the triangle is supplied by
`AlgebraicGeometry.Space.mem_distTriang_mayerVietoris`, whose terms are the derived functors of
the composites `j_{Y!}((-)|_Y)` rather than the composites of the derived functors.  The two
are identified by `CategoryTheory.Functor.mapDerivedCategoryComp`, and the triangle is carried
across that identification by `CategoryTheory.Pretriangulated.isomorphic_distinguished`; this
is all that separates the square's statement from the one taking the triangle as a hypothesis,
which is kept because it applies to any three étale morphisms and to any triangle of that
shape, elementary distinguished square or not.

### Where `@[stacks 08H9]` sits

The input of the statements here is **part (1) of Stacks 08GV**: the short exact sequence

`0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`

of sheaves of `𝒪_X`-modules.  It is the hypothesis `hMV` of
`AlgebraicGeometry.Space.mem_distTriang_mayerVietoris`, and so it is an input of
`AlgebraicGeometry.Space.exists_mayerVietoris_derivedHom_longExactSequence_of_square` here as
well, taken for two arbitrary maps `a` and `b` out of the intersection term so that it applies
to any such pair.  Part (2) of Stacks 08GV — the Mayer–Vietoris distinguished triangle of the
square — is taken from that theorem, and the passage from the triangle to the long exact
sequence is complete.

For the two comparisons of the square part (1) is a theorem,
`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`.  Stacks 08H9 is therefore
registered, with no hypothesis beyond those of the source, in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtTag` — on the single carrier
`AlgebraicGeometry.Space.mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek`, whose
only binder is the square and whose three maps are named rather than quantified over.  The
statements of *this* file, which quantify over the three maps, are all untagged: so are their
two discharged forms
`AlgebraicGeometry.Space.exists_mayerVietoris_derivedHom_longExactSequence_of_eds` and
`AlgebraicGeometry.Space.exists_mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek`
in that file.

That hypothesis is proved, not assumed, and the proof is the source's own: part (1) is taken at
the geometric points, by the criterion
`AlgebraicGeometry.Space.shortExact_iff_geometricModuleStalk` (Stacks 04K5) that a short
complex of `Modules.{u, u}` is short exact as soon as its geometric stalks are, together with
Equation 08GT, `AlgebraicGeometry.Space.modulePullbackStalkIso`, for the stalks of a
restriction; `AlgebraicGeometry.Space.geometricPointLift_dichotomy`, the count of lifts of a
geometric point through the two legs of the square; and Equation 08GU, the decomposition of the
stalk of an extension by zero, in the small-étale form
`AlgebraicGeometry.Space.isIso_sheafFiber_toSheaf_etaleModuleShriek_map_of_lifts` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModuleShriekStalkMap.lean`, which is stated for
`Modules.{u, u}` and for `AlgebraicGeometry.Space.etaleModuleLowerShriek` and so needs no
comparison with the slice construction on the spaces-étale site at module universe `u + 1`.
The assembly is `AlgebraicGeometry.Space.mayerVietoris_shortExact_and_mem_distTriang`, the
registered Stacks 08GV.

The three extension functors `j_{Y!}` nevertheless stay data in the statements of *this* file,
so that they apply to any choice; their existence is not an obstruction but a theorem,
`AlgebraicGeometry.Space.isRightAdjoint_etaleModulePullback`, with the chosen functor and
adjunction `AlgebraicGeometry.Space.etaleModuleLowerShriek` and
`AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction`.

## References

* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08FJ](https://stacks.math.columbia.edu/tag/08FJ)
* [Stacks Project, Tag 0149](https://stacks.math.columbia.edu/tag/0149)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section Transport

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A distinguished triangle `Y ⟶ A ⊞ B ⟶ Z ⟶ Y⟦1⟧` whose first map is a lift, whose second
is a description followed by a morphism and whose three outer terms are given up to
isomorphism stays distinguished when read at the isomorphic terms. -/
theorem mem_distTriang_biprod_of_iso {YP YU YV ZP ZU ZV T E : C}
    [HasBinaryBiproduct YU YV] [HasBinaryBiproduct ZU ZV] (iP : YP ≅ ZP) (iU : YU ≅ ZU)
    (iV : YV ≅ ZV) (a : YP ⟶ YU) (b : YP ⟶ YV) (cU : YU ⟶ T) (cV : YV ⟶ T) (g : T ⟶ E)
    (d : E ⟶ YP⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift a b) (biprod.desc cU cV ≫ g) d ∈ distTriang C) :
    Triangle.mk (biprod.lift (iP.inv ≫ a ≫ iU.hom) (iP.inv ≫ b ≫ iV.hom))
      (biprod.desc (iU.inv ≫ cU ≫ g) (iV.inv ≫ cV ≫ g))
      (d ≫ (shiftFunctor C (1 : ℤ)).map iP.hom) ∈ distTriang C := by
  refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ iP.symm
    (biprod.mapIso iU.symm iV.symm) (Iso.refl E) ?_ ?_ ?_)
  · refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  · refine biprod.hom_ext' _ _ ?_ ?_ <;> simp
  · simp [← Functor.map_comp]

end Transport

section Derived

variable {AX : Type*} [Category* AX] [Abelian AX] [HasDerivedCategory AX]
  {AU : Type*} [Category* AU] [Abelian AU] [HasDerivedCategory AU]
  {AV : Type*} [Category* AV] [Abelian AV] [HasDerivedCategory AV]
  {AP : Type*} [Category* AP] [Abelian AP] [HasDerivedCategory AP]
  {rU : AX ⥤ AU} {shriekU : AU ⥤ AX} {rV : AX ⥤ AV} {shriekV : AV ⥤ AX}
  {rP : AX ⥤ AP} {shriekP : AP ⥤ AX}
  [rU.Additive] [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
  [shriekU.Additive] [PreservesFiniteLimits shriekU] [PreservesFiniteColimits shriekU]
  [rV.Additive] [PreservesFiniteLimits rV] [PreservesFiniteColimits rV]
  [shriekV.Additive] [PreservesFiniteLimits shriekV] [PreservesFiniteColimits shriekV]
  [rP.Additive] [PreservesFiniteLimits rP] [PreservesFiniteColimits rP]
  [shriekP.Additive] [PreservesFiniteLimits shriekP] [PreservesFiniteColimits shriekP]

/-- For an adjunction `j_! ⊣ j^*` between exact functors of abelian categories, the morphisms
in the derived category from `j_!A` into the `n`-th shift of `F` are the morphisms from `A`
into the `n`-th shift of `j^*F`. -/
def Adjunction.shiftedHomMapDerivedCategoryEquiv (adj : shriekU ⊣ rU)
    (A : DerivedCategory AU) (F : DerivedCategory AX) (n : ℤ) :
    (shriekU.mapDerivedCategory.obj A ⟶ F⟦n⟧) ≃+
      (A ⟶ (rU.mapDerivedCategory.obj F)⟦n⟧) :=
  (adj.mapDerivedCategory.homAddEquiv A (F⟦n⟧)).trans
    (Stacks.ExtensionByZero.postcompAddEquiv _ ((rU.mapDerivedCategory.commShiftIso n).app F))

/-- The two identifications of `Adjunction.shiftedHomMapDerivedCategoryEquiv` for the first
and the second adjunction, taken together. -/
private def shiftedHomMapDerivedCategoryPairEquiv (adjU : shriekU ⊣ rU) (adjV : shriekV ⊣ rV)
    (E F : DerivedCategory AX) (n : ℤ) :
    ((shriekU.mapDerivedCategory.obj (rU.mapDerivedCategory.obj E) ⟶ F⟦n⟧) ×
        (shriekV.mapDerivedCategory.obj (rV.mapDerivedCategory.obj E) ⟶ F⟦n⟧)) ≃+
      ((rU.mapDerivedCategory.obj E ⟶ (rU.mapDerivedCategory.obj F)⟦n⟧) ×
        (rV.mapDerivedCategory.obj E ⟶ (rV.mapDerivedCategory.obj F)⟦n⟧)) :=
  (adjU.shiftedHomMapDerivedCategoryEquiv (rU.mapDerivedCategory.obj E) F n).prodCongr
    (adjV.shiftedHomMapDerivedCategoryEquiv (rV.mapDerivedCategory.obj E) F n)

/-- **The Mayer–Vietoris long exact sequence of a triangle of three exact adjunctions.**  Let
`j_{Y!} ⊣ j_Y^*` be exact adjunctions for `Y = U, V, P` and let

`j_{P!}P^*E ⟶ j_{U!}U^*E ⊕ j_{V!}V^*E ⟶ E ⟶ (j_{P!}P^*E)[1]`

be a distinguished triangle.  Then there are restriction, difference and connecting maps making

`⋯ ⟶ Ext⁻¹(P^*E, P^*F) ⟶ Hom(E, F) ⟶ Hom(U^*E, U^*F) ⊕ Hom(V^*E, V^*F) ⟶ Hom(P^*E, P^*F) ⟶ ⋯`

exact at each of its three kinds of spot and in every integer degree. -/
theorem exists_mayerVietoris_shiftedHom_longExactSequence (adjU : shriekU ⊣ rU)
    (adjV : shriekV ⊣ rV) (adjP : shriekP ⊣ rP) (E F : DerivedCategory AX)
    (a : shriekP.mapDerivedCategory.obj (rP.mapDerivedCategory.obj E) ⟶
      shriekU.mapDerivedCategory.obj (rU.mapDerivedCategory.obj E))
    (b : shriekP.mapDerivedCategory.obj (rP.mapDerivedCategory.obj E) ⟶
      shriekV.mapDerivedCategory.obj (rV.mapDerivedCategory.obj E))
    (cU : shriekU.mapDerivedCategory.obj (rU.mapDerivedCategory.obj E) ⟶ E)
    (cV : shriekV.mapDerivedCategory.obj (rV.mapDerivedCategory.obj E) ⟶ E)
    (d : E ⟶ (shriekP.mapDerivedCategory.obj (rP.mapDerivedCategory.obj E))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift a b) (biprod.desc cU cV) d ∈
      distTriang (DerivedCategory AX)) :
    ∃ (restriction : ∀ n : ℤ, (E ⟶ F⟦n⟧) →+
          ((rU.mapDerivedCategory.obj E ⟶ (rU.mapDerivedCategory.obj F)⟦n⟧) ×
            (rV.mapDerivedCategory.obj E ⟶ (rV.mapDerivedCategory.obj F)⟦n⟧)))
      (difference : ∀ n : ℤ,
        ((rU.mapDerivedCategory.obj E ⟶ (rU.mapDerivedCategory.obj F)⟦n⟧) ×
            (rV.mapDerivedCategory.obj E ⟶ (rV.mapDerivedCategory.obj F)⟦n⟧)) →+
          (rP.mapDerivedCategory.obj E ⟶ (rP.mapDerivedCategory.obj F)⟦n⟧))
      (boundary : ∀ n : ℤ,
        (rP.mapDerivedCategory.obj E ⟶ (rP.mapDerivedCategory.obj F)⟦n⟧) →+
          (E ⟶ F⟦n + 1⟧)),
      ∀ n : ℤ, Function.Exact (restriction n) (difference n) ∧
        Function.Exact (difference n) (boundary n) ∧
        Function.Exact (boundary n) (restriction (n + 1)) := by
  refine ⟨fun n => ((shiftedHomMapDerivedCategoryPairEquiv adjU adjV E F n) : _ →+ _).comp
      (shiftedHomRestriction cU cV F n),
    fun n => ((adjP.shiftedHomMapDerivedCategoryEquiv
        (rP.mapDerivedCategory.obj E) F n) : _ →+ _).comp
      ((shiftedHomDifference a b F n).comp
        (((shiftedHomMapDerivedCategoryPairEquiv adjU adjV E F n).symm : _ →+ _))),
    fun n => (biprodTriangleShiftedHomδ a b cU cV d F n (n + 1) rfl).comp
      ((adjP.shiftedHomMapDerivedCategoryEquiv
        (rP.mapDerivedCategory.obj E) F n).symm : _ →+ _),
    fun n => ⟨?_, ?_, ?_⟩⟩
  · refine Function.Exact.of_ladder_addEquiv_of_exact' (AddEquiv.refl _)
      (shiftedHomMapDerivedCategoryPairEquiv adjU adjV E F n).symm
      (adjP.shiftedHomMapDerivedCategoryEquiv (rP.mapDerivedCategory.obj E) F n).symm ?_ ?_
      (exact_shiftedHomRestriction_shiftedHomDifference a b cU cV d hT F n) <;>
      exact AddMonoidHom.ext fun _ => by simp
  · refine Function.Exact.of_ladder_addEquiv_of_exact'
      (shiftedHomMapDerivedCategoryPairEquiv adjU adjV E F n).symm
      (adjP.shiftedHomMapDerivedCategoryEquiv (rP.mapDerivedCategory.obj E) F n).symm
      (AddEquiv.refl _) ?_ ?_
      (exact_shiftedHomDifference_biprodTriangleShiftedHomδ a b cU cV d hT F n (n + 1) rfl) <;>
      exact AddMonoidHom.ext fun _ => by simp
  · refine Function.Exact.of_ladder_addEquiv_of_exact'
      (adjP.shiftedHomMapDerivedCategoryEquiv (rP.mapDerivedCategory.obj E) F n).symm
      (AddEquiv.refl _)
      (shiftedHomMapDerivedCategoryPairEquiv adjU adjV E F (n + 1)).symm ?_ ?_
      (exact_biprodTriangleShiftedHomδ_shiftedHomRestriction a b cU cV d hT F n (n + 1) rfl) <;>
      exact AddMonoidHom.ext fun _ => by simp

end Derived

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Etale

variable {X U V P : AlgebraicSpaces B S hS}
  (jU : U ⟶ X) (hjU : IsEtale B S hS jU.hom)
  (jV : V ⟶ X) (hjV : IsEtale B S hS jV.hom)
  (jP : P ⟶ X) (hjP : IsEtale B S hS jP.hom)
  {shriekU : Modules.{u, u} B S hS U.1 U.2 ⥤ Modules.{u, u} B S hS X.1 X.2}
  {shriekV : Modules.{u, u} B S hS V.1 V.2 ⥤ Modules.{u, u} B S hS X.1 X.2}
  {shriekP : Modules.{u, u} B S hS P.1 P.2 ⥤ Modules.{u, u} B S hS X.1 X.2}
  [shriekU.Additive] [PreservesFiniteLimits shriekU] [PreservesFiniteColimits shriekU]
  [shriekV.Additive] [PreservesFiniteLimits shriekV] [PreservesFiniteColimits shriekV]
  [shriekP.Additive] [PreservesFiniteLimits shriekP] [PreservesFiniteColimits shriekP]

/-- The Mayer–Vietoris long exact sequence of three étale morphisms of algebraic spaces,
deduced from a Mayer–Vietoris distinguished triangle.
Let `j_U : U ⟶ X`, `j_V : V ⟶ X` and `j_P : P ⟶ X` be étale morphisms of algebraic spaces over
a scheme `S`, write `(-)|_Y` for restriction of modules along `j_Y` and let `j_{Y!}` be a left
adjoint of it, extension by zero.  Let `E` and `F` be objects of `D(𝒪_X)` and suppose

`j_{P!}E|_P ⟶ j_{U!}E|_U ⊕ j_{V!}E|_V ⟶ E ⟶ (j_{P!}E|_P)[1]`

is a distinguished triangle, as it is for an elementary distinguished square `(U ⊆ X, V ⟶ X)`
with `P = U ×_X V`.  Then there are restriction, difference and connecting homomorphisms making
the Mayer–Vietoris sequence

`⋯ ⟶ Ext⁻¹(E|_P, F|_P) ⟶ Hom(E, F) ⟶ Hom(E|_U, F|_U) ⊕ Hom(E|_V, F|_V) ⟶ Hom(E|_P, F|_P) ⟶ ⋯`

exact at each of its three kinds of spot and in every integer degree, the homomorphism groups of
the restrictions being taken in the derived categories of `U`, of `V` and of `P`. -/
theorem exists_mayerVietoris_derivedHom_longExactSequence
    (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS jU hjU)
    (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS jV hjV)
    (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS jP hjP)
    (E F : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (a : shriekP.mapDerivedCategory.obj
          ((etaleModulePullback.{u, u} B S hS jP hjP).mapDerivedCategory.obj E) ⟶
        shriekU.mapDerivedCategory.obj
          ((etaleModulePullback.{u, u} B S hS jU hjU).mapDerivedCategory.obj E))
    (b : shriekP.mapDerivedCategory.obj
          ((etaleModulePullback.{u, u} B S hS jP hjP).mapDerivedCategory.obj E) ⟶
        shriekV.mapDerivedCategory.obj
          ((etaleModulePullback.{u, u} B S hS jV hjV).mapDerivedCategory.obj E))
    (cU : shriekU.mapDerivedCategory.obj
      ((etaleModulePullback.{u, u} B S hS jU hjU).mapDerivedCategory.obj E) ⟶ E)
    (cV : shriekV.mapDerivedCategory.obj
      ((etaleModulePullback.{u, u} B S hS jV hjV).mapDerivedCategory.obj E) ⟶ E)
    (d : E ⟶ (shriekP.mapDerivedCategory.obj
      ((etaleModulePullback.{u, u} B S hS jP hjP).mapDerivedCategory.obj E))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift a b) (biprod.desc cU cV) d ∈
      distTriang (DerivedCategory (Modules.{u, u} B S hS X.1 X.2))) :
    ∃ (restriction : ∀ n : ℤ, (E ⟶ F⟦n⟧) →+
          (((etaleModulePullback.{u, u} B S hS jU hjU).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS jU hjU).mapDerivedCategory.obj F)⟦n⟧) ×
            ((etaleModulePullback.{u, u} B S hS jV hjV).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS jV hjV).mapDerivedCategory.obj F)⟦n⟧)))
      (difference : ∀ n : ℤ,
        (((etaleModulePullback.{u, u} B S hS jU hjU).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS jU hjU).mapDerivedCategory.obj F)⟦n⟧) ×
            ((etaleModulePullback.{u, u} B S hS jV hjV).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS jV hjV).mapDerivedCategory.obj F)⟦n⟧)) →+
          ((etaleModulePullback.{u, u} B S hS jP hjP).mapDerivedCategory.obj E ⟶
            ((etaleModulePullback.{u, u} B S hS jP hjP).mapDerivedCategory.obj F)⟦n⟧))
      (boundary : ∀ n : ℤ,
        ((etaleModulePullback.{u, u} B S hS jP hjP).mapDerivedCategory.obj E ⟶
            ((etaleModulePullback.{u, u} B S hS jP hjP).mapDerivedCategory.obj F)⟦n⟧) →+
          (E ⟶ F⟦n + 1⟧)),
      ∀ n : ℤ, Function.Exact (restriction n) (difference n) ∧
        Function.Exact (difference n) (boundary n) ∧
        Function.Exact (boundary n) (restriction (n + 1)) :=
  exists_mayerVietoris_shiftedHom_longExactSequence adjU adjV adjP E F a b cU cV d hT

end Etale

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))
  [shriekU.Additive] [PreservesFiniteLimits shriekU] [PreservesFiniteColimits shriekU]
  [shriekV.Additive] [PreservesFiniteLimits shriekV] [PreservesFiniteColimits shriekV]
  [shriekP.Additive] [PreservesFiniteLimits shriekP] [PreservesFiniteColimits shriekP]

include adjP in
/-- The Mayer–Vietoris sequence of Stacks 08H9, from part (1) of Stacks 08GV.  Let
`(U ⊆ X, j_V : V ⟶ X)` be an
elementary distinguished square of algebraic spaces over a scheme `S`, let `P = U ×_X V`, write
`(-)|_Y` for restriction of modules along `j_Y : Y ⟶ X` and let `j_{Y!}` be a left adjoint of
it, extension by zero, with counit `j_{Y!}(F|_Y) ⟶ F`.  Suppose the short exact sequence

`0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`

of part (1) of the source holds for every sheaf of `𝒪_X`-modules `F`.  Then for all objects
`E` and `F` of `D(𝒪_X)` there are restriction, difference and connecting homomorphisms making
the Mayer–Vietoris sequence

`⋯ ⟶ Ext⁻¹(E|_P, F|_P) ⟶ Hom(E, F) ⟶ Hom(E|_U, F|_U) ⊕ Hom(E|_V, F|_V) ⟶ Hom(E|_P, F|_P) ⟶ ⋯`

exact at each of its three kinds of spot and in every integer degree, the homomorphism groups
of the restrictions being taken in the derived categories of `U`, of `V` and of `P`.

Part (2) of Stacks 08GV is taken from
`AlgebraicGeometry.Space.mem_distTriang_mayerVietoris`, and part (1) is a theorem for the two
comparisons of the square, so this is not where the tag is registered; and the three maps are
quantified over here without being described, which is weaker than the tag.  Stacks 08H9 is
`AlgebraicGeometry.Space.mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek` of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtTag`. -/
theorem exists_mayerVietoris_derivedHom_longExactSequence_of_square
    (a : etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙ shriekP ⟶
        etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙ shriekU)
    (b : etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙ shriekP ⟶
        etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙ shriekV)
    (hzero : ∀ M, biprod.lift (a.app M) (-(b.app M)) ≫
      biprod.desc (adjU.counit.app M) (adjV.counit.app M) = 0)
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (a.app M) (-(b.app M)))
      (biprod.desc (adjU.counit.app M) (adjV.counit.app M)) (hzero M)).ShortExact)
    (E F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (restriction : ∀ n : ℤ, (E ⟶ F⟦n⟧) →+
          (((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) ×
            ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧)))
      (difference : ∀ n : ℤ,
        (((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) ×
            ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧)) →+
          ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
            ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧))
      (boundary : ∀ n : ℤ,
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
            ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) →+
          (E ⟶ F⟦n + 1⟧)),
      ∀ n : ℤ, Function.Exact (restriction n) (difference n) ∧
        Function.Exact (difference n) (boundary n) ∧
        Function.Exact (boundary n) (restriction (n + 1)) := by
  have hT := mem_distTriang_mayerVietoris B S hS hsq adjU adjV a b hzero hMV E
  obtain ⟨δ, hδ⟩ := hT
  exact exists_mayerVietoris_derivedHom_longExactSequence B S hS
    (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
    (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq) adjU adjV adjP E F _ _ _ _ _
    (mem_distTriang_biprod_of_iso
      ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
        (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)) shriekP).app E)
      ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
        (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)) shriekU).app E)
      ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
        (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)) shriekV).app E)
      _ _ _ _ _ δ hδ)

end Square

end AlgebraicGeometry.Space

end
