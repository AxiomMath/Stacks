module

public import StacksFrontier.Algebra.Homology.TwoTermHomologyMono
public import StacksFrontier.RingTheory.NaiveCotangent.TwoTermDoubleQuasiIso
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentCompositionTriangle
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSixTerm
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# The canonical map to the shifted cone is a quasi-isomorphism

Let `A ⟶ B ⟶ C` be morphisms of sheaves of commutative rings on a topological space.  The
canonical map

`c : NL_{B/A} ⊗_B C ⟶ C(NL_{C/A} ⟶ NL_{C/B})[-1]`

of Stacks 0E1Y is an isomorphism on `H⁰` and surjective on `H^{-1}` for an arbitrary tower, and
that is everything the six-term exact sequence of Stacks 0E1Y gives.  This file shows that one
further input — injectivity on `H₁` of the ring-level comparison at every stalk — makes it a
**quasi-isomorphism**, and hence an isomorphism in the derived category.

Over a pair of composable morphisms of schemes `f : X ⟶ Y`, `g : Y ⟶ Z` with `f` a local complete
intersection morphism that input is
`Stacks.NaiveCotangentLciStalk.injective_onH₁_nlExtensionBaseChangeMap_stalk_of_lci`, and the
conclusion is the comparison of Stacks 0FV3.

## Main results

* `AlgebraicGeometry.SheafOfModules.mono_homologyMap_iff_forall_stalk`: monomorphy of a map of
  cohomology sheaves is stalkwise, the companion of
  `AlgebraicGeometry.SheafOfModules.epi_homologyMap_iff_forall_stalk` and
  `AlgebraicGeometry.SheafOfModules.isIso_homologyMap_iff_forall_stalk`.
* `Stacks.SheafOfModules.mono_homologyMap_spaceBaseChangeNaiveCotangentMap_negOne`: the canonical
  map `c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}` is a monomorphism on `H^{-1}` as soon as it is injective
  on `H₁` at every stalk.
* `Stacks.SheafOfModules.isZero_homology_spaceNaiveCotangentCone`: the shifted cone has no
  cohomology outside degrees `-1` and `0`.
* `Stacks.SheafOfModules.quasiIso_spaceNaiveCotangentConeMap_of_stalkwiseInjectiveOnH₁`: the
  canonical map of Stacks 0E1Y is a quasi-isomorphism, given that extra input.  The name carries
  the hypothesis because `Stacks.SheafOfModules.quasiIso_spaceNaiveCotangentConeMap` of
  `StacksFrontier/AlgebraicGeometry/MoreMorphisms/NaiveCotangentConeMapInvertible.lean` is a
  different statement -- the same conclusion under formal smoothness instead.
* `Stacks.SheafOfModules.isIso_Q_map_ringedSpaceNaiveCotangentConeMap`: the canonical map of
  Stacks 0E1Z is an isomorphism in `D(𝒪_X)`.

## Implementation notes

**Where the extra input enters, and only there.**  The projection of the shifted cone is a
monomorphism in degree `-1` (`Stacks.SheafOfModules.mono_homologyMap_pShift_negOne`) and `c`
composed with it is `c₁`, so `H^{-1}(c)` is a monomorphism as soon as `H^{-1}(c₁)` is; with
`H^{-1}(c)` already an epimorphism for an arbitrary tower
(`Stacks.SheafOfModules.epi_homologyMap_spaceNaiveCotangentConeMap_negOne`) that makes it an
isomorphism.  On `H⁰` it is an isomorphism for an arbitrary tower
(`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`).

**The degrees outside `-1` and `0`.**  The source has zero terms there, hence zero cohomology.
The shifted cone has a nonzero term in degree `1`, but no cohomology: the connecting morphism
`H^{j-1}(NL_{C/B}) ⟶ H^j(C[-1])` of the long exact sequence of the cone is preceded by
`H^{j-1}(NL_{C/A}) ⟶ H^{j-1}(NL_{C/B})`, which is an epimorphism — for `j = 1` because it is the
final `⟶ 0` of the six-term sequence, and for every other `j` because its target vanishes — so
the connecting morphism is zero; the long exact sequence then makes
`H^j(C[-1]) ⟶ H^j(NL_{C/A}) = 0` a monomorphism, and a monomorphism into a zero object has a
zero source.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the canonical map and
  the six-term exact sequence for sheaves of rings on a topological space.
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the same for a pair of
  composable morphisms of ringed spaces.
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), the stalkwise criterion.
* [Stacks Project, Tag 08RI](https://stacks.math.columbia.edu/tag/08RI), the long exact sequence
  of the cone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open TopologicalSpace
open AlgebraicGeometry CochainComplex
open Stacks.SheafOfModules
open Stacks.NaiveCotangentAffineStalkLegs
open Stacks.NaiveCotangentStalkBaseChange
open Stacks.NaiveCotangentTowerStalk
open Stacks.RelativeDifferentialStalk (algebraStalk)
open AlgebraicGeometry.SheafOfModules (stalkFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sites.Conormal (stalkIsScalarTowerSquareTarget)

universe t u

noncomputable section

namespace AlgebraicGeometry.SheafOfModules

/-! ### Monomorphy of a map of cohomology sheaves is stalkwise -/

section StalkwiseMono

variable {X : TopCat.{u}}
  (𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})

private theorem mono_map_iff_of_natIso {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F G : C ⥤ D} (α : F ≅ G) {A B : C} (h : A ⟶ B) : Mono (F.map h) ↔ Mono (G.map h) := by
  rw [← mono_comp_iff_of_mono (f := α.hom.app B) (g := F.map h), α.hom.naturality,
    mono_comp_iff_of_isIso]

/-- **Monomorphy is stalkwise, over the stalk ring.**  A morphism of sheaves of `𝒪`-modules is a
monomorphism if and only if every induced map of stalks is. -/
theorem mono_iff_forall_mono_stalkFunctor_map {M N : _root_.SheafOfModules.{u} 𝒪} (g : M ⟶ N) :
    Mono g ↔ ∀ x : X, Mono ((stalkFunctor 𝒪 x).map g) := by
  rw [mono_iff_injective_stalkMap]
  exact forall_congr' fun x => (ModuleCat.mono_iff_injective _).symm

/-- The map induced in degree `i` on cohomology by a morphism of cochain complexes of sheaves of
`𝒪`-modules is a monomorphism if and only if, for every point `x` of `X`, the map induced in
degree `i` on cohomology by the corresponding morphism of complexes of stalks is.

The stalk functor is exact, so it commutes with cohomology; monomorphy is then detected on
stalks. -/
theorem mono_homologyMap_iff_forall_stalk
    {K L : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ} (f : K ⟶ L) (i : ℤ) :
    Mono (HomologicalComplex.homologyMap f i) ↔ ∀ x : X,
      Mono (HomologicalComplex.homologyMap
        (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map f) i) := by
  rw [mono_iff_forall_mono_stalkFunctor_map]
  exact forall_congr' fun x => (mono_map_iff_of_natIso
    (ShortComplex.homologyFunctorIso (stalkFunctor 𝒪 x))
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) i).map f)).symm

end StalkwiseMono

end AlgebraicGeometry.SheafOfModules

namespace Stacks.SheafOfModules

/-! ### The canonical map `c₁` is a monomorphism on `H^{-1}` -/

section Space

attribute [local instance 1]
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C) (z : T)

/-- **The one extra input.**  The canonical map `c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}` of Stacks 0E1Y
is injective on `H₁` at every stalk, for every morphism of extensions inducing it.  Over a pair
of composable morphisms of schemes with the first a local complete intersection morphism this is
`Stacks.NaiveCotangentLciStalk.injective_onH₁_nlExtensionBaseChangeMap_stalk_of_lci`. -/
abbrev StalkwiseInjectiveOnH₁ : Prop :=
  ∀ w : T,
    letI := algebraStalk a.hom w
    letI := algebraStalk (a ≫ b).hom w
    letI := algebraStalk b.hom w
    letI := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b w rfl
    ∀ h : (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj w))
          (ToType (TopCat.Presheaf.stalk B.obj w))).toExtension.Hom
        (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj w))
          (ToType (TopCat.Presheaf.stalk C.obj w))).toExtension,
      Function.Injective (NaiveCotangent.nlExtensionBaseChangeMap
        (T := ToType (TopCat.Presheaf.stalk C.obj w)) h).onH₁

/-- **Injectivity of the canonical map `c₁` on cycles, at a stalk, elementwise.**  A cycle of the
stalk of `NL_{B/A} ⊗_B C` in degree `-1` killed by `c₁` is zero, given the ring-level injectivity
on `H₁` at the tower of stalk rings.

This is `Stacks.TwoTermDoubleQuasiIso.eq_zero_of_injective_onH₁` read through Stacks 0D09 at the
two complexes and through the identification of the stalk of `c₁`, in the same way as
`Stacks.NaiveCotangentStalkJacobiZariski.exists_cycle_stalk` reads exactness. -/
theorem eq_zero_stalk
    (ξ : ToType ((stalkFunctor (ringSheaf.{u, u, u} C) z).obj
      ((spaceBaseChangeNaiveCotangentComplex A B C a b).X (-1))))
    (hd : ((stalkFunctor (ringSheaf.{u, u, u} C) z).map
        ((spaceBaseChangeNaiveCotangentComplex A B C a b).d (-1) 0)).hom ξ = 0)
    (hc : ((stalkFunctor (ringSheaf.{u, u, u} C) z).map
        ((spaceBaseChangeNaiveCotangentMap A B C a b).f (-1))).hom ξ = 0)
    (hring :
      letI := algebraStalk a.hom z
      letI := algebraStalk (a ≫ b).hom z
      letI := algebraStalk b.hom z
      letI := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
      ∀ h : (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
            (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.Hom
          (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
            (ToType (TopCat.Presheaf.stalk C.obj z))).toExtension,
        Function.Injective (NaiveCotangent.nlExtensionBaseChangeMap
          (T := ToType (TopCat.Presheaf.stalk C.obj z)) h).onH₁) :
    ξ = 0 := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  let := moduleRingStalkCotangent A C (a ≫ b) z
  let := moduleRingStalkCotangentSpace A C (a ≫ b) z
  refine CochainComplex.eq_zero_of_addEquiv
    (u₁ := stalkBaseChangeAddEquivNegOne A B C a b z)
    (u₀ := stalkBaseChangeAddEquivZero A B C a b z)
    (v₁ := (stalkLegNegOneLinear A C (a ≫ b) z).toAddEquiv)
    (stalkBaseChangeAddEquiv_d A B C a b z)
    (Stacks.NaiveCotangentStalkJacobiZariski.stalkLegNegOneLinear_spaceBaseChangeMap A B C a b z)
    (Stacks.TwoTermDoubleQuasiIso.eq_zero_of_injective_onH₁
      (hring (stalkTowerHomBase A B C a b z))) ξ hd hc

/-- The terms of the source of the canonical map vanish outside degrees `-1` and `0`. -/
private theorem isZero_X_spaceBaseChangeNaiveCotangentComplex (j : ℤ) (hj : j ≠ -1)
    (hj0 : j ≠ 0) :
    IsZero ((spaceBaseChangeNaiveCotangentComplex A B C a b).X j) :=
  CategoryTheory.Functor.map_isZero
    (towerExtendScalars.{u, u, u} (Opens.grothendieckTopology T) B C b)
    (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) A B a j hj hj0)

/-- **The canonical map `c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}` is a monomorphism on `H^{-1}`** as soon
as it is injective on `H₁` at every stalk.  In degree `-1` the cohomology sheaf is the sheaf of
cycles, both complexes vanishing in degree `-2`, so monomorphy is injectivity on cycles, and that
is stalkwise. -/
theorem mono_homologyMap_spaceBaseChangeNaiveCotangentMap_negOne
    (hring : StalkwiseInjectiveOnH₁ A B C a b) :
    Mono (HomologicalComplex.homologyMap
      (spaceBaseChangeNaiveCotangentMap A B C a b) (-1)) := by
  refine (AlgebraicGeometry.SheafOfModules.mono_homologyMap_iff_forall_stalk
    (ringSheaf.{u, u, u} C)
    (spaceBaseChangeNaiveCotangentMap A B C a b) (-1)).2 fun z => ?_
  refine HomologicalComplex.mono_homologyMap_of_mono_cyclesMap _ (-2) (-1)
    (by rw [CochainComplex.prev]; ring) ?_ ?_ ?_
  · exact (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ z _
      (isZero_X_spaceBaseChangeNaiveCotangentComplex A B C a b (-2)
        (by decide) (by decide))).eq_of_src _ _
  · exact (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ z _
      (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b) (-2)
        (by decide) (by decide))).eq_of_src _ _
  · exact HomologicalComplex.mono_cyclesMap_of_injective _ (-1) 0
      (by rw [CochainComplex.next]; ring)
      fun x hx hfx => eq_zero_stalk A B C a b z x hx hfx (hring z)

/-! ### The cohomology of the shifted cone outside degrees `-1` and `0` -/

/-- **The connecting morphism into a degree outside `-1` and `0` vanishes.**  It is preceded in
the long exact sequence of the cone by `H^{j-1}(NL_{C/A}) ⟶ H^{j-1}(NL_{C/B})`, which is an
epimorphism: for `j = 1` that is the final `⟶ 0` of the six-term sequence of Stacks 0E1Y, and
for every other `j` outside `-1` and `0` its target vanishes. -/
private theorem spaceNaiveCotangentConeHomologyConnecting_eq_zero (j : ℤ) (hj : j ≠ -1)
    (hj0 : j ≠ 0) :
    spaceNaiveCotangentConeHomologyConnecting A B C a b (-1 + j) j rfl = 0 := by
  have hepi : Epi (HomologicalComplex.homologyMap
      (spaceRelativeNaiveCotangentComplexMap A B C a b) (-1 + j)) := by
    obtain rfl | h1 := eq_or_ne j 1
    · rw [show (-1 : ℤ) + 1 = 0 by norm_num]
      exact epi_homologyMap_spaceRelativeNaiveCotangentComplexMap_zero A B C a b
    · exact ⟨fun _ _ _ => (naiveCotangentComplex_isZero_homology.{u, u, u}
        (Opens.grothendieckTopology T) B C b (-1 + j) (by omega) (by omega)).eq_of_src _ _⟩
  exact zero_of_epi_comp
    (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap A B C a b) (-1 + j))
    (CochainComplex.homologyMap_comp_coneHomologyConnecting
      (spaceRelativeNaiveCotangentComplexMap A B C a b) (-1 + j) j rfl)

/-- **The shifted cone has no cohomology outside degrees `-1` and `0`.**  The connecting morphism
into degree `j` vanishes, so the long exact sequence of the cone makes the projection
`H^j(C(g)[-1]) ⟶ H^j(NL_{C/A})` a monomorphism, and its target vanishes. -/
theorem isZero_homology_spaceNaiveCotangentCone (j : ℤ) (hj : j ≠ -1) (hj0 : j ≠ 0) :
    IsZero (((CategoryTheory.shiftFunctor
      (CochainComplex (_root_.SheafOfModules.{u}
        (ringSheaf.{u, u, u} C)) ℤ) (-1 : ℤ)).obj
      (CochainComplex.mappingCone
        (spaceRelativeNaiveCotangentComplexMap A B C a b))).homology j) := by
  have hmono : Mono (HomologicalComplex.homologyMap
      (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) j) :=
    (ShortComplex.exact_iff_mono _
        (spaceNaiveCotangentConeHomologyConnecting_eq_zero A B C a b j hj hj0)).1
      (spaceNaiveCotangentCone_homology_exact_cone A B C a b (-1 + j) j rfl)
  exact IsZero.of_mono
    (HomologicalComplex.homologyMap
      (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) j)
    (naiveCotangentComplex_isZero_homology.{u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b) j
      hj hj0)

/-- **The source of the canonical map has no cohomology outside degrees `-1` and `0`**, its terms
there being zero objects. -/
private theorem isZero_homology_spaceBaseChangeNaiveCotangentComplex (j : ℤ) (hj : j ≠ -1)
    (hj0 : j ≠ 0) :
    IsZero ((spaceBaseChangeNaiveCotangentComplex A B C a b).homology j) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (isZero_X_spaceBaseChangeNaiveCotangentComplex A B C a b j hj hj0)

/-! ### The canonical map is a quasi-isomorphism -/

/-- **The canonical map `c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]` of Stacks 0E1Y is an isomorphism on every
cohomology sheaf**, given that `c₁` is injective on `H₁` at every stalk.

In degree `0` it is an isomorphism for an arbitrary tower; in degree `-1` it is an epimorphism
for an arbitrary tower and the extra input makes it a monomorphism; and outside those two degrees
both cohomology sheaves vanish. -/
theorem isIso_homologyMap_spaceNaiveCotangentConeMap
    (hring : StalkwiseInjectiveOnH₁ A B C a b)
    (j : ℤ) :
    IsIso (HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) j) := by
  obtain rfl | hj := eq_or_ne j (-1)
  · have : Mono (HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) (-1) ≫
        HomologicalComplex.homologyMap
          (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) (-1)) := by
      rw [← HomologicalComplex.homologyMap_comp, spaceNaiveCotangentConeMap_comp_pShift]
      exact mono_homologyMap_spaceBaseChangeNaiveCotangentMap_negOne A B C a b hring
    have := mono_of_mono
      (HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) (-1))
      (HomologicalComplex.homologyMap
        (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) (-1))
    have := epi_homologyMap_spaceNaiveCotangentConeMap_negOne A B C a b
    exact isIso_of_mono_of_epi _
  obtain rfl | hj0 := eq_or_ne j 0
  · exact isIso_homologyMap_spaceNaiveCotangentConeMap_zero A B C a b
  exact ⟨0, (isZero_homology_spaceBaseChangeNaiveCotangentComplex A B C a b j hj hj0).eq_of_src _ _,
    (isZero_homology_spaceNaiveCotangentCone A B C a b j hj hj0).eq_of_src _ _⟩

/-- **The canonical map of Stacks 0E1Y is a quasi-isomorphism**, given that `c₁` is injective on
`H₁` at every stalk. -/
theorem quasiIso_spaceNaiveCotangentConeMap_of_stalkwiseInjectiveOnH₁
    (hring : StalkwiseInjectiveOnH₁ A B C a b) :
    QuasiIso (spaceNaiveCotangentConeMap A B C a b) :=
  (_root_.quasiIso_iff _).2 fun j =>
    (quasiIsoAt_iff_isIso_homologyMap _ j).2
      (isIso_homologyMap_spaceNaiveCotangentConeMap A B C a b hring j)

end Space

/-! ### The canonical map of Stacks 0E1Z in the derived category -/

section RingedSpace

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasDerivedCategory.{t} (_root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology (X : TopCat)) X.sheaf))]

/-- **The canonical map `f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]` of Stacks 0E1Z is an
isomorphism in `D(𝒪_X)`**, given that the canonical map `c₁` is injective on `H₁` at every stalk
of the tower `f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X`.

The canonical map is the identification of Stacks 08TM, which is an isomorphism of complexes,
followed by the canonical map of Stacks 0E1Y for that tower. -/
theorem isIso_Q_map_ringedSpaceNaiveCotangentConeMap
    (hring : StalkwiseInjectiveOnH₁ (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f)) :
    IsIso (DerivedCategory.Q.map (ringedSpaceNaiveCotangentConeMap f g)) := by
  have : IsIso (DerivedCategory.Q.map (spaceNaiveCotangentConeMap (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f))) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact quasiIso_spaceNaiveCotangentConeMap_of_stalkwiseInjectiveOnH₁ _ _ _ _ _ hring
  rw [show ringedSpaceNaiveCotangentConeMap f g =
      (pulledNaiveCotangentComparison f g).hom ≫
        spaceNaiveCotangentConeMap (inverseImageBaseRing f g) (inverseImageMiddleRing f)
          X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f) from rfl,
    DerivedCategory.Q.map_comp]
  infer_instance

/-- The comparison of Stacks 0E1Z with the sign that makes it match the projection out of the
mapping cocone: the projection `C(φ)[-1] ⟶ K` out of the mapping cocone is the negative of the
projection through which Stacks 0E1Z characterises the comparison, so it is `-c` and not `c` that
replaces the first vertex of the triangle, and `-c` is an isomorphism exactly when `c` is. -/
theorem isIso_neg_Q_map_ringedSpaceNaiveCotangentConeMap
    (hring : StalkwiseInjectiveOnH₁ (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f)) :
    IsIso (-DerivedCategory.Q.map (ringedSpaceNaiveCotangentConeMap f g)) := by
  have h := isIso_Q_map_ringedSpaceNaiveCotangentConeMap f g hring
  refine ⟨-inv (DerivedCategory.Q.map (ringedSpaceNaiveCotangentConeMap f g)), ?_, ?_⟩
  · rw [Preadditive.neg_comp_neg, IsIso.hom_inv_id]
  · rw [Preadditive.neg_comp_neg, IsIso.inv_hom_id]

/-- The comparison of Stacks 0E1Z, with that sign, as an isomorphism of `D(𝒪_X)`. -/
def coneComparisonIso
    (hring : StalkwiseInjectiveOnH₁ (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f)) :=
  letI := isIso_neg_Q_map_ringedSpaceNaiveCotangentConeMap f g hring
  asIso (-DerivedCategory.Q.map (ringedSpaceNaiveCotangentConeMap f g))

/-- **The triangle `f^*NL_{Y/Z} ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ f^*NL_{Y/Z}[1]` of `D(𝒪_X)`**: the
triangle of the mapping cocone of the canonical map `NL_{X/Z} ⟶ NL_{X/Y}` with its first vertex
replaced by `f^*NL_{Y/Z}` along the comparison of Stacks 0E1Z. -/
def coneTriangle
    (hring : StalkwiseInjectiveOnH₁ (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f)) :=
  Triangle.mk
    ((coneComparisonIso f g hring).hom ≫
      (Stacks.NaiveCotangentCompositionTriangle.triangle f g).mor₁)
    (Stacks.NaiveCotangentCompositionTriangle.triangle f g).mor₂
    ((Stacks.NaiveCotangentCompositionTriangle.triangle f g).mor₃ ≫
      (coneComparisonIso f g hring).inv⟦(1 : ℤ)⟧')

/-- **The first morphism of the triangle is the canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}`.**  The
projection out of the mapping cocone is the negative of the projection of Stacks 0E1Z, and the
comparison used to replace the first vertex carries the matching sign, so the two signs
cancel. -/
theorem coneTriangle_mor₁
    (hring : StalkwiseInjectiveOnH₁ (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f)) :
    (coneTriangle f g hring).mor₁ = DerivedCategory.Q.map
      (Stacks.NaiveCotangentCompositionTriangle.pulledNaiveCotangentMap f g) :=
  have h1 : DerivedCategory.Q.map (ringedSpaceNaiveCotangentConeMap f g) ≫
      DerivedCategory.Q.map (CochainComplex.mappingCocone.fst
        (Stacks.NaiveCotangentCompositionTriangle.relativeNaiveCotangentMap f g)) =
      -DerivedCategory.Q.map
        (Stacks.NaiveCotangentCompositionTriangle.pulledNaiveCotangentMap f g) :=
    (CategoryTheory.Functor.map_comp DerivedCategory.Q _ _).symm.trans
      ((congrArg DerivedCategory.Q.map
          (Stacks.NaiveCotangentCompositionTriangle.coneMap_comp_fst f g)).trans
        (CategoryTheory.Functor.map_neg DerivedCategory.Q))
  (Preadditive.neg_comp ..).trans ((congrArg Neg.neg h1).trans (neg_neg _))

/-- **The second morphism of the triangle is the canonical map `NL_{X/Z} ⟶ NL_{X/Y}`.** -/
theorem coneTriangle_mor₂
    (hring : StalkwiseInjectiveOnH₁ (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f)) :
    (coneTriangle f g hring).mor₂ = DerivedCategory.Q.map
      (Stacks.NaiveCotangentCompositionTriangle.relativeNaiveCotangentMap f g) :=
  rfl

/-- **The triangle is distinguished.**  It is the triangle of the mapping cocone of the canonical
map `NL_{X/Z} ⟶ NL_{X/Y}`, which is distinguished, with its first vertex replaced along the
comparison of Stacks 0E1Z, an isomorphism by
`Stacks.SheafOfModules.isIso_Q_map_ringedSpaceNaiveCotangentConeMap`. -/
theorem coneTriangle_distinguished
    (hring : StalkwiseInjectiveOnH₁ (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f)) :
    coneTriangle f g hring ∈ distTriang _ := by
  refine isomorphic_distinguished
    (Stacks.NaiveCotangentCompositionTriangle.triangle f g)
    (Stacks.NaiveCotangentCompositionTriangle.triangle_distinguished f g) _
    (Triangle.isoMk _ _ (coneComparisonIso f g hring) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · exact Category.comp_id _
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (Stacks.NaiveCotangentCompositionTriangle.triangle f g).mor₃ ≫ k)
          (((CategoryTheory.Functor.map_comp
                (CategoryTheory.shiftFunctor _ (1 : ℤ)) _ _).symm).trans
            ((congrArg (CategoryTheory.shiftFunctor _ (1 : ℤ)).map
                (Iso.inv_hom_id (coneComparisonIso f g hring))).trans
              (CategoryTheory.Functor.map_id (CategoryTheory.shiftFunctor _ (1 : ℤ)) _)))).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))

end RingedSpace

end Stacks.SheafOfModules

end

end
