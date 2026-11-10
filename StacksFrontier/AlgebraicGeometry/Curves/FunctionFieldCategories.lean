module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Mathlib.CategoryTheory.Widesubcategory
public import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.Curves.RationalMapExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Equivalence
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksCore.Tactic.StacksAttribute

/-!
# Curves, their function fields, and their proper models

Let `k` be a field. **Stacks Project, Tag 0BY1** asserts that six categories are canonically
equivalent:

1. finitely generated field extensions `K/k` of transcendence degree one;
2. curves over `k` and dominant rational maps;
3. normal projective curves over `k` and nonconstant morphisms;
4. nonsingular projective curves over `k` and nonconstant morphisms;
5. regular projective curves over `k` and nonconstant morphisms;
6. normal proper curves over `k` and nonconstant morphisms.

This file builds the six categories and the comparisons between them that the source's proof
supplies. The source organises the proof as follows: (1) and (2) are compared by restricting the
anti-equivalence of Stacks 0BXN to transcendence degree one; (3), (4), (5) and (6) are *the same*
category, since "nonsingular" and "regular" are synonyms, since normality and regularity agree
for curves (Stacks 0BX2), and since a proper curve is projective (Stacks 0A26); and the
comparison of (3) with (2) is a fully faithful functor, Stacks 0BXZ, which is essentially
surjective because every finitely generated field extension of transcendence degree one is the
function field of a normal projective curve. Everything in that list is proved below, essential
surjectivity included; see "Essential surjectivity".

## Main definitions

* `AlgebraicGeometry.FinitelyGeneratedFieldExtensionTrdegOne` — category (1).
* `AlgebraicGeometry.Curve` — category (2).
* `AlgebraicGeometry.NormalProjectiveCurve` — category (3).
* `AlgebraicGeometry.NonsingularProjectiveCurve` — category (4).
* `AlgebraicGeometry.RegularProjectiveCurve` — category (5).
* `AlgebraicGeometry.NormalProperCurve` — category (6).
* `AlgebraicGeometry.normalProjectiveCurveToCurve` — the functor (3) → (2).

## Main results

* `AlgebraicGeometry.isCurve_iff_trdeg_functionField_eq_one`: a variety over `k` is a curve
  exactly when its function field has transcendence degree one, the step of the source's proof
  which cuts the anti-equivalence of Stacks 0BXN down to size.
* `AlgebraicGeometry.curveEquivalenceFinitelyGeneratedFieldExtensionTrdegOneOpposite`:
  categories (1) and (2) are anti-equivalent.
* `AlgebraicGeometry.normalProjectiveCurveEquivalenceRegularProjectiveCurve`: categories (3)
  and (5) are the same.
* `AlgebraicGeometry.nonsingularProjectiveCurveEquivalenceRegularProjectiveCurve`: categories (4)
  and (5) are the same.
* `AlgebraicGeometry.normalProjectiveCurveEquivalenceNormalProperCurve`: categories (3) and (6)
  are the same.
* `AlgebraicGeometry.isProjectiveMorphism_of_isProper_of_isCurve`: a proper curve over a field is
  H-projective, the case of Stacks 0A26 that the previous item needs, with no hypothesis carried.
* `AlgebraicGeometry.normalProjectiveCurveToCurveFullyFaithful`: the functor (3) → (2) is fully
  faithful.
* `AlgebraicGeometry.exists_isCurve_isProjectiveMorphism_isOpenImmersion`: a curve over `k` is a
  dense open subscheme of a projective curve over `k`, with nothing carried.
* `AlgebraicGeometry.normalProjectiveCurveToCurve_essSurj`: the functor (3) → (2) is essentially
  surjective — every curve is birational to a normal projective curve.
* `AlgebraicGeometry.normalProjectiveCurveEquivalenceCurve`: categories (2) and (3) are
  equivalent.

## Implementation notes

Category (2) is a full subcategory of `AlgebraicGeometry.Variety`, the category of varieties over
`k` and dominant rational maps underlying Stacks 0BXN, cut out by the property of being a curve;
category (1) is the corresponding full subcategory of
`AlgebraicGeometry.FinitelyGeneratedFieldExtension`, cut out by having transcendence degree one.
The anti-equivalence between them is therefore *literally* the restriction of the one of
Stacks 0BXN, obtained from `CategoryTheory.Equivalence.congrFullSubcategory`, and no new functor
is built.

Categories (3)–(6) are full subcategories of one and the same category — the schemes over `k`
with nonconstant morphisms over `k`, `AlgebraicGeometry.SchemeOverNonconstant`, a wide
subcategory of `CategoryTheory.Over (Spec k)` — so the source's assertion that they are the same
category is formalized by the statement that the *inclusions* of these full subcategories are
equivalences. Those inclusions are the identity on underlying schemes and on morphisms, which is
the strongest available reading of "the categories are the same".

A nonconstant morphism is formalized as a dominant one, `AlgebraicGeometry.IsDominant` of the
underlying morphism of schemes. This is the reading the source's own proof uses: it takes a
nonconstant morphism of nonsingular projective curves to be one carrying the generic point of the
source to the generic point of the target, which for morphisms of integral schemes is exactly
dominance.

Categories (4) and (5) are the same *type*, not merely equivalent types: "nonsingular" and
"regular" are synonyms, Stacks 02IS, and this library has one predicate
`AlgebraicGeometry.IsRegular` formalizing both. So
`AlgebraicGeometry.NonsingularProjectiveCurve` is a reducible abbreviation for
`AlgebraicGeometry.RegularProjectiveCurve` and the comparison is `CategoryTheory.Equivalence.refl`.
The content of the source's claim here is the synonymy of two words, which is a matter of
terminology and not a separately formalizable mathematical statement.

Projectivity is `AlgebraicGeometry.IsProjectiveMorphism`, H-projectivity, which is what
`AlgebraicGeometry.IsProjectiveVariety` adds to being a variety; being a curve already supplies
the variety hypotheses, so the object properties are stated as a conjunction of
`AlgebraicGeometry.IsCurve` with the bare projectivity or properness of the structure morphism
rather than with the bundled variety classes.

Everything proved here is unconditional. The comparison of (3) with (6) needs the source's step
"a proper curve is projective" only for a *curve*, which is integral of dimension exactly one;
that step is `AlgebraicGeometry.isProjectiveMorphism_of_isProper_of_isCurve`, which takes
Tag 0A25 in its integral case
`Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral`, run off
[Stacks, Tag 09ND]. Tag 0A25 also holds in general, as
`Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_dimension_le_one`, from
[Stacks, Tag 09NZ],
`Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one`.

## Essential surjectivity

Essential surjectivity of `AlgebraicGeometry.normalProjectiveCurveToCurve` — the source's final
paragraph, that every finitely generated field extension of `k` of transcendence degree one is
the function field of a normal projective curve — is proved by the route of the source's own
remark: compactify, then normalize.

A curve `X` over `k` is a dense open subscheme of a projective curve `Y` over `k`, which is
Stacks 0BXV — the completion
`Stacks.CurveProjectiveCompletion.exists_projective_completion_aux_of_isHQuasiProjective` —
together with the observation that the compactification of a curve is again a curve. Nothing is
carried there: the only input of Stacks 0BXV beyond its own hypotheses is Stacks 0A25, supplied
here in its integral case `Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral`,
exactly as for Tag 0A26 above. Both tags hold in full generality as well, as
`Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_dimension_le_one` and
`Stacks.CurveProjectiveCompletion.exists_projective_completion_of_dimension_le_one`. The
normalization of `Y` is then a normal proper curve over `k` — a variety by
Stacks 0BXR, proper by Stacks 0GK4 since the normalization morphism is finite, and
one-dimensional because the normalization morphism is birational — hence a normal *projective*
curve by `AlgebraicGeometry.isProjectiveMorphism_of_isProper_of_isCurve`.

Both the open immersion and the normalization morphism are dominant and induce isomorphisms of
function fields, so both become isomorphisms in category (2): the function-field functor of
Stacks 0BXN is fully faithful, so it reflects isomorphisms, and that is how the birational
identification of the normal projective curve with `X` is produced, in
`AlgebraicGeometry.varietyIsoOfIsIsoFunctionFieldMap`.

## References

* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1)
* [Stacks Project, Tag 0BXN](https://stacks.math.columbia.edu/tag/0BXN)
* [Stacks Project, Tag 0BXZ](https://stacks.math.columbia.edu/tag/0BXZ)
* [Stacks Project, Tag 0BX2](https://stacks.math.columbia.edu/tag/0BX2)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 02IS](https://stacks.math.columbia.edu/tag/02IS)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-! ### The transcendence degree of the function field -/

/-- For a variety over `k`, the function field is `k`-algebra isomorphic to the residue field at
the generic point: the local ring at the generic point of an integral scheme is already a field,
so the residue map is bijective, and both `k`-algebra structures are induced by the global
sections of the structure morphism. -/
noncomputable def functionFieldAlgEquivGenericResidueField (X : Variety k) :
    letI : Algebra k (X.toScheme.residueField (genericPoint X.toScheme)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.structureMap.appTop ≫
        X.toScheme.Γevaluation (genericPoint X.toScheme)).hom.toAlgebra
    X.toScheme.functionField ≃ₐ[k] X.toScheme.residueField (genericPoint X.toScheme) := by
  letI : Algebra k (X.toScheme.residueField (genericPoint X.toScheme)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ X.structureMap.appTop ≫
      X.toScheme.Γevaluation (genericPoint X.toScheme)).hom.toAlgebra
  refine AlgEquiv.ofRingEquiv (R := k)
    (f := RingEquiv.ofBijective (X.toScheme.residue (genericPoint X.toScheme)).hom
      ⟨RingHom.injective (X.toScheme.residue (genericPoint X.toScheme)).hom,
        X.toScheme.residue_surjective _⟩) ?_
  intro a
  change (X.toScheme.residue (genericPoint X.toScheme)).hom (functionFieldAlgebraMap X a) = _
  rw [functionFieldAlgebraMap_eq_germToFunctionField X]
  rfl

/-- A variety over `k` is a curve exactly when its function field has transcendence degree one
over `k`.

This is the step "a variety is a curve if and only if its function field has transcendence degree
one" of the proof of Stacks 0BY1. It is a consequence of the clause of Stacks 0A21 already in the
library as `AlgebraicGeometry.topologicalKrullDim_eq_trdeg_residueField`, namely that the
dimension of an irreducible scheme locally of finite type over `k` is the transcendence degree of
the residue field at its generic point, together with the identification of that residue field
with the function field. -/
@[ega "IV 5.2.1" "special case"]
theorem isCurve_iff_trdeg_functionField_eq_one (X : Variety k) :
    IsCurve k X.structureMap ↔ Algebra.trdeg k X.toScheme.functionField = 1 := by
  let : Algebra k (X.toScheme.residueField (genericPoint X.toScheme)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ X.structureMap.appTop ≫
      X.toScheme.Γevaluation (genericPoint X.toScheme)).hom.toAlgebra
  have htr : Algebra.trdeg k X.toScheme.functionField =
      Algebra.trdeg k (X.toScheme.residueField (genericPoint X.toScheme)) :=
    (functionFieldAlgEquivGenericResidueField X).trdeg_eq
  have hdim := topologicalKrullDim_eq_trdeg_residueField k X.toScheme X.structureMap
    (genericPoint X.toScheme) (genericPoint_spec X.toScheme)
  rw [isCurve_iff, and_iff_right X.isVariety, hdim, htr]
  refine ⟨fun h => Cardinal.toENat_eq_one.mp (WithBot.coe_inj.mp h), fun h => ?_⟩
  exact_mod_cast Cardinal.toENat_eq_one.mpr h

/-! ### Category (1): finitely generated field extensions of transcendence degree one -/

/-- Having transcendence degree one over `k`: the property of a finitely generated field
extension of `k` which cuts out category (1) of Stacks 0BY1. -/
def HasTrdegOne (k : Type u) [Field k] : ObjectProperty (FinitelyGeneratedFieldExtension k) :=
  fun K ↦ Algebra.trdeg k K.obj = 1

/-- Having transcendence degree one over `k` is invariant under isomorphism of finitely generated
field extensions of `k`. -/
instance hasTrdegOne_isClosedUnderIsomorphisms (k : Type u) [Field k] :
    (HasTrdegOne k).IsClosedUnderIsomorphisms where
  of_iso {_ _} e hK :=
    (CommAlgCat.algEquivOfIso ((ObjectProperty.ι _).mapIso e)).trdeg_eq.symm.trans hK

/-- Category (1) of Stacks 0BY1: the finitely generated field extensions of `k` of transcendence
degree one, a full subcategory of all finitely generated field extensions of `k`. -/
@[ega "II 7.4.17"]
abbrev FinitelyGeneratedFieldExtensionTrdegOne (k : Type u) [Field k] :=
  (HasTrdegOne k).FullSubcategory

/-! ### Category (2): curves and dominant rational maps -/

/-- Being a curve: the property of a variety over `k` which cuts out category (2) of
Stacks 0BY1. -/
def Variety.IsCurveProperty (k : Type u) [Field k] : ObjectProperty (Variety k) :=
  fun X ↦ IsCurve k X.structureMap

/-- Category (2) of Stacks 0BY1: curves over `k` and dominant rational maps, a full subcategory
of the varieties over `k` and dominant rational maps. -/
abbrev Curve (k : Type u) [Field k] := (Variety.IsCurveProperty k).FullSubcategory

/-! ### Categories (1) and (2) -/

/-- Under the function-field functor of Stacks 0BXN the varieties of transcendence degree one are
exactly the curves. This is the comparison of object properties which restricts that
anti-equivalence to categories (1) and (2) of Stacks 0BY1. -/
theorem op_hasTrdegOne_inverseImage_functionFieldFunctor (k : Type u) [Field k] :
    (HasTrdegOne k).op.inverseImage
        (varietyEquivalenceFinitelyGeneratedFieldExtensionOpposite k).functor =
      Variety.IsCurveProperty k :=
  funext fun X ↦ propext (isCurve_iff_trdeg_functionField_eq_one X).symm

/-- **Stacks Project, Tag 0BY1, categories (1) and (2).** Over a field `k`, the category of
curves over `k` and dominant rational maps is anti-equivalent to the category of finitely
generated field extensions of `k` of transcendence degree one.

This is the restriction of the anti-equivalence of Stacks 0BXN,
`AlgebraicGeometry.varietyEquivalenceFinitelyGeneratedFieldExtensionOpposite`, to the varieties
whose function field has transcendence degree one; those are exactly the curves, by
`AlgebraicGeometry.isCurve_iff_trdeg_functionField_eq_one`. -/
@[stacks 0BY1 "the equivalence of categories (1) and (2), as the anti-equivalence of Tag 0BXN \
restricted to transcendence degree one"]
noncomputable def curveEquivalenceFinitelyGeneratedFieldExtensionTrdegOneOpposite
    (k : Type u) [Field k] :
    Curve k ≌ (FinitelyGeneratedFieldExtensionTrdegOne k)ᵒᵖ :=
  ((varietyEquivalenceFinitelyGeneratedFieldExtensionOpposite k).congrFullSubcategory
      (op_hasTrdegOne_inverseImage_functionFieldFunctor k)).trans
    (ObjectProperty.opEquivalence (HasTrdegOne k))

/-! ### Nonconstant morphisms -/

/-- Nonconstant morphisms of schemes over `k`, read as the dominant ones. For a morphism of
curves over `k` this is the reading used by the proof of Stacks 0BY1, which takes a nonconstant
morphism to be one carrying the generic point of the source to the generic point of the target;
for morphisms of integral schemes that is precisely dominance. -/
def nonconstantOver (k : Type u) [Field k] : MorphismProperty (Over (Spec (.of k))) :=
  fun _ _ f ↦ IsDominant f.left

/-- Dominant morphisms of schemes over `k` contain the identities and are closed under
composition. -/
instance nonconstantOver_isMultiplicative (k : Type u) [Field k] :
    (nonconstantOver k).IsMultiplicative where
  id_mem X := by
    change IsDominant (𝟙 X.left)
    infer_instance
  comp_mem {_ _ _} f g hf hg := by
    change IsDominant (f.left ≫ g.left)
    let : IsDominant f.left := hf
    let : IsDominant g.left := hg
    infer_instance

/-- Schemes over `k` and nonconstant morphisms over `k`: the ambient category of categories
(3)–(6) of Stacks 0BY1. -/
abbrev SchemeOverNonconstant (k : Type u) [Field k] := WideSubcategory (nonconstantOver k)

/-! ### Categories (3)–(6): the proper models -/

/-- Being a normal projective curve over `k`: the property cutting out category (3) of
Stacks 0BY1. -/
def IsNormalProjectiveCurve (k : Type u) [Field k] :
    ObjectProperty (SchemeOverNonconstant k) :=
  fun X ↦ IsCurve k X.obj.hom ∧ IsProjectiveMorphism X.obj.hom ∧ IsNormal X.obj.left

/-- Being a regular — equivalently, nonsingular — projective curve over `k`: the property
cutting out categories (4) and (5) of Stacks 0BY1. -/
def IsRegularProjectiveCurve (k : Type u) [Field k] :
    ObjectProperty (SchemeOverNonconstant k) :=
  fun X ↦ IsCurve k X.obj.hom ∧ IsProjectiveMorphism X.obj.hom ∧ IsRegular X.obj.left

/-- Being a normal proper curve over `k`: the property cutting out category (6) of
Stacks 0BY1. -/
def IsNormalProperCurve (k : Type u) [Field k] :
    ObjectProperty (SchemeOverNonconstant k) :=
  fun X ↦ IsCurve k X.obj.hom ∧ IsProper X.obj.hom ∧ IsNormal X.obj.left

/-- Category (3) of Stacks 0BY1: normal projective curves over `k` and nonconstant morphisms. -/
abbrev NormalProjectiveCurve (k : Type u) [Field k] :=
  (IsNormalProjectiveCurve k).FullSubcategory

/-- Category (5) of Stacks 0BY1: regular projective curves over `k` and nonconstant
morphisms. -/
abbrev RegularProjectiveCurve (k : Type u) [Field k] :=
  (IsRegularProjectiveCurve k).FullSubcategory

/-- Category (4) of Stacks 0BY1: nonsingular projective curves over `k` and nonconstant
morphisms. The words "nonsingular" and "regular" are synonyms — `AlgebraicGeometry.IsRegular`,
the predicate of Stacks 02IS, is the formalization of both — so this is not merely equivalent to
category (5) but literally the same category. -/
abbrev NonsingularProjectiveCurve (k : Type u) [Field k] := RegularProjectiveCurve k

/-- Category (6) of Stacks 0BY1: normal proper curves over `k` and nonconstant morphisms. -/
abbrev NormalProperCurve (k : Type u) [Field k] := (IsNormalProperCurve k).FullSubcategory

/-! ### Categories (3), (4) and (5) are the same category -/

/-- A normal projective curve is a regular projective curve, by Stacks 0BX2. -/
@[ega "II 7.4.5" "special case"]
theorem isNormalProjectiveCurve_le_isRegularProjectiveCurve (k : Type u) [Field k] :
    IsNormalProjectiveCurve k ≤ IsRegularProjectiveCurve k := by
  rintro X ⟨hcurve, hproj, hnormal⟩
  exact ⟨hcurve, hproj, (@isRegular_iff_isNormal_of_isCurve k _ _ X.obj.hom hcurve).mpr hnormal⟩

/-- A regular projective curve is a normal projective curve, since a regular scheme is
normal. -/
@[ega "II 7.4.5" "special case"]
theorem isRegularProjectiveCurve_le_isNormalProjectiveCurve (k : Type u) [Field k] :
    IsRegularProjectiveCurve k ≤ IsNormalProjectiveCurve k := by
  rintro X ⟨hcurve, hproj, hregular⟩
  exact ⟨hcurve, hproj, (@isRegular_iff_isNormal_of_isCurve k _ _ X.obj.hom hcurve).mp hregular⟩

/-- **Stacks Project, Tag 0BY1, categories (3) and (5).** The category of normal projective
curves over `k` and nonconstant morphisms and the category of regular projective curves over `k`
and nonconstant morphisms are the same: the equivalence is the inclusion of full subcategories,
which is the identity on underlying schemes and on morphisms, and it is an equivalence because
normality and regularity are the same condition on a curve, Stacks 0BX2
(`AlgebraicGeometry.isRegular_iff_isNormal_of_isCurve`). -/
@[stacks 0BY1 "that categories (3) and (5) are the same category: the inclusion of the normal \
projective curves into the regular projective curves, which is the identity on schemes and on \
morphisms, is an equivalence"]
noncomputable def normalProjectiveCurveEquivalenceRegularProjectiveCurve
    (k : Type u) [Field k] : NormalProjectiveCurve k ≌ RegularProjectiveCurve k :=
  letI : (ObjectProperty.ιOfLE
      (isNormalProjectiveCurve_le_isRegularProjectiveCurve k)).IsEquivalence :=
    (ObjectProperty.isEquivalence_ιOfLE_iff _).mpr
      (le_trans (isRegularProjectiveCurve_le_isNormalProjectiveCurve k)
        (ObjectProperty.le_isoClosure _))
  (ObjectProperty.ιOfLE (isNormalProjectiveCurve_le_isRegularProjectiveCurve k)).asEquivalence

/-- **Stacks Project, Tag 0BY1, categories (4) and (5).** The category of nonsingular projective
curves over `k` and nonconstant morphisms is the category of regular projective curves over `k`
and nonconstant morphisms.

"Nonsingular" and "regular" are synonyms, Stacks 02IS: this library has one predicate,
`AlgebraicGeometry.IsRegular`, formalizing both, so `AlgebraicGeometry.NonsingularProjectiveCurve`
and `AlgebraicGeometry.RegularProjectiveCurve` are the same type and the comparison is the
identity equivalence. The content of the source's claim is the synonymy of the two words, which
is a matter of terminology and not a mathematical statement that can be formalized separately. -/
@[stacks 0BY1 "that categories (4) and (5) are the same category; since `IsRegular` (Tag 02IS) \
formalizes both `nonsingular` and `regular`, the two categories are the same type and this is \
the identity equivalence"]
noncomputable def nonsingularProjectiveCurveEquivalenceRegularProjectiveCurve
    (k : Type u) [Field k] :
    NonsingularProjectiveCurve k ≌ RegularProjectiveCurve k :=
  CategoryTheory.Equivalence.refl

/-! ### Categories (3) and (6) are the same category -/

/-- A normal projective curve is a normal proper curve, since an H-projective morphism is
proper. -/
theorem isNormalProjectiveCurve_le_isNormalProperCurve (k : Type u) [Field k] :
    IsNormalProjectiveCurve k ≤ IsNormalProperCurve k := by
  rintro X ⟨hcurve, hproj, hnormal⟩
  exact ⟨hcurve, isProper_of_isProjectiveMorphism X.obj.hom hproj, hnormal⟩

/-- **A proper curve over a field is H-projective**, with nothing carried.

This is the case of Stacks 0A26 that the proof of Stacks 0BY1 uses. A curve is an *integral*
scheme of dimension exactly one, and for those Tag 0A25 is
`Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral`, whose ample sheaf is the
one of [Stacks, Tag 09ND]. Tag 0A25 holds in general too, as
`Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_dimension_le_one`, with its
ample sheaf from [Stacks, Tag 09NZ],
`Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one`.
Properness then upgrades
H-quasi-projectivity to H-projectivity, which is clause (2) of [Stacks, Tag 0BCL],
`AlgebraicGeometry.isProjectiveMorphism_iff_isHQuasiProjective_and_isProper`. -/
@[ega "II 7.4.12" "special case"]
theorem isProjectiveMorphism_of_isProper_of_isCurve (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] :
    IsProjectiveMorphism f :=
  (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper (f := f)).mpr
    ⟨Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral f
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)), inferInstance⟩

/-- A normal proper curve is a normal projective curve, by
`AlgebraicGeometry.isProjectiveMorphism_of_isProper_of_isCurve`. -/
theorem isNormalProperCurve_le_isNormalProjectiveCurve (k : Type u) [Field k] :
    IsNormalProperCurve k ≤ IsNormalProjectiveCurve k := by
  rintro X ⟨hcurve, hproper, hnormal⟩
  exact ⟨hcurve, @isProjectiveMorphism_of_isProper_of_isCurve k _ _ X.obj.hom hcurve hproper,
    hnormal⟩

/-- **Stacks Project, Tag 0BY1, categories (3) and (6).** The category of normal projective
curves over `k` and nonconstant morphisms and the category of normal proper curves over `k` and
nonconstant morphisms are the same: the equivalence is the inclusion of full subcategories,
which is the identity on underlying schemes and on morphisms, and it is an equivalence because a
proper curve is projective, the case of Stacks 0A26 proved outright in
`AlgebraicGeometry.isProjectiveMorphism_of_isProper_of_isCurve`. -/
@[stacks 0BY1 "that categories (3) and (6) are the same category: the inclusion of the normal \
projective curves into the normal proper curves, which is the identity on schemes and on \
morphisms, is an equivalence"]
noncomputable def normalProjectiveCurveEquivalenceNormalProperCurve
    (k : Type u) [Field k] : NormalProjectiveCurve k ≌ NormalProperCurve k :=
  letI : (ObjectProperty.ιOfLE
      (isNormalProjectiveCurve_le_isNormalProperCurve k)).IsEquivalence :=
    (ObjectProperty.isEquivalence_ιOfLE_iff _).mpr
      (le_trans (isNormalProperCurve_le_isNormalProjectiveCurve k)
        (ObjectProperty.le_isoClosure _))
  (ObjectProperty.ιOfLE (isNormalProjectiveCurve_le_isNormalProperCurve k)).asEquivalence

/-! ### Categories (2) and (3) -/

/-- The functor from normal projective curves over `k` and nonconstant morphisms to curves over
`k` and dominant rational maps: a normal projective curve is in particular a curve, and a
nonconstant — that is, dominant — morphism has a dominant rational map. -/
noncomputable def normalProjectiveCurveToCurve (k : Type u) [Field k] :
    NormalProjectiveCurve k ⥤ Curve k where
  obj X :=
    letI : IsCurve k X.obj.obj.hom := X.property.1
    ⟨{ toScheme := X.obj.obj.left, structureMap := X.obj.obj.hom }, X.property.1⟩
  map {X Y} f :=
    letI : IsCurve k X.obj.obj.hom := X.property.1
    letI : IsCurve k Y.obj.obj.hom := Y.property.1
    letI : IsDominant f.hom.hom.left := f.hom.property
    ObjectProperty.homMk ⟨f.hom.hom.left.toRationalMap⟩
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Variety.Hom.ext
    change (Scheme.PartialMap.id X.obj.obj.left).toRationalMap = _
    rfl
  map_comp {X Y Z} f g := by
    let _ : IsCurve k X.obj.obj.hom := X.property.1
    let _ : IsCurve k Y.obj.obj.hom := Y.property.1
    let _ : IsCurve k Z.obj.obj.hom := Z.property.1
    let _ : IsDominant f.hom.hom.left := f.hom.property
    let _ : IsDominant g.hom.hom.left := g.hom.property
    apply ObjectProperty.hom_ext
    apply Variety.Hom.ext
    change (Scheme.Hom.toPartialMap (f.hom.hom.left ≫ g.hom.hom.left)).toRationalMap =
      (Scheme.Hom.toPartialMap f.hom.hom.left).toRationalMap.comp
        (Scheme.Hom.toPartialMap g.hom.hom.left).toRationalMap
    rw [← Scheme.Hom.toPartialMap_compHom, ← Scheme.PartialMap.comp_toPartialMap,
      ← Scheme.RationalMap.toRationalMap_comp]

/-- The functor of `AlgebraicGeometry.normalProjectiveCurveToCurve` is faithful: a morphism of
normal projective curves is determined by its rational map, Stacks 0BXZ. -/
instance normalProjectiveCurveToCurve_faithful (k : Type u) [Field k] :
    (normalProjectiveCurveToCurve k).Faithful where
  map_injective {X Y} f g h := by
    let _ : IsCurve k X.obj.obj.hom := X.property.1
    let _ : IsNormal X.obj.obj.left := X.property.2.2
    let _ : IsCurve k Y.obj.obj.hom := Y.property.1
    let _ : IsProjectiveVariety k Y.obj.obj.hom := ⟨Y.property.2.1⟩
    have hrat : f.hom.hom.left.toRationalMap = g.hom.hom.left.toRationalMap := by
      simpa [normalProjectiveCurveToCurve] using
        congrArg (fun q : (normalProjectiveCurveToCurve k).obj X ⟶
          (normalProjectiveCurveToCurve k).obj Y => q.hom.toRationalMap) h
    exact ObjectProperty.hom_ext _ (WideSubcategory.hom_ext _
      ((toRationalMap_bijective k X.obj.obj Y.obj.obj).1 (Subtype.ext hrat)))

/-- The functor of `AlgebraicGeometry.normalProjectiveCurveToCurve` is full: every dominant
rational map of normal projective curves is the rational map of a nonconstant morphism,
Stacks 0BXZ. -/
instance normalProjectiveCurveToCurve_full (k : Type u) [Field k] :
    (normalProjectiveCurveToCurve k).Full where
  map_surjective {X Y} f := by
    let _ : IsCurve k X.obj.obj.hom := X.property.1
    let _ : IsNormal X.obj.obj.left := X.property.2.2
    let _ : IsCurve k Y.obj.obj.hom := Y.property.1
    let _ : IsProjectiveVariety k Y.obj.obj.hom := ⟨Y.property.2.1⟩
    let _ : f.hom.toRationalMap.IsOver (Spec (.of k)) := f.hom.isOver
    let _ : f.hom.toRationalMap.IsDominant := f.hom.isDominant
    obtain ⟨m, hm⟩ := (toRationalMap_bijective k X.obj.obj Y.obj.obj).2
      ⟨f.hom.toRationalMap, f.hom.isOver⟩
    have hrat : m.left.toRationalMap = f.hom.toRationalMap := congrArg Subtype.val hm
    have hdomR : m.left.toPartialMap.toRationalMap.IsDominant := by
      change m.left.toRationalMap.IsDominant
      rw [hrat]
      exact f.hom.isDominant
    have hdom : IsDominant m.left := by
      have hdomP : IsDominant m.left.toPartialMap.hom :=
        (Scheme.PartialMap.isDominant_toRationalMap_iff _).mp hdomR
      change IsDominant (X.obj.obj.left.topIso.hom ≫ m.left) at hdomP
      exact IsDominant.of_comp X.obj.obj.left.topIso.hom m.left
    exact ⟨ObjectProperty.homMk ⟨m, hdom⟩, ObjectProperty.hom_ext _ (Variety.Hom.ext _ _ hrat)⟩

/-- **Stacks Project, Tag 0BY1, the fully faithful functor from category (3) to category (2).**
Over a field `k`, passing from a normal projective curve and its nonconstant morphisms to the
same curve and the rational maps of those morphisms is a fully faithful functor from category (3)
to category (2).

This is the source's step "there is a fully faithful functor (5) → (1)", transported along the
identification of category (3) with category (5) and along the anti-equivalence of categories (1)
and (2); both halves are Stacks 0BXZ,
`AlgebraicGeometry.toRationalMap_bijective` — morphisms from a normal curve to a proper variety
are exactly the rational maps over the base field — applied to the normal curve `X` and the
projective, hence proper, curve `Y`.

Essential surjectivity of this functor is `AlgebraicGeometry.normalProjectiveCurveToCurve_essSurj`
below, and the two together are the equivalence
`AlgebraicGeometry.normalProjectiveCurveEquivalenceCurve`; this declaration is the fully faithful
half alone. -/
@[stacks 0BY1 "only that the functor from category (3) to category (2) is fully faithful, which \
is the source's step `there is a fully faithful functor (5) to (1)`. Essential surjectivity of \
that functor — the source's final paragraph, that every finitely generated field extension of \
transcendence degree one is the function field of a normal projective curve — is NOT proved \
here, so this does not cover the equivalence of categories (2) and (3)"]
noncomputable def normalProjectiveCurveToCurveFullyFaithful (k : Type u) [Field k] :
    (normalProjectiveCurveToCurve k).FullyFaithful :=
  .ofFullyFaithful _

/-! ### Categories (2) and (3): essential surjectivity -/

/-- A dominant morphism of varieties over `k` induces a map of function fields which is a map of
`k`-algebras: both structure maps are the germ at the generic point of the global sections of the
structure morphism, and the morphism is over `k`. -/
theorem functionFieldMap_functionFieldAlgebraMap (V W : Variety k)
    (g : V.toScheme ⟶ W.toScheme) [IsDominant g]
    (hg : g ≫ W.structureMap = V.structureMap) (a : k) :
    (Scheme.Hom.functionFieldMap g).hom (algebraMap k W.toScheme.functionField a) =
      algebraMap k V.toScheme.functionField a := by
  let _ : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨genericPoint V.toScheme, trivial⟩⟩
  let _ : Nonempty (⊤ : W.toScheme.Opens) := ⟨⟨genericPoint W.toScheme, trivial⟩⟩
  have hle : (⊤ : V.toScheme.Opens) ≤ g ⁻¹ᵁ (⊤ : W.toScheme.Opens) := by simp
  have happ : g.appLE ⊤ ⊤ hle = g.appTop := by
    rw [Scheme.Hom.appLE,
      show (homOfLE hle) = 𝟙 (⊤ : V.toScheme.Opens) from Subsingleton.elim _ _]
    simp only [TopologicalSpace.Opens.map_top, op_id, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hstruct : V.structureMap.appTop = W.structureMap.appTop ≫ g.appTop := by
    rw [← hg, Scheme.Hom.comp_appTop]
  have hV := DFunLike.congr_fun (functionFieldAlgebraMap_eq_germToFunctionField V) a
  have hW := DFunLike.congr_fun (functionFieldAlgebraMap_eq_germToFunctionField W) a
  change (Scheme.Hom.functionFieldMap g).hom (functionFieldAlgebraMap W a) =
    functionFieldAlgebraMap V a
  rw [hV, hW]
  change (Scheme.Hom.functionFieldMap g)
      (W.toScheme.germToFunctionField ⊤ ((W.structureMap.appTop).hom
        (((Scheme.ΓSpecIso (.of k)).inv).hom a))) = _
  rw [Scheme.Hom.functionFieldMap_germToFunctionField g hle, happ, hstruct]
  rfl

/-- A dominant morphism of varieties over `k` inducing an isomorphism of function fields is an
isomorphism in the category of varieties over `k` and dominant rational maps: the function-field
functor of Stacks 0BXN is fully faithful. -/
noncomputable def varietyIsoOfIsIsoFunctionFieldMap {V W : Variety k}
    (g : V.toScheme ⟶ W.toScheme) [IsDominant g]
    (hg : g ≫ W.structureMap = V.structureMap)
    (hiso : IsIso (Scheme.Hom.functionFieldMap g)) : V ≅ W := by
  letI : IsIso (Scheme.Hom.functionFieldMap g) := hiso
  have hbij : Function.Bijective (Scheme.Hom.functionFieldMap g).hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.Hom.functionFieldMap g)
  let e : W.toScheme.functionField ≃ₐ[k] V.toScheme.functionField :=
    AlgEquiv.ofRingEquiv (R := k) (f := RingEquiv.ofBijective _ hbij)
      (functionFieldMap_functionFieldAlgebraMap V W g hg)
  have α : functionFieldObject W ≅ functionFieldObject V :=
    ObjectProperty.isoMk (fun A : CommAlgCat k ↦ IsField A ∧ Algebra.EssFiniteType k A)
      (CommAlgCat.isoMk e)
  exact (functionFieldFunctor k).preimageIso α.op

/-- The extension of function fields of a dominant open immersion of integral schemes is an
isomorphism: the generic point of the source maps to the generic point of the target and the
stalk map of an open immersion is an isomorphism. -/
theorem isIso_functionFieldMap_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsOpenImmersion j] [IsDominant j] :
    IsIso (Scheme.Hom.functionFieldMap j) := by
  have hspec : Y.presheaf.stalkSpecializes (specializes_genericPoint_of_isDominant j) =
      (Y.presheaf.stalkCongr (Inseparable.of_eq
        (genericPoint_eq_of_isDominant j).symm)).hom := rfl
  let _ : IsIso (j.stalkMap (genericPoint X)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
  rw [Scheme.Hom.functionFieldMap, hspec]
  infer_instance

/-- **A curve over `k` is a dense open subscheme of a projective curve over `k`**, with nothing
carried.

The compactification is the one of [Stacks, Tag 0BXV],
`Stacks.CurveProjectiveCompletion.exists_projective_completion_aux_of_isHQuasiProjective`, whose
only input beyond the hypotheses here is [Stacks, Tag 0A25]; for an *integral* scheme of
dimension one that input is proved outright by
`Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral`, so [Stacks, Tag 09NZ] is
not needed. The compactification is again a curve: irreducible because the open immersion is
dominant, reduced because its image is scheme-theoretically dense and `X` is reduced
([Stacks, Tag 056E]), and of dimension one because its dimension is at most one and at least the
dimension of the open subscheme. -/
@[ega "III 5.2.6" "curves over a field"]
theorem exists_isCurve_isProjectiveMorphism_isOpenImmersion (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsCurve k p] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)) (j : X ⟶ Y) (_ : IsOpenImmersion j)
      (_ : IsDominant j), j ≫ q = p ∧ IsCurve k q ∧ IsProjectiveMorphism q := by
  have hdimX : topologicalKrullDim (X : Type u) = 1 :=
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := p)
  obtain ⟨Y, q, j, hj, hjq, hproj, hqft, hdimY, hdom, hstd, -, -⟩ :=
    Stacks.CurveProjectiveCompletion.exists_projective_completion_aux_of_isHQuasiProjective k p
      (Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral p hdimX) hdimX.le
  let _ : IsOpenImmersion j := hj
  let _ : IsDominant j := hdom
  have _ : IsProper q := isProper_of_isProjectiveMorphism q hproj
  let _ : IsReduced j.opensRange.toScheme := isReduced_of_isOpenImmersion j.isoOpensRange.inv
  let _ : IsReduced Y := isReduced_of_isSchemeTheoreticallyDense j.opensRange hstd
  let _ : IrreducibleSpace Y := irreducibleSpace_of_isDominant j
  let _ : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  have hdim : topologicalKrullDim (Y : Type u) = 1 :=
    le_antisymm hdimY (hdimX ▸ Topology.IsInducing.topologicalKrullDim_le
      (f := (j.base : X → Y)) j.isOpenEmbedding.isEmbedding.isInducing)
  let _ : IsCurve k q :=
    { toIsVariety := { }
      topologicalKrullDim_eq_one := hdim }
  exact ⟨Y, q, j, hj, hdom, hjq, inferInstance, hproj⟩

/-- **Stacks Project, Tag 0BY1, essential surjectivity of the functor from category (3) to
category (2)**: every curve over `k` is isomorphic, in the category of curves and dominant
rational maps, to a normal projective curve.

This is the source's final paragraph, in the order of its own remark: compactify, then normalize.
A curve `X` is a dense open subscheme of a projective curve `Y` over `k` by
`AlgebraicGeometry.exists_isCurve_isProjectiveMorphism_isOpenImmersion`. The normalization of `Y`
is a variety over `k` ([Stacks, Tag 0BXR]) which is normal, proper over `k` ([Stacks, Tag 0GK4],
the normalization being finite) and again one-dimensional, so it is a normal *proper* curve,
hence a normal *projective* curve by
`AlgebraicGeometry.isProjectiveMorphism_of_isProper_of_isCurve`. Both the open immersion and the
normalization morphism are dominant and induce isomorphisms of function fields, so both are
isomorphisms in the category of varieties and dominant rational maps, the function-field functor
of [Stacks, Tag 0BXN] being fully faithful. -/
instance normalProjectiveCurveToCurve_essSurj (k : Type u) [Field k] :
    (normalProjectiveCurveToCurve k).EssSurj where
  mem_essImage C := by
    let _ : IsCurve k C.obj.structureMap := C.property
    obtain ⟨Y, q, j, hj, hdom, hjq, hcq, hproj⟩ :=
      exists_isCurve_isProjectiveMorphism_isOpenImmersion k C.obj.structureMap
    let _ : IsOpenImmersion j := hj
    let _ : IsDominant j := hdom
    let _ : IsCurve k q := hcq
    have _ : IsProper q := isProper_of_isProjectiveMorphism q hproj
    let _ : IsVariety k (normalizationOverField k q ≫ q) := isVariety_normalizationOverField k q
    let _ : IsProper (normalizationOverField k q ≫ q) :=
      isProper_normalizationOverField_comp k q
    let _ : IsDominant (normalizationOverField k q) := isDominant_normalizationOverField k q
    let _ : IsNormal (normalizationSchemeOverField k q) :=
      Scheme.isNormal_normalizationScheme Y
        (finite_irreducibleComponents_of_locallyOfFiniteType k q)
    let _ : IsCurve k (normalizationOverField k q ≫ q) :=
      { topologicalKrullDim_eq_one :=
          (topologicalKrullDim_normalizationSchemeOverField k q).trans
            (IsCurve.topologicalKrullDim_eq_one (k := k) (f := q)) }
    let _ : IsProjectiveMorphism (normalizationOverField k q ≫ q) :=
      isProjectiveMorphism_of_isProper_of_isCurve k (normalizationOverField k q ≫ q)
    let VY : Variety k := { toScheme := Y, structureMap := q }
    let VN : Variety k :=
      { toScheme := normalizationSchemeOverField k q
        structureMap := normalizationOverField k q ≫ q }
    refine ⟨⟨⟨Over.mk (normalizationOverField k q ≫ q)⟩,
      ⟨‹IsCurve k (normalizationOverField k q ≫ q)›,
        ‹IsProjectiveMorphism (normalizationOverField k q ≫ q)›,
        ‹IsNormal (normalizationSchemeOverField k q)›⟩⟩, ⟨?_⟩⟩
    refine (ObjectProperty.ι (Variety.IsCurveProperty k)).preimageIso ?_
    exact (varietyIsoOfIsIsoFunctionFieldMap (V := VN) (W := VY)
          (normalizationOverField k q) rfl
          (isIso_functionFieldMap_normalizationOverField k q)).trans
      (varietyIsoOfIsIsoFunctionFieldMap (V := C.obj) (W := VY) j hjq
        (isIso_functionFieldMap_of_isOpenImmersion j)).symm

/-- The functor from category (3) to category (2) is an equivalence: it is fully faithful by
Stacks 0BXZ and essentially surjective by
`AlgebraicGeometry.normalProjectiveCurveToCurve_essSurj`. -/
instance normalProjectiveCurveToCurve_isEquivalence (k : Type u) [Field k] :
    (normalProjectiveCurveToCurve k).IsEquivalence where

/-- **Stacks Project, Tag 0BY1, categories (2) and (3).** Over a field `k`, the category of
normal projective curves over `k` and nonconstant morphisms is equivalent to the category of
curves over `k` and dominant rational maps.

The functor is the one of `AlgebraicGeometry.normalProjectiveCurveToCurve`; it is fully faithful
by [Stacks, Tag 0BXZ] and essentially surjective by
`AlgebraicGeometry.normalProjectiveCurveToCurve_essSurj`. Together with the anti-equivalence of
categories (1) and (2) and the identifications of categories (3), (4), (5) and (6), all six
categories of the source are equivalent. -/
@[stacks 0BY1 "the equivalence of categories (2) and (3): the functor of \
`AlgebraicGeometry.normalProjectiveCurveToCurve`, fully faithful by Tag 0BXZ and essentially \
surjective by `AlgebraicGeometry.normalProjectiveCurveToCurve_essSurj`, which is the source's \
final paragraph — every curve over `k` is birational to a normal projective curve, obtained by \
compactifying (Tag 0BXV, outright for an integral scheme of dimension one) and then normalizing \
(Tag 0BXR, proper by Tag 0GK4)"]
noncomputable def normalProjectiveCurveEquivalenceCurve (k : Type u) [Field k] :
    NormalProjectiveCurve k ≌ Curve k :=
  (normalProjectiveCurveToCurve k).asEquivalence

end AlgebraicGeometry

end
