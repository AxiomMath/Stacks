module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.FiberRankIsomorphismInvariant
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneInvertibleOpen

/-!
# Restriction is an equivalence on rank one coherent reflexive modules

Let `X` be an integral locally Noetherian normal scheme and let `V ⊆ X` be an open subscheme
every irreducible component of whose complement has codimension at least two in `X`.  Then
restriction along `V ⟶ X` is an **equivalence of categories** between the rank one coherent
reflexive `𝒪_X`-modules and the rank one coherent reflexive `𝒪_V`-modules.

This is the step on which the colimit assertion of [Stacks, Tag
0EBN](https://stacks.math.columbia.edu/tag/0EBN) turns.  The source's proof of Tag 0EBN uses it
twice — once for the pair `X ⊇ V`, once for the pair `U ⊇ V ∩ U` where `U ⊆ X` is the open
subscheme on which the given section is an isomorphism — so everything below is stated for an
*arbitrary* integral locally Noetherian normal scheme together with an *arbitrary* open whose
complement has codimension at least two.  Both uses of the source are instances.

## Main definitions

* `AlgebraicGeometry.CoherentReflexive.coherentReflexiveForget`: the underlying `𝒪_X`-module of
  a coherent reflexive module, as a functor; `rankOneForget` is the same for the rank one
  modules and `rankOneForgetFullyFaithful` says it is fully faithful.
* `AlgebraicGeometry.CoherentReflexive.flattenEquiv`: the two presentations of the category of
  coherent reflexive modules that meet here agree.
* `AlgebraicGeometry.CoherentReflexive.coherentReflexiveRestrictEquiv`: [Stacks, Tag 0EBJ] on
  the nested presentation of the category of coherent reflexive modules.
* `AlgebraicGeometry.CoherentReflexive.rankOneRestrictFunctor`: **restriction**, as a functor
  from the rank one coherent reflexive `𝒪_X`-modules to the rank one coherent reflexive
  `𝒪_V`-modules; `rankOneRestrictFunctorForgetIso` says that on underlying modules it is
  `Scheme.Modules.restrictFunctor`, on the nose.
* `AlgebraicGeometry.CoherentReflexive.rankOneCodimTwoRestrictEquiv`: **the equivalence in the
  form the source uses it**, from the codimension hypothesis on a normal scheme.  Its functor is
  `rankOneRestrictFunctor`.

## Main results

* `AlgebraicGeometry.CoherentReflexive.fiberRank_genericPoint_coherentReflexiveRestrict`: the
  equivalence of [Stacks, Tag 0EBJ] does not change the fibre rank at the generic point, so by
  `hasRankOne_inverseImage` it both preserves and reflects rank one.
* `AlgebraicGeometry.CoherentReflexive.isEquivalence_rankOneCodimTwoRestrictFunctor`: **the
  restriction functor itself is an equivalence**, and
  `rankOneCodimTwoRestrictEquiv_functor` records that the functor of
  `rankOneCodimTwoRestrictEquiv` is that restriction functor.  Without these the equivalence
  would not identify the restriction functor and so would not be the assertion of the source.

## Method

[Stacks, Tag 0EBJ] — `Stacks.AlgebraicGeometry.ReflexiveModules.reflexiveCoherentEquivalence`
— already gives the equivalence on *all* coherent reflexive modules, from the hypothesis that
the structure sheaf has depth at least two at every point off the open.  Serre's criterion
[Stacks, Tag 0345] turns the codimension hypothesis into that depth hypothesis on a normal
scheme; that step is
`AlgebraicGeometry.two_le_depth_stalk_of_notMem_of_two_le_codimension`.

What has to be added is that the equivalence carries the *rank one* subcategory to the rank one
subcategory and back.  The fibre rank at the generic point is unchanged by restriction
(`AlgebraicGeometry.fiberRank_genericPoint_restrict`, an open immersion of integral schemes
carrying the generic point to the generic point) and is an isomorphism invariant
(`AlgebraicGeometry.Scheme.Modules.fiberRank_eq_of_iso`); the functor of Tag 0EBJ is only
*naturally isomorphic* to restriction, not equal to it, which is why the second ingredient is
needed.  Together they say that rank one is the inverse image of rank one along the functor, and
`CategoryTheory.Equivalence.congrFullSubcategory` then cuts the equivalence down to the full
subcategories.

Two presentations of the category of coherent reflexive modules meet here: Tag 0EBJ is stated
for the flattened one, `Stacks.AlgebraicGeometry.ReflexiveModules.ReflexiveCoherentModules`,
while the rank one modules are a full subcategory of the nested one,
`Stacks.AlgebraicGeometry.ReflexiveHull.CoherentReflexiveModules`.  They are exchanged by the
existing `Stacks.AlgebraicGeometry.ReflexiveModules.coherentReflexiveModulesEquiv`, and no new
bridge is introduced.

**No Stacks attribute is attached in this file.**  The assertion proved here is a step inside
the proofs of Tags 0EBL, 0EBM and 0EBN and is not the whole of any tag; the tag for the
equivalence on all coherent reflexive modules, 0EBJ, is already carried by
`Stacks.AlgebraicGeometry.ReflexiveModules.reflexiveCoherentEquivalence`.

## References

* [Stacks Project, Tag 0345](https://stacks.math.columbia.edu/tag/0345)
* [Stacks Project, Tag 0AY6](https://stacks.math.columbia.edu/tag/0AY6)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive ReflexiveCoherentModules
  reflexiveCoherentEquivalence)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentReflexiveModules)

universe u

namespace AlgebraicGeometry.CoherentReflexive

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-! ### The underlying module -/

/-- The underlying `𝒪_X`-module of a coherent reflexive module, as a functor.  Objects of
`CoherentReflexiveModules X` are modules carrying two proofs, so this forgets only proofs. -/
def coherentReflexiveForget (X : Scheme.{u}) : CoherentReflexiveModules X ⥤ X.Modules where
  obj F := F.obj.obj
  map f := f.hom.hom

/-- The underlying `𝒪_X`-module of a rank one coherent reflexive module, as a functor. -/
def rankOneForget (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    RankOneReflexiveModules X ⥤ X.Modules :=
  ObjectProperty.ι _ ⋙ coherentReflexiveForget X

/-- The underlying `𝒪_X`-module functor on rank one coherent reflexive modules is fully
faithful: on either side a morphism is a morphism of `𝒪_X`-modules, and the three layers of
full subcategory only carry proofs. -/
def rankOneForgetFullyFaithful (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    (rankOneForget X).FullyFaithful where
  preimage f := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk f))

/-- **Rank one is an isomorphism-invariant property** of a coherent reflexive module: isomorphic
modules have the same fibre rank at the generic point. -/
instance isClosedUnderIsomorphisms_hasRankOne (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun F : CoherentReflexiveModules X => HasRankOne F) where
  of_iso {_ _} e hA :=
    (Scheme.Modules.fiberRank_eq_of_iso ((coherentReflexiveForget X).mapIso e).symm
      (genericPoint X)).trans hA

/-! ### Flattening the nested presentation

The rank one modules are a full subcategory of
`Stacks.AlgebraicGeometry.ReflexiveHull.CoherentReflexiveModules`, the reflexive objects inside
the coherent modules, whereas [Stacks, Tag 0EBJ] quantifies over
`Stacks.AlgebraicGeometry.ReflexiveModules.ReflexiveCoherentModules`, the full subcategory of
*all* modules cut out by "coherent and reflexive".  Both use the same coherence predicate, so
the two differ only in how the proofs they carry are nested and the comparison is the identity
on underlying modules and on morphisms. -/

/-- From the nested presentation of the category of coherent reflexive modules to the flattened
one. -/
def flattenFunctor (X : Scheme.{u}) :
    CoherentReflexiveModules X ⥤ ReflexiveCoherentModules X where
  obj F := ⟨F.obj.obj, F.obj.property, F.property⟩
  map f := ⟨f.hom.hom⟩

/-- From the flattened presentation of the category of coherent reflexive modules to the nested
one. -/
def nestFunctor (X : Scheme.{u}) :
    ReflexiveCoherentModules X ⥤ CoherentReflexiveModules X where
  obj F := ⟨⟨F.obj, F.property.1⟩, F.property.2⟩
  map f := ⟨⟨f.hom⟩⟩

/-- **The nested and the flattened presentations of the category of coherent reflexive modules
agree.**  On either side an object is a module carrying proofs and a morphism is a morphism of
`𝒪_X`-modules, so the two functors are mutually inverse on the nose. -/
def flattenEquiv (X : Scheme.{u}) :
    CoherentReflexiveModules X ≌ ReflexiveCoherentModules X where
  functor := flattenFunctor X
  inverse := nestFunctor X
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-! ### The equivalence from a depth hypothesis -/

section Depth

variable (V : X.Opens) [IsIntegral V.toScheme] [IsLocallyNoetherian V.toScheme]
  (hdepth : ∀ x : X, x ∉ (V : Set X) →
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))

/-- **[Stacks, Tag 0EBJ] on the nested presentation of the category of coherent reflexive
modules.**  Restriction to an open subscheme off which the structure sheaf has depth at least two
is an equivalence of categories; this is that equivalence, transported from the flattened
presentation in which the source's statement is proved. -/
def coherentReflexiveRestrictEquiv :
    CoherentReflexiveModules X ≌ CoherentReflexiveModules V.toScheme :=
  (flattenEquiv X).trans
    (((reflexiveCoherentEquivalence X V hdepth).1).trans (flattenEquiv V.toScheme).symm)

/-- **The functor of `coherentReflexiveRestrictEquiv` is restriction**, naturally in the module.
Both presentation bridges are the identity on underlying modules, so this is the natural
isomorphism that [Stacks, Tag 0EBJ] supplies alongside its equivalence, composed with the
comparison of restriction and pullback. -/
def coherentReflexiveRestrictForgetIso :
    (coherentReflexiveRestrictEquiv V hdepth).functor ⋙ coherentReflexiveForget V.toScheme ≅
      coherentReflexiveForget X ⋙ Scheme.Modules.restrictFunctor V.ι :=
  (flattenFunctor X).isoWhiskerLeft (reflexiveCoherentEquivalence X V hdepth).2.1 ≪≫
    (coherentReflexiveForget X).isoWhiskerLeft
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm

variable [IsDominant V.ι]

omit [IsLocallyNoetherian V.toScheme] in
/-- **The equivalence of [Stacks, Tag 0EBJ] does not change the fibre rank at the generic
point.**  Its functor is restriction up to isomorphism, the fibre rank is an isomorphism
invariant, and an open immersion of integral schemes carries the generic point to the generic
point. -/
theorem fiberRank_genericPoint_coherentReflexiveRestrict (A : CoherentReflexiveModules X) :
    Scheme.Modules.fiberRank
        (((coherentReflexiveRestrictEquiv V hdepth).functor.obj A).obj.obj)
        (genericPoint V.toScheme) =
      Scheme.Modules.fiberRank A.obj.obj (genericPoint X) := by
  set M : X.Modules := (coherentReflexiveForget X).obj A with hM
  have hcoh : _root_.SheafOfModules.IsCoherent M := A.obj.property
  have : (M.restrict V.ι).IsCoherent :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isCoherent X V M hcoh
  have : M.IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  have : (M.restrict V.ι).IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  refine (Scheme.Modules.fiberRank_eq_of_iso
    ((coherentReflexiveRestrictForgetIso V hdepth).app A) (genericPoint V.toScheme)).trans ?_
  exact fiberRank_genericPoint_restrict V.ι M

omit [IsLocallyNoetherian V.toScheme] in
/-- **Rank one is exactly the inverse image of rank one** along the functor of [Stacks, Tag
0EBJ]: the functor both preserves and reflects rank one, because it does not change the fibre
rank at the generic point. -/
theorem hasRankOne_inverseImage :
    ObjectProperty.inverseImage (fun F : CoherentReflexiveModules V.toScheme => HasRankOne F)
        (coherentReflexiveRestrictEquiv V hdepth).functor =
      (fun F : CoherentReflexiveModules X => HasRankOne F) := by
  funext A
  exact congrArg (fun n : ℕ => n = 1)
    (fiberRank_genericPoint_coherentReflexiveRestrict V hdepth A)

/-- **Restriction is an equivalence of categories between the rank one coherent reflexive
modules on `X` and those on an open subscheme off which the structure sheaf has depth at least
two.**  The equivalence of [Stacks, Tag 0EBJ] carries rank one to rank one and back, so it cuts
down to the full subcategories. -/
def rankOneRestrictEquiv :
    RankOneReflexiveModules X ≌ RankOneReflexiveModules V.toScheme :=
  (coherentReflexiveRestrictEquiv V hdepth).congrFullSubcategory
    (hasRankOne_inverseImage V hdepth)

/-- **The functor of `rankOneRestrictEquiv` is restriction**, naturally in the module.  The
functor of `CategoryTheory.Equivalence.congrFullSubcategory` is the ambient functor read on the
subcategory, so this is `coherentReflexiveRestrictForgetIso` whiskered by the inclusion. -/
def rankOneRestrictForgetIso :
    (rankOneRestrictEquiv V hdepth).functor ⋙ rankOneForget V.toScheme ≅
      rankOneForget X ⋙ Scheme.Modules.restrictFunctor V.ι :=
  (ObjectProperty.ι (fun F : CoherentReflexiveModules X => HasRankOne F)).isoWhiskerLeft
    (coherentReflexiveRestrictForgetIso V hdepth)

/-! ### The restriction functor itself is an equivalence

`rankOneRestrictEquiv` is built from [Stacks, Tag 0EBJ], whose functor is only *naturally
isomorphic* to restriction.  Below, restriction itself is assembled as a functor between the two
categories of rank one coherent reflexive modules and shown to be an equivalence, so that no
identification is needed to read the conclusion. -/

omit [IsIntegral V.toScheme] [IsLocallyNoetherian V.toScheme] [IsDominant V.ι] in
/-- The restriction of a rank one coherent reflexive module is coherent. -/
theorem isCoherent_restrict_rankOne (A : RankOneReflexiveModules X) :
    (((rankOneForget X).obj A).restrict V.ι).IsCoherent :=
  Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isCoherent X V _
    A.obj.obj.property

omit [IsIntegral V.toScheme] [IsLocallyNoetherian V.toScheme] [IsDominant V.ι] in
/-- The restriction of a rank one coherent reflexive module is reflexive: reflexivity of a
coherent module is a condition on stalks, and the stalks of a restriction are stalks of the
module. -/
theorem isReflexive_restrict_rankOne (A : RankOneReflexiveModules X) :
    IsReflexive (((rankOneForget X).obj A).restrict V.ι) :=
  Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_restrict_of_isOpenImmersion V.ι _
    A.obj.obj.property A.obj.property

omit [IsLocallyNoetherian V.toScheme] in
/-- The restriction of a rank one coherent reflexive module has rank one: an open immersion of
integral schemes carries the generic point to the generic point. -/
theorem fiberRank_genericPoint_restrict_rankOne (A : RankOneReflexiveModules X) :
    Scheme.Modules.fiberRank (((rankOneForget X).obj A).restrict V.ι)
      (genericPoint V.toScheme) = 1 := by
  have hcoh : ((rankOneForget X).obj A).IsCoherent := A.obj.obj.property
  have : (((rankOneForget X).obj A).restrict V.ι).IsCoherent := isCoherent_restrict_rankOne V A
  have : ((rankOneForget X).obj A).IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  have : (((rankOneForget X).obj A).restrict V.ι).IsFiniteType :=
    _root_.IsCoherent.toIsFiniteType _
  exact (fiberRank_genericPoint_restrict V.ι _).trans A.property

/-- **Restriction, as a functor from the rank one coherent reflexive `𝒪_X`-modules to the rank
one coherent reflexive `𝒪_V`-modules.**  Restriction preserves coherence, reflexivity and the
fibre rank at the generic point, so the restriction functor on modules lifts through the three
layers of full subcategory. -/
def rankOneRestrictFunctor :
    RankOneReflexiveModules X ⥤ RankOneReflexiveModules V.toScheme :=
  ObjectProperty.lift _
    (ObjectProperty.lift _
      (ObjectProperty.lift _ (rankOneForget X ⋙ Scheme.Modules.restrictFunctor V.ι)
        (isCoherent_restrict_rankOne V))
      (isReflexive_restrict_rankOne V))
    (fiberRank_genericPoint_restrict_rankOne V)

/-- **`rankOneRestrictFunctor` is restriction**: read on underlying modules it is literally the
restriction functor, with no comparison isomorphism intervening. -/
def rankOneRestrictFunctorForgetIso :
    rankOneRestrictFunctor V ⋙ rankOneForget V.toScheme ≅
      rankOneForget X ⋙ Scheme.Modules.restrictFunctor V.ι :=
  Iso.refl _

/-- **Restriction agrees with the functor of the equivalence built from [Stacks, Tag 0EBJ]**,
naturally in the module.  The underlying-module functor is fully faithful, so the natural
isomorphism of `rankOneRestrictForgetIso` lifts from the modules to the categories. -/
def rankOneRestrictFunctorIsoEquivFunctor :
    rankOneRestrictFunctor V ≅ (rankOneRestrictEquiv V hdepth).functor :=
  ((rankOneForgetFullyFaithful V.toScheme).whiskeringRight
    (RankOneReflexiveModules X)).preimageIso (rankOneRestrictForgetIso V hdepth).symm

include hdepth in
/-- **Restriction to an open subscheme off which the structure sheaf has depth at least two is an
equivalence of categories on rank one coherent reflexive modules.**  It is isomorphic to the
functor of the equivalence cut out of [Stacks, Tag 0EBJ], and a functor isomorphic to an
equivalence is an equivalence. -/
theorem isEquivalence_rankOneRestrictFunctor :
    (rankOneRestrictFunctor V).IsEquivalence :=
  Functor.isEquivalence_of_iso (rankOneRestrictFunctorIsoEquivFunctor V hdepth).symm

include hdepth in
/-- **Restriction, as an equivalence of categories between the rank one coherent reflexive
modules on `X` and those on an open subscheme off which the structure sheaf has depth at least
two.**  Its functor is `rankOneRestrictFunctor`, that is restriction, on the nose. -/
def rankOneRestrictEquivalence :
    RankOneReflexiveModules X ≌ RankOneReflexiveModules V.toScheme :=
  have := isEquivalence_rankOneRestrictFunctor V hdepth
  (rankOneRestrictFunctor V).asEquivalence

/-- The functor of `rankOneRestrictEquivalence` is restriction, by definition. -/
theorem rankOneRestrictEquivalence_functor :
    (rankOneRestrictEquivalence V hdepth).functor = rankOneRestrictFunctor V :=
  rfl

end Depth

/-! ### The equivalence from the codimension hypothesis -/

section Codimension

variable [IsNormal X] (V : X.Opens)
  (hV : ∀ x : X, x ∉ V → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))

/-- **Restriction is an equivalence of categories between the rank one coherent reflexive
modules on `X` and those on `V`**, for `X` an integral locally Noetherian normal scheme and
`V ⊆ X` an open subscheme every irreducible component of whose complement has codimension at
least two in `X`.

This is the form in which the source uses the statement, in the proofs of [Stacks, Tag 0EBL],
[Stacks, Tag 0EBM] and [Stacks, Tag 0EBN].  Normality enters through Serre's criterion
[Stacks, Tag 0345]: a normal local ring of dimension at least two has depth at least two, so the
codimension hypothesis of [Stacks, Tag 0AY6] (3) implies the depth hypothesis of
[Stacks, Tag 0EBJ].  That `V` is itself integral and locally Noetherian — needed for
`RankOneReflexiveModules V.toScheme` to be defined at all — is *derived* from the hypothesis and
not assumed: an open whose complement has codimension at least two is nonempty, hence an
integral open subscheme, and an open subscheme of a locally Noetherian scheme is locally
Noetherian.  That is what the two `haveI`s in the statement record.

The functor is `rankOneRestrictFunctor`, that is restriction, *on the nose*; see
`AlgebraicGeometry.CoherentReflexive.rankOneCodimTwoRestrictEquiv_functor`, and
`AlgebraicGeometry.CoherentReflexive.rankOneRestrictFunctorForgetIso` for the statement that
reading that functor on underlying modules gives `Scheme.Modules.restrictFunctor`. -/
def rankOneCodimTwoRestrictEquiv :
    haveI : IsIntegral V.toScheme := isIntegral_of_two_le_codimension_compl V hV
    haveI : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
    RankOneReflexiveModules X ≌ RankOneReflexiveModules V.toScheme :=
  have : IsIntegral V.toScheme := isIntegral_of_two_le_codimension_compl V hV
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have : IsDominant V.ι := isDominant_opensι (U := V)
  rankOneRestrictEquivalence V (two_le_depth_stalk_of_notMem_of_two_le_codimension V hV)

/-- **The functor of `rankOneCodimTwoRestrictEquiv` is the restriction functor**, by definition.
This is what makes the equivalence an assertion about *restriction* rather than about some
abstract functor. -/
theorem rankOneCodimTwoRestrictEquiv_functor :
    haveI : IsIntegral V.toScheme := isIntegral_of_two_le_codimension_compl V hV
    haveI : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
    haveI : IsDominant V.ι := isDominant_opensι (U := V)
    (rankOneCodimTwoRestrictEquiv V hV).functor = rankOneRestrictFunctor V :=
  rfl

/-- **Restriction to an open whose complement has codimension at least two is an equivalence on
rank one coherent reflexive modules**, stated as `IsEquivalence` of the restriction functor
itself. -/
theorem isEquivalence_rankOneCodimTwoRestrictFunctor :
    haveI : IsIntegral V.toScheme := isIntegral_of_two_le_codimension_compl V hV
    haveI : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
    haveI : IsDominant V.ι := isDominant_opensι (U := V)
    (rankOneRestrictFunctor V).IsEquivalence :=
  have : IsIntegral V.toScheme := isIntegral_of_two_le_codimension_compl V hV
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have : IsDominant V.ι := isDominant_opensι (U := V)
  isEquivalence_rankOneRestrictFunctor V
    (two_le_depth_stalk_of_notMem_of_two_le_codimension V hV)

end Codimension

end AlgebraicGeometry.CoherentReflexive

end
