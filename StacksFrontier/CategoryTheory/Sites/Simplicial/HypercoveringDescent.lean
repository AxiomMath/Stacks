module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Sites.LocallyFullyFaithful
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Presheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkLimit
public import StacksFrontier.CategoryTheory.Sites.Topos.PushforwardEquality

/-!
# Cohomological descent along the augmentation of a hypercovering

Let `(C, J)` be a site with equalizers and fibre products and let `K` be a hypercovering of the
final presheaf, in the sense of Stacks 09VU. Its underlying simplicial semi-representable object
makes `n ↦ C/K_n` a simplicial family of sites in case (B) of Stacks 0D6Z, with total site
`(C/K)_total` and augmentation `a` towards `(C, J)` given by the degree-zero localization functor
`j_0` (Stacks 0D8B). Because `j_total : (C/K)_total ⥤ C` is continuous as well as cocontinuous,
the inverse image `a^{-1}` is restriction along `j_total`, at any coefficient category.

Stacks 0D8E asserts that `a^{-1}` is fully faithful with essential image the cartesian sheaves,
for sheaves of sets and for sheaves of abelian groups, with `a_*` as quasi-inverse. This file
proves the two clauses that follow from the *degree-zero* condition on a hypercovering alone:

* `a^{-1}` is faithful, and
* every sheaf in the essential image of `a^{-1}` is cartesian.

The input for the first is that `j_total` is cover dense: condition (1) of Stacks 09VU says that
the degree-zero augmentation `F(K_0) ⟶ *` of presheaves is locally surjective, which is exactly
the statement that every object of `C` is covered by objects admitting a morphism to a component
of `K_0`, and every such object, with that morphism, is an object of `C/K_0` and so of the total
site. Restriction along a continuous cover-dense functor is faithful, which is Stacks 04D9.

The input for the second is Stacks 0D7H: the inverse image along the augmentation of a sheaf on
`(C, J)` is cartesian, since the augmentation does not see the simplicial direction. Being
cartesian is invariant under isomorphism of sheaves, so it holds throughout the essential image.
No condition on `K` is used here at all.

## Main definitions

* `CategoryTheory.SemiRepresentable.Factors` and `.factorsPresheaf`: the presheaf whose sections
  over `V` record that `V` admits a morphism to some component of a semi-representable object.
* `CategoryTheory.SimplicialSemiRepresentable.degreeZeroSieve`: the sieve on an object of `C`
  consisting of the arrows whose source admits a morphism to a component of `K_0`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.isCoverDense_totalForget`: the localization functor
  of the total site of a hypercovering is cover dense.
* `CategoryTheory.SimplicialSemiRepresentable.faithful_inverseImage` and
  `.faithful_totalInverseImage`: **Stacks 0D8E (1)**, the faithfulness half, for the inverse image
  read as restriction along `j_total` and for the inverse image of the morphism of topoi which
  Stacks 0D70 attaches to the augmentation.
* `CategoryTheory.SimplicialSemiRepresentable.faithful_abelianInverseImage`: **Stacks 0D8E (2)**,
  the faithfulness half, on abelian sheaves.
* `CategoryTheory.SimplicialSemiRepresentable.isCartesianSheaf_of_mem_essImage` and
  `.isCartesianAbSheaf_of_mem_essImage`: **Stacks 0D8E (1) and (2)**, the inclusion of the
  essential image of `a^{-1}` in the cartesian sheaves, of sets and of abelian groups.
* `CategoryTheory.SimplicialSiteSituation.isCartesianSheaf_of_iso`: being cartesian is invariant
  under isomorphism of sheaves on the total site.
* `CategoryTheory.SimplicialSemiRepresentable.full_inverseImage`,
  `.fullyFaithfulInverseImageHypercovering`, `.isIso_unit_hypercovering`,
  `.mem_essImage_iff_isCartesianSheaf` and `.isIso_counit_app_hypercovering`: **Stacks 0D8E
  (1)**, the two remaining clauses and their consequences for the unit and the counit, each
  carrying its missing input as a hypothesis.
* the same names with `abelian` in them: **Stacks 0D8E (2)**, at abelian coefficients.

## Implementation notes

Extracting a morphism to a component of `K_0` from a section of the presheaf `F(K_0)` is done
without computing the sections of a coproduct of presheaves. The presheaf `factorsPresheaf K_0`
receives a morphism from each summand `h_{K_{0,i}}` of `F(K_0)`, by Yoneda, so it receives one
from `F(K_0)` by `CategoryTheory.Limits.Sigma.desc`; applying that morphism to a section is the
extraction. Only the existence of the morphism is needed, which is why no inverse is constructed.

The hypercovering of Stacks 09VU is a hypercovering of a presheaf, and for a hypercovering of the
final presheaf the section of the augmentation target over an object `X` which condition (1) is
applied to is produced from the terminal morphism out of the presheaf represented by `X`; which
section it is does not matter, since the condition is applied to every object and the conclusion
discards the equation satisfied by the local lift.

The two remaining clauses of Stacks 0D8E — that `a^{-1}` is full, and that every cartesian sheaf
lies in its essential image, so that `a_*` is a quasi-inverse — are *not* proved outright. Both
need the higher conditions on a hypercovering, which the degree-zero condition used above does
not supply: the surjectivity of `K_1 ⟶ K_0 × K_0` already fails for the constant simplicial
object on a covering, for which `a^{-1}` is faithful by the result above and not full. They are
stated below with their missing input carried as an explicit hypothesis, and each such statement
says in its clause string exactly what it carries.

The missing input for fullness is `CategoryTheory.Functor.IsLocallyFull` for `j_total`:
restriction along a continuous functor which is both cover dense and locally full is full, and
the first two are available. Unwound at objects of simplicial degrees `m` and `n`, local
fullness is the local existence of a simplex of some degree carrying the two given charts on its
faces; at `m = n = 0` that is condition (2) of Stacks 09VU, and in general it needs condition
(3) as well.

The missing input for the description of the essential image is essential surjectivity onto the
cartesian sheaves, which is the clause itself; what the statements below add to it is the other
inclusion, proved above, and the deduction of the invertibility of the counit, which uses full
faithfulness as well. Granted full faithfulness, the unit `E ⟶ a_* a^{-1} E` is invertible for
every `E` and the counit `a^{-1} a_* F ⟶ F` is invertible exactly on the essential image; so
fullness alone yields the first half of "`a_*` is a quasi-inverse" and the two clauses together
yield the second.

That route is not the cheapest one, and is probably not the one to take. In general degrees the
simplex it asks for is a prescribed-faces filling, `r = m + n + 1` with the two complementary
face inclusions of `⦋m⦌ ⋆ ⦋n⦌`; this repository has condition (3) only in the coskeleton form
`Stacks.CategoryTheory.Hypercovering.locallySurjective_higherMatchingMap_of_isHypercovering`, and
Mathlib has no join on `SimplexCategory` at all, so the passage between the two forms is new
simplicial content. `CategoryTheory.Functor.IsLocallyFull` is also strictly stronger than what
this tag needs, being a property of the site rather than of a pair of sheaves.

The cheaper route is the unit of `a^{-1} ⊣ a_*`: if `G ⟶ a_* a^{-1} G` is an isomorphism for
every `G` then `a^{-1}` is fully faithful, and it is, because `a_* a^{-1} G` is the equalizer of
the two degree-one transitions by Stacks 0D70 (3)
(`CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalDirectImageForkIsLimit`), each
vertex is `SheafHom(F(K_n)^#, G)` by Stacks 0D8B and 0D86, and
`F(K_1)^# ⇉ F(K_0)^# ⟶ ⊤` is a coequalizer by conditions (1) and (2) alone
(`CategoryTheory.Sheaf.isColimitCoforkOfLocallySurjective`), which
`CategoryTheory.SheafHomAdj.isLimitForkSheafHomContraMap` turns into the matching limit fork.
Conditions (1) and (2) are the only inputs, and condition (3) is not needed. Note that
`SimplexCategory.δ 0` and `δ 1` are `const 1` and `const 0`, so the coequalizer and the fork run
over opposite orderings and one of the two has to be swapped.

## References

* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 04D9](https://stacks.math.columbia.edu/tag/04D9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory

/-! ### Morphisms to a component of a semi-representable object -/

namespace SemiRepresentable

variable {C : Type u} [SmallCategory C]

/-- The sections over `V` of the presheaf recording that `V` admits a morphism to some component
of the semi-representable object `T`. -/
def Factors (T : FormalCoproduct.{u} C) (V : C) : Type u :=
  ULift.{u} (PLift (∃ i : T.I, Nonempty (V ⟶ T.obj i)))

/-- The presheaf recording that an object admits a morphism to some component of the
semi-representable object `T`. It is a presheaf because such a morphism may be precomposed. -/
def factorsPresheaf (T : FormalCoproduct.{u} C) : Cᵒᵖ ⥤ Type u where
  obj V := Factors T V.unop
  map {V W} g := ↾fun (x : Factors T V.unop) =>
    (ULift.up (PLift.up (x.down.down.imp fun _ hi => ⟨g.unop ≫ hi.some⟩)) : Factors T W.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The morphism from the representable presheaf of a component of `T` to `factorsPresheaf T`:
the identity of that component is a section, by Yoneda. -/
def factorsι (T : FormalCoproduct.{u} C) (i : T.I) :
    uliftYoneda.{u}.obj (T.obj i) ⟶ factorsPresheaf T :=
  uliftYonedaEquiv.symm (show Factors T (T.obj i) from ULift.up (PLift.up ⟨i, ⟨𝟙 _⟩⟩))

/-- The morphism from the presheaf represented by `T` to `factorsPresheaf T`, assembled from the
morphisms out of the summands. -/
def factorsDesc (T : FormalCoproduct.{u} C) :
    FormalCoproduct.uliftYoneda.{u}.obj T ⟶ factorsPresheaf T :=
  Limits.Sigma.desc fun i => factorsι T i

/-- A section over `V` of the presheaf represented by a semi-representable object `T` exhibits a
morphism from `V` to one of the components of `T`. -/
theorem exists_hom_of_associatedPresheaf_section (T : FormalCoproduct.{u} C) (V : C)
    (t : (associatedPresheafFunctor.{u, u, u, u} (C := C)).obj T |>.obj (op V)) :
    ∃ i : T.I, Nonempty (V ⟶ T.obj i) :=
  (show Factors T V from (factorsDesc T).app (op V) t.down).down.down

end SemiRepresentable

/-! ### Cartesianness is invariant under isomorphism -/

namespace SimplicialSiteSituation

/-- A sheaf on the total site isomorphic to a cartesian one is cartesian: the transitions of the
two are conjugate by the isomorphism, through naturality of
`CategoryTheory.SimplicialSiteSituation.fiberTransition`. -/
theorem isCartesianSheaf_of_iso (S : SimplicialSiteSituation.{u})
    {F F' : Sheaf S.totalTopology (Type u)} (e : F ≅ F') (h : S.IsCartesianSheaf F) :
    S.IsCartesianSheaf F' := by
  intro m n φ
  have := h φ
  have hnat := (S.fiberTransition φ).naturality e.hom
  have hrw : (S.fiberTransition φ).app F' =
      inv ((S.restrict m ⋙ (S.transitionMorphism φ).inverseImage).map e.hom) ≫
        (S.fiberTransition φ).app F ≫ (S.restrict n).map e.hom := by
    rw [← hnat, IsIso.inv_hom_id_assoc]
  rw [hrw]
  infer_instance

end SimplicialSiteSituation

/-! ### Cover density of the localization functor of the total site -/

namespace SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C]

/-- The sieve on `X` of the arrows whose source admits a morphism to a component of `K_0`. It is
a sieve because such a morphism may be precomposed. -/
def degreeZeroSieve (K : SimplicialObject (FormalCoproduct.{u} C)) (X : C) : Sieve X where
  arrows V _ := ∃ i : (K.obj (op (SimplexCategory.mk 0))).I,
    Nonempty (V ⟶ (K.obj (op (SimplexCategory.mk 0))).obj i)
  downward_closed := by
    rintro _ _ _ ⟨i, ⟨p⟩⟩ h
    exact ⟨i, ⟨h ≫ p⟩⟩

/-- An arrow whose source admits a morphism to a component of `K_0` factors through the image of
the localization functor of the total site: its source, with that morphism, is an object of
`C/K_0` and hence of the total site, on which `j_total` is `j_0`. -/
theorem degreeZeroSieve_le_coverByImage (K : SimplicialObject (FormalCoproduct.{u} C)) (X : C) :
    degreeZeroSieve K X ≤ Sieve.coverByImage (totalForget K) X := by
  rintro V g ⟨i, ⟨p⟩⟩
  exact ⟨⟨⟨op (SimplexCategory.mk 0), ⟨i, Over.mk p⟩⟩, 𝟙 V, g, Category.id_comp g⟩⟩

/-- The unique section over `X` of the target of the augmentation of a hypercovering of the final
presheaf, obtained from the terminal morphism out of the presheaf represented by `X`. -/
def terminalLiftedSection (X : C) : ULift.{u} ((⊤_ (Cᵒᵖ ⥤ Type u)).obj (op X)) :=
  ULift.up ((terminal.from (yoneda.obj X)).app (op X) (𝟙 X))

/-- **Condition (1) of Stacks 09VU, as a covering sieve.** For a hypercovering of the final
presheaf, every object of `C` is covered by objects admitting a morphism to a component of `K_0`.

Local surjectivity of the degree-zero augmentation applied to the section
`terminalLiftedSection X` produces a covering sieve of `X` each of whose arrows has, over its
source, a section of the presheaf represented by `K_0`; such a section exhibits a morphism to a
component of `K_0` by `exists_hom_of_associatedPresheaf_section`. -/
theorem degreeZeroSieve_mem [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P) (X : C) :
    degreeZeroSieve H.toSimplicialObject X ∈ P.toGrothendieck X := by
  have := H.locallySurjective_zero
  have key := Presheaf.imageSieve_mem P.toGrothendieck
    (H.augmentation.app (op (SimplexCategory.mk 0))) (U := op X) (terminalLiftedSection X)
  refine GrothendieckTopology.superset_covering _ ?_ key
  rintro V g ⟨t, -⟩
  exact exists_hom_of_associatedPresheaf_section _ _ t

/-- The localization functor `j_total : (C/K)_total ⥤ C` of the total site of a hypercovering is
cover dense: the sieve of arrows factoring through its image contains the covering sieve of
`degreeZeroSieve_mem`. -/
instance isCoverDense_totalForget [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P) :
    (totalForget H.toSimplicialObject).IsCoverDense P.toGrothendieck :=
  ⟨fun X => GrothendieckTopology.superset_covering _
    (degreeZeroSieve_le_coverByImage _ X) (degreeZeroSieve_mem P H X)⟩

/-! ### Faithfulness of the inverse image -/

/-- **Stacks 0D8E (1), the faithfulness half.** For a hypercovering `K` the inverse image
`a^{-1} : Sh(C) ⥤ Sh((C/K)_total)` of the augmentation is faithful.

The inverse image is restriction along `j_total`, which is continuous and cover dense, and
restriction along such a functor is faithful by Stacks 04D9. -/
@[stacks 0D8E "part (1): a^{-1} on sheaves of sets is faithful"]
theorem faithful_inverseImage [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P) :
    (totalLocalizationMorphism P.toGrothendieck H.toSimplicialObject).inverseImage.Faithful :=
  sheafPushforwardContinuous_faithful_of_isCoverDense (totalForget H.toSimplicialObject)
    ((situation P.toGrothendieck H.toSimplicialObject).totalTopology) P.toGrothendieck (Type u)

/-- **Stacks 0D8E (1), the faithfulness half**, for the inverse image of the morphism of topoi
which Stacks 0D70 attaches to the augmentation. By Stacks 0D8B that functor is isomorphic to
restriction along `j_total`, and faithfulness is invariant under isomorphism of functors. -/
@[stacks 0D8E "part (1): a^{-1} of Stacks 0D70 on sheaves of sets is faithful"]
theorem faithful_totalInverseImage [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P) :
    Functor.Faithful
      (augmentation P.toGrothendieck H.toSimplicialObject).totalMorphismOfTopoi.inverseImage :=
  @Functor.Faithful.of_iso _ _ _ _ _ _ (faithful_inverseImage P H)
    (totalInverseImageIso P.toGrothendieck H.toSimplicialObject).symm

/-- **Stacks 0D8E (2), the faithfulness half.** For a hypercovering `K` the inverse image
`a^{-1} : Ab(C) ⥤ Ab((C/K)_total)` of the augmentation — restriction along `j_total` on abelian
sheaves, as in Stacks 09WM (2) — is faithful.

Cover density of `j_total` is a statement about the site, so the argument of
`faithful_inverseImage` applies at any coefficient category. -/
@[stacks 0D8E "part (2): a^{-1} on abelian sheaves is faithful"]
theorem faithful_abelianInverseImage [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P) :
    ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
      ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
      P.toGrothendieck).Faithful :=
  sheafPushforwardContinuous_faithful_of_isCoverDense (totalForget H.toSimplicialObject)
    ((situation P.toGrothendieck H.toSimplicialObject).totalTopology) P.toGrothendieck Ab.{u}

/-! ### The essential image consists of cartesian sheaves -/

variable (J : GrothendieckTopology C) (K : SimplicialObject (FormalCoproduct.{u} C))
  [J.toCoverage.HasPullbacks]

/-- **Stacks 0D7H (1)**, read through the identification of Stacks 0D8B: the inverse image along
the augmentation of a sheaf of sets on `(C, J)` is a cartesian sheaf on the total site. -/
theorem isCartesianSheaf_inverseImage (G : Sheaf J (Type u)) :
    (situation J K).IsCartesianSheaf
      ((totalLocalizationMorphism J K).inverseImage.obj G) := by
  refine SimplicialSiteSituation.isCartesianSheaf_of_iso _
    ((totalInverseImageIso J K).app G) ?_
  intro m n φ
  exact CocontinuousSimplicialSite.Augmentation.isIso_fiberTransition_app_inverseImage
    (augmentation J K) φ G

/-- **Stacks 0D8E (1), the inclusion of the essential image in the cartesian sheaves.** Every
sheaf of sets on the total site isomorphic to an inverse image along the augmentation is
cartesian.

This is Stacks 0D7H (1) together with invariance of cartesianness under isomorphism, and uses no
condition on the simplicial semi-representable object `K`. -/
@[stacks 0D8E "part (1): the essential image of a^{-1} consists of cartesian sheaves of sets"]
theorem isCartesianSheaf_of_mem_essImage {F : Sheaf (situation J K).totalTopology (Type u)}
    (hF : (totalLocalizationMorphism J K).inverseImage.essImage F) :
    (situation J K).IsCartesianSheaf F := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact SimplicialSiteSituation.isCartesianSheaf_of_iso _ e (isCartesianSheaf_inverseImage J K G)

/-- **Stacks 0D8E (2), the inclusion of the essential image in the cartesian sheaves.** Every
sheaf of abelian groups on the total site isomorphic to an inverse image along the augmentation is
cartesian.

Cartesianness of an abelian sheaf is cartesianness of its underlying sheaf of sets, and the
underlying sheaf of the restriction of `𝒢` along `j_total` is the restriction of the underlying
sheaf of `𝒢`, both being a composition of functors. So the abelian statement follows from the
statement for sheaves of sets applied to the underlying sheaf. -/
@[stacks 0D8E "part (2): the essential image of a^{-1} consists of cartesian abelian sheaves"]
theorem isCartesianAbSheaf_of_mem_essImage {F : Sheaf (situation J K).totalTopology Ab.{u}}
    (hF : ((totalForget K).sheafPushforwardContinuous Ab.{u}
      ((situation J K).totalTopology) J).essImage F) :
    (situation J K).IsCartesianAbSheaf F := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  refine SimplicialSiteSituation.isCartesianSheaf_of_iso _
    ((sheafCompose (situation J K).totalTopology (forget Ab.{u})).mapIso e) ?_
  exact isCartesianSheaf_inverseImage J K ((sheafCompose J (forget Ab.{u})).obj G)

/-! ### Full faithfulness of the inverse image, granted local fullness of `j_total` -/

/-- Restriction along `j_total` is faithful when `j_total` is cover dense, by Stacks 04D9. -/
theorem faithful_inverseImage_of_isCoverDense (hcd : (totalForget K).IsCoverDense J) :
    (totalLocalizationMorphism J K).inverseImage.Faithful :=
  @sheafPushforwardContinuous_faithful_of_isCoverDense _ _ _ _ (totalForget K)
    ((situation J K).totalTopology) J (Type u) _ (totalForget_isContinuous J K) hcd

/-- Restriction along `j_total` is full when `j_total` is cover dense and locally full: the two
conditions together let a morphism between the restrictions of two sheaves on the total site be
amalgamated into a morphism of those sheaves. -/
theorem full_inverseImage_of_isLocallyFull (hcd : (totalForget K).IsCoverDense J)
    (hlf : (totalForget K).IsLocallyFull J) :
    (totalLocalizationMorphism J K).inverseImage.Full :=
  @Functor.IsCoverDense.full_sheafPushforwardContinuous _ _ _ _
    ((situation J K).totalTopology) J (Type u) _ (totalForget K) hcd hlf
    (totalForget_isContinuous J K)

/-- Restriction along a cover dense and locally full `j_total` is fully faithful. -/
def fullyFaithfulInverseImage (hcd : (totalForget K).IsCoverDense J)
    (hlf : (totalForget K).IsLocallyFull J) :
    (totalLocalizationMorphism J K).inverseImage.FullyFaithful :=
  @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _
    (full_inverseImage_of_isLocallyFull J K hcd hlf) (faithful_inverseImage_of_isCoverDense J K hcd)

/-- The unit of the adjunction `a^{-1} ⊣ a_*` is invertible when `a^{-1}` is fully faithful. -/
theorem isIso_unit_of_isLocallyFull (hcd : (totalForget K).IsCoverDense J)
    (hlf : (totalForget K).IsLocallyFull J) :
    IsIso (totalLocalizationMorphism J K).adj.unit :=
  @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _
    (totalLocalizationMorphism J K).adj (full_inverseImage_of_isLocallyFull J K hcd hlf)
    (faithful_inverseImage_of_isCoverDense J K hcd)

/-- For an adjunction with fully faithful left adjoint the counit is invertible at exactly the
objects of the essential image of that adjoint. -/
theorem isIso_counit_app_iff_mem_essImage_of_isLocallyFull
    (hcd : (totalForget K).IsCoverDense J) (hlf : (totalForget K).IsLocallyFull J)
    (F : Sheaf (situation J K).totalTopology (Type u)) :
    IsIso ((totalLocalizationMorphism J K).adj.counit.app F) ↔
      (totalLocalizationMorphism J K).inverseImage.essImage F :=
  @Adjunction.isIso_counit_app_iff_mem_essImage _ _ _ _ _ _
    (totalLocalizationMorphism J K).adj (faithful_inverseImage_of_isCoverDense J K hcd)
    (full_inverseImage_of_isLocallyFull J K hcd hlf) F

/-- The adjunction `a^{-1} ⊣ a_*` on sheaves of abelian groups, as in Stacks 09WM (2): the
inverse image is restriction along `j_total` and the direct image is the right Kan extension
along it. -/
def abelianTotalAdjunction :
    (totalForget K).sheafPushforwardContinuous Ab.{u} ((situation J K).totalTopology) J ⊣
      (totalForget K).sheafPushforwardCocontinuous Ab.{u} ((situation J K).totalTopology) J :=
  (totalForget K).sheafAdjunctionCocontinuous Ab.{u} ((situation J K).totalTopology) J

/-- Restriction along a cover dense `j_total` is faithful at abelian coefficients. -/
theorem faithful_abelianInverseImage_of_isCoverDense (hcd : (totalForget K).IsCoverDense J) :
    ((totalForget K).sheafPushforwardContinuous Ab.{u}
      ((situation J K).totalTopology) J).Faithful :=
  @sheafPushforwardContinuous_faithful_of_isCoverDense _ _ _ _ (totalForget K)
    ((situation J K).totalTopology) J Ab.{u} _ (totalForget_isContinuous J K) hcd

/-- Restriction along a cover dense and locally full `j_total` is full at abelian coefficients:
local fullness is a condition on the site, so the same input serves at any coefficients. -/
theorem full_abelianInverseImage_of_isLocallyFull (hcd : (totalForget K).IsCoverDense J)
    (hlf : (totalForget K).IsLocallyFull J) :
    ((totalForget K).sheafPushforwardContinuous Ab.{u}
      ((situation J K).totalTopology) J).Full :=
  @Functor.IsCoverDense.full_sheafPushforwardContinuous _ _ _ _
    ((situation J K).totalTopology) J Ab.{u} _ (totalForget K) hcd hlf
    (totalForget_isContinuous J K)

/-- Restriction along a cover dense and locally full `j_total` is fully faithful at abelian
coefficients. -/
def fullyFaithfulAbelianInverseImage (hcd : (totalForget K).IsCoverDense J)
    (hlf : (totalForget K).IsLocallyFull J) :
    ((totalForget K).sheafPushforwardContinuous Ab.{u}
      ((situation J K).totalTopology) J).FullyFaithful :=
  @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _
    (full_abelianInverseImage_of_isLocallyFull J K hcd hlf)
    (faithful_abelianInverseImage_of_isCoverDense J K hcd)

/-- The unit of the abelian adjunction is invertible when its left adjoint is fully faithful. -/
theorem isIso_abelianUnit_of_isLocallyFull (hcd : (totalForget K).IsCoverDense J)
    (hlf : (totalForget K).IsLocallyFull J) :
    IsIso (abelianTotalAdjunction J K).unit :=
  @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _ (abelianTotalAdjunction J K)
    (full_abelianInverseImage_of_isLocallyFull J K hcd hlf)
    (faithful_abelianInverseImage_of_isCoverDense J K hcd)

/-- The counit of the abelian adjunction is invertible at exactly the objects of the essential
image of its left adjoint. -/
theorem isIso_abelianCounit_app_iff_mem_essImage_of_isLocallyFull
    (hcd : (totalForget K).IsCoverDense J) (hlf : (totalForget K).IsLocallyFull J)
    (F : Sheaf (situation J K).totalTopology Ab.{u}) :
    IsIso ((abelianTotalAdjunction J K).counit.app F) ↔
      ((totalForget K).sheafPushforwardContinuous Ab.{u}
        ((situation J K).totalTopology) J).essImage F :=
  @Adjunction.isIso_counit_app_iff_mem_essImage _ _ _ _ _ _ (abelianTotalAdjunction J K)
    (faithful_abelianInverseImage_of_isCoverDense J K hcd)
    (full_abelianInverseImage_of_isLocallyFull J K hcd hlf) F

/-! ### The two remaining clauses of Stacks 0D8E, with their missing input carried -/

section Remaining

variable [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u, u} P)

/-- **Stacks 0D8E (1), fullness**, carrying local fullness of `j_total`.

For a hypercovering `K` the inverse image `a^{-1} : Sh(C) ⥤ Sh((C/K)_total)` of the augmentation
is full as soon as the localization functor `j_total` is locally full for the topology of `C`.
That local fullness — unwound at two objects of the total site, the local existence of a simplex
of `K` carrying two prescribed charts on two of its faces — is the input the degree-zero
condition does not supply, and it is carried here as a hypothesis. -/
@[stacks 0D8E "part (1): a^{-1} on sheaves of sets is full, carrying local fullness of j_total"]
theorem full_inverseImage
    (hlf : (totalForget H.toSimplicialObject).IsLocallyFull P.toGrothendieck) :
    (totalLocalizationMorphism P.toGrothendieck H.toSimplicialObject).inverseImage.Full :=
  full_inverseImage_of_isLocallyFull P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) hlf

/-- **Stacks 0D8E (1), full faithfulness**, carrying local fullness of `j_total`. -/
@[stacks 0D8E "part (1): a^{-1} on sheaves of sets is fully faithful, carrying local fullness"]
def fullyFaithfulInverseImageHypercovering
    (hlf : (totalForget H.toSimplicialObject).IsLocallyFull P.toGrothendieck) :
    (totalLocalizationMorphism P.toGrothendieck
      H.toSimplicialObject).inverseImage.FullyFaithful :=
  fullyFaithfulInverseImage P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) hlf

/-- **Stacks 0D8E (1), the unit is invertible**, carrying local fullness of `j_total`: for every
sheaf of sets `E` on `C` the canonical map `E ⟶ a_* a^{-1} E` is an isomorphism. This is the
half of "`a_*` is a quasi-inverse" that holds on all of `Sh(C)`. -/
@[stacks 0D8E "part (1): E = a_* a^{-1} E on sheaves of sets, carrying local fullness"]
theorem isIso_unit_hypercovering
    (hlf : (totalForget H.toSimplicialObject).IsLocallyFull P.toGrothendieck) :
    IsIso (totalLocalizationMorphism P.toGrothendieck H.toSimplicialObject).adj.unit :=
  isIso_unit_of_isLocallyFull P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) hlf

/-- **Stacks 0D8E (1), the essential image is exactly the cartesian sheaves**, carrying
essential surjectivity onto them. One inclusion is `isCartesianSheaf_of_mem_essImage`; the other
is the clause the degree-zero condition does not supply, and it is carried as a hypothesis. -/
@[stacks 0D8E "part (1): essential image = cartesian sheaves of sets, carrying surjectivity"]
theorem mem_essImage_iff_isCartesianSheaf
    (hsurj : ∀ G : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology
        (Type u),
      (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf G →
        (totalLocalizationMorphism P.toGrothendieck
          H.toSimplicialObject).inverseImage.essImage G)
    (F : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology (Type u)) :
    (totalLocalizationMorphism P.toGrothendieck
        H.toSimplicialObject).inverseImage.essImage F ↔
      (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf F :=
  ⟨isCartesianSheaf_of_mem_essImage P.toGrothendieck H.toSimplicialObject, hsurj F⟩

/-- **Stacks 0D8E (1), the counit is invertible on cartesian sheaves**, carrying both of the two
clauses: for a cartesian sheaf of sets `F` on the total site the canonical map
`a^{-1} a_* F ⟶ F` is an isomorphism. This is the half of "`a_*` is a quasi-inverse" that holds
on the cartesian sheaves; the two carried hypotheses supply full faithfulness of `a^{-1}` and
membership of `F` in its essential image. -/
@[stacks 0D8E "part (1): a^{-1} a_* F = F for cartesian F, carrying both remaining clauses"]
theorem isIso_counit_app_hypercovering
    (hlf : (totalForget H.toSimplicialObject).IsLocallyFull P.toGrothendieck)
    (hsurj : ∀ G : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology
        (Type u),
      (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf G →
        (totalLocalizationMorphism P.toGrothendieck
          H.toSimplicialObject).inverseImage.essImage G)
    {F : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology (Type u)}
    (hF : (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf F) :
    IsIso ((totalLocalizationMorphism P.toGrothendieck
      H.toSimplicialObject).adj.counit.app F) :=
  (isIso_counit_app_iff_mem_essImage_of_isLocallyFull P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) hlf F).mpr (hsurj F hF)

/-- **Stacks 0D8E (2), fullness**, carrying local fullness of `j_total`. Local fullness is a
condition on the site, so the same input serves at abelian coefficients. -/
@[stacks 0D8E "part (2): a^{-1} on abelian sheaves is full, carrying local fullness of j_total"]
theorem full_abelianInverseImage
    (hlf : (totalForget H.toSimplicialObject).IsLocallyFull P.toGrothendieck) :
    ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
      ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
      P.toGrothendieck).Full :=
  full_abelianInverseImage_of_isLocallyFull P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) hlf

/-- **Stacks 0D8E (2), full faithfulness**, carrying local fullness of `j_total`. -/
@[stacks 0D8E "part (2): a^{-1} on abelian sheaves is fully faithful, carrying local fullness"]
def fullyFaithfulAbelianInverseImageHypercovering
    (hlf : (totalForget H.toSimplicialObject).IsLocallyFull P.toGrothendieck) :
    ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
      ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
      P.toGrothendieck).FullyFaithful :=
  fullyFaithfulAbelianInverseImage P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) hlf

/-- **Stacks 0D8E (2), the unit is invertible**, carrying local fullness of `j_total`: for every
sheaf of abelian groups `E` on `C` the canonical map `E ⟶ a_* a^{-1} E` is an isomorphism. -/
@[stacks 0D8E "part (2): E = a_* a^{-1} E on abelian sheaves, carrying local fullness"]
theorem isIso_abelianUnit_hypercovering
    (hlf : (totalForget H.toSimplicialObject).IsLocallyFull P.toGrothendieck) :
    IsIso (abelianTotalAdjunction P.toGrothendieck H.toSimplicialObject).unit :=
  isIso_abelianUnit_of_isLocallyFull P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) hlf

/-- **Stacks 0D8E (2), the essential image is exactly the cartesian abelian sheaves**, carrying
essential surjectivity onto them. -/
@[stacks 0D8E "part (2): essential image = cartesian abelian sheaves, carrying surjectivity"]
theorem mem_essImage_iff_isCartesianAbSheaf
    (hsurj : ∀ G : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology Ab.{u},
      (situation P.toGrothendieck H.toSimplicialObject).IsCartesianAbSheaf G →
        ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
          ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
          P.toGrothendieck).essImage G)
    (F : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology Ab.{u}) :
    ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
        ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
        P.toGrothendieck).essImage F ↔
      (situation P.toGrothendieck H.toSimplicialObject).IsCartesianAbSheaf F :=
  ⟨isCartesianAbSheaf_of_mem_essImage P.toGrothendieck H.toSimplicialObject, hsurj F⟩

/-- **Stacks 0D8E (2), the counit is invertible on cartesian abelian sheaves**, carrying both of
the two clauses: for a cartesian sheaf of abelian groups `F` on the total site the canonical map
`a^{-1} a_* F ⟶ F` is an isomorphism. -/
@[stacks 0D8E "part (2): a^{-1} a_* F = F for cartesian F, carrying both remaining clauses"]
theorem isIso_abelianCounit_app_hypercovering
    (hlf : (totalForget H.toSimplicialObject).IsLocallyFull P.toGrothendieck)
    (hsurj : ∀ G : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology Ab.{u},
      (situation P.toGrothendieck H.toSimplicialObject).IsCartesianAbSheaf G →
        ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
          ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
          P.toGrothendieck).essImage G)
    {F : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology Ab.{u}}
    (hF : (situation P.toGrothendieck H.toSimplicialObject).IsCartesianAbSheaf F) :
    IsIso ((abelianTotalAdjunction P.toGrothendieck
      H.toSimplicialObject).counit.app F) :=
  (isIso_abelianCounit_app_iff_mem_essImage_of_isLocallyFull P.toGrothendieck
    H.toSimplicialObject (isCoverDense_totalForget P H) hlf F).mpr (hsurj F hF)

end Remaining

end SimplicialSemiRepresentable

end CategoryTheory

end
