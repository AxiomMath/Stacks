module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechComplex
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationComponents

/-!
# Lower shriek along the augmentation of the site of a simplicial semi-representable object

Let `(C, J)` be a site and let `K` be a simplicial object of `SR(C)`, so that the simplicial
family of sites `n ↦ C/K_n` carries an augmentation `a` towards `(C, J)` given by the
degree-zero localization functor. The localization functor `j_total : (C/K)_total ⥤ C` of the
total site is both continuous and cocontinuous, and it is the site functor of `a`.

Continuity of `j_total` makes the inverse image `a^{-1}` — restriction along `j_total` — a right
adjoint, so there is an extension by zero `a_!` both on sheaves of sets and on abelian sheaves.
In simplicial degree `n` the inverse image `a^{-1}` is the inverse image `a_n^{-1}` of the
augmentation of that degree, which is restriction along the localization functor
`j_n : C/K_n ⥤ C`. The direct image of an abelian sheaf `𝒢` on the total site is the equalizer
of the two maps `a_{0,*}𝒢_0 ⟶ a_{1,*}𝒢_1` attached to the two vertices of the one-simplex.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.augmentationSheafLowerShriekAdjunction`: **part
  (1)**, the left adjoint `a^{Sh}_!` of `a^{-1}` on sheaves of sets.
* `CategoryTheory.SimplicialSemiRepresentable.augmentationAbelianLowerShriekAdjunction`: **part
  (2)**, the left adjoint `a_!` of `a^{-1}` on abelian sheaves.
* `CategoryTheory.SimplicialSemiRepresentable.augmentationInverseImageComponentIso`: **part
  (3)**, the inverse image `a^{-1}ℱ` is in simplicial degree `n` the sheaf `a_n^{-1}ℱ`, that is
  the restriction of `ℱ` along `j_n`.
* `CategoryTheory.SimplicialSemiRepresentable.augmentationAbelianPushforwardFork`: **part (4)**,
  the fork exhibiting `a_*𝒢` over the two vertex maps `a_{0,*}𝒢_0 ⟶ a_{1,*}𝒢_1`, and
  `CategoryTheory.SimplicialSemiRepresentable.augmentationAbelianPushforwardForkIsLimit`:
  **part (4)**, that fork is a limit, so `a_*𝒢` is their equalizer.

## Scope of the hypothesis

Everything here assumes `[J.toCoverage.HasPullbacks]`. The maximal presieve of an object
generates the maximal sieve, so it is a covering family of `J`, and the hypothesis therefore
asks for the fibre product of *every* pair of morphisms with a common target: it forces `C` to
have all fibre products. A site in the sense of the Stacks project only has fibre products of
coverings with arbitrary morphisms, so these declarations are the special case of Stacks 09WM
for sites whose underlying category has all fibre products. The statement for an arbitrary site
is in `StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableStacksSite`
(`CategoryTheory.SimplicialSemiRepresentable.stableSheafLowerShriekAdjunction` and the
following declarations), which carries the tag.

## Implementation notes

Parts (1) and (2) are the single statement of Stacks 00XR (2) — Mathlib's sheaf pullback along a
continuous functor is left adjoint to restriction along it — applied at the two coefficient
categories `Type u` and `AddCommGrpCat.{u}`; that is simultaneously Sites, Lemma 7.21.5 and
Modules on Sites, Lemma 18.16.2. The only input beyond continuity of `j_total` is that
restriction along `j_total` is `a^{-1}`, which needs `j_total` to be cocontinuous as well, and
both properties are available for the total localization functor.

For sheaves of sets that identification of `a^{-1}` with restriction is the Stacks 0D8B
comparison of the morphism of topoi of the augmentation with the morphism of topoi of `j_total`,
so part (1) is stated against the inverse image of the augmentation itself. The morphism of
topoi which Stacks 0D70 attaches to an augmentation is built for sheaves of sets only, so for
abelian sheaves no such comparison is available to quote and part (2) is stated against
restriction along `j_total` on abelian sheaves. That is exactly what the source's proof means by
`a^{-1}`: the inverse image of a morphism of topoi defined by a functor which is continuous as
well as cocontinuous is plain restriction, by Stacks 00XR (1), at any coefficient category.

Stacks 0D70 provides two constructions of the augmentation's morphism of topoi: a uniform one,
whose direct image is a limit over the simplex category, and, in the cocontinuous case, the
morphism of topoi of the cocontinuous functor out of the total category. They agree, but the
agreement is not recorded in this repository, so each part below is stated against the one whose
formalization it uses. Parts (1) and (3) use the cocontinuous one, which is the one Stacks 0D8B
identifies with `j_total` and with `j_n`; part (4) uses the uniform one, whose direct image is by
construction the limit of the cosimplicial sheaf `n ↦ a_{n,*}𝒢_n`.

Part (4) is stated for abelian sheaves, as in the source. The abelian direct image is the limit
of that cosimplicial sheaf over the whole simplex category, and a limit cone over a cosimplicial
object has its degree-zero leg as a limit fork of the two maps in degrees `0 ⇉ 1`, which is the
dual of Simplicial, Lemma 14.20.2. The two vertex maps of the one-simplex are the two cofaces,
and they are the maps `a_{n,*} = j_{n,*}` of the source by the Stacks 0D8B identification of the
degreewise morphisms of topoi.

The simplicial-site situation fixes one universe for the objects and the morphisms of its
component categories and takes its sheaves in that same universe, so the universes of `C`, of
its morphisms, of the index sets of the `K_n` and of the sections all collapse to a single `u`;
`C` is therefore taken small. Sheafification of abelian sheaves on `(C, J)`, which the lower
shriek needs, is then available because a small site is essentially small.

## References

* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 04BG](https://stacks.math.columbia.edu/tag/04BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

namespace SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-! ### The lower shriek on sheaves of sets -/

/-- The extension by zero `a^{Sh}_! : Sh((C/K)_total) ⥤ Sh(C)` along the augmentation: the sheaf
pullback along the localization functor `j_total` of the total site, that is the left Kan
extension along `j_total` followed by sheafification. -/
def augmentationSheafLowerShriek :
    Sheaf ((situation J K).totalTopology) (Type u) ⥤ Sheaf J (Type u) :=
  Functor.sheafPullbackConstruction.sheafPullback (totalForget K) (Type u)
    ((situation J K).totalTopology) J

/-- **Stacks 09WM, part (1), when `C` has all fibre products.**
The functor `a^{Sh}_! : Sh((C/K)_total) ⥤ Sh(C)` is left adjoint
to the inverse image `a^{-1} : Sh(C) ⥤ Sh((C/K)_total)` of the augmentation.

The inverse image of the augmentation is restriction along `j_total`, because `j_total` is
cocontinuous as well as continuous, and restriction along a continuous functor has a left
adjoint. -/
def augmentationSheafLowerShriekAdjunction :
    augmentationSheafLowerShriek J K ⊣
      (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi
        (augmentation J K)).inverseImage :=
  ((totalForget K).sheafAdjunctionLowerShriek (Type u)
    ((situation J K).totalTopology) J).ofNatIsoRight (totalInverseImageIso J K).symm

/-! ### The lower shriek on abelian sheaves -/

/-- The extension by zero `a_! : Ab((C/K)_total) ⥤ Ab(C)` along the augmentation: the sheaf
pullback of abelian sheaves along the localization functor `j_total` of the total site. -/
def augmentationAbelianLowerShriek :
    Sheaf ((situation J K).totalTopology) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  Functor.sheafPullbackConstruction.sheafPullback (totalForget K) AddCommGrpCat.{u}
    ((situation J K).totalTopology) J

/-- **Stacks 09WM, part (2), when `C` has all fibre products.**
The functor `a_! : Ab((C/K)_total) ⥤ Ab(C)` is left adjoint to the
inverse image `a^{-1} : Ab(C) ⥤ Ab((C/K)_total)` of the augmentation, which on abelian sheaves as
on sheaves of sets is restriction along `j_total`. -/
def augmentationAbelianLowerShriekAdjunction :
    augmentationAbelianLowerShriek J K ⊣
      (totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).totalTopology) J :=
  (totalForget K).sheafAdjunctionLowerShriek AddCommGrpCat.{u}
    ((situation J K).totalTopology) J

/-! ### The inverse image in a simplicial degree -/

/-- **Stacks 09WM, part (3), when `C` has all fibre products.**
The inverse image of the augmentation followed by restriction to
the simplicial degree `n` is the inverse image `a_n^{-1}` of the augmentation of that degree,
which by Stacks 0D8B is the inverse image of the morphism of topoi of the localization functor
`j_n : C/K_n ⥤ C`, that is restriction along `j_n`. So `a^{-1}ℱ` is in degree `n` the sheaf
`a_n^{-1}ℱ`. -/
def augmentationInverseImageComponentIso (n : SimplexCategory) :
    (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi
          (augmentation J K)).inverseImage ⋙ (situation J K).restrict n ≅
      (localizationMorphism J K n).inverseImage :=
  Functor.isoWhiskerLeft _
      (SimplicialSiteSituation.componentInverseImageIsoPushforward (situation J K) n).symm ≪≫
    CocontinuousSimplicialSite.Augmentation.componentInclusionCompInverseImageIso
      (augmentation J K) n ≪≫
    componentInverseImageIso J K n

/-! ### The abelian direct image as an equalizer -/

variable (G : Sheaf ((situation J K).totalTopology) AddCommGrpCat.{u})

/-- The cosimplicial abelian sheaf `n ↦ a_{n,*}𝒢_n` on `(C, J)` attached to an abelian sheaf `𝒢`
on the total site: in simplicial degree `n` the direct image along the augmentation of that
degree of the restriction of `𝒢` to `C/K_n`. -/
def augmentationAbelianComponentDiagram : CosimplicialObject (Sheaf J AddCommGrpCat.{u}) :=
  SimplicialSiteSituation.Augmentation.abelianCechDiagram (situation J K) (Cat.of C) J
    (situationAugmentation J K) G

/-- The term of `n ↦ a_{n,*}𝒢_n` in simplicial degree `n`. -/
theorem augmentationAbelianComponentDiagram_obj (n : SimplexCategory) :
    (augmentationAbelianComponentDiagram J K G).obj n =
      (SimplicialSiteSituation.Augmentation.abelianComponentPushforward (situation J K)
        (Cat.of C) J (situationAugmentation J K) n).obj G := rfl

/-- The cone over `n ↦ a_{n,*}𝒢_n` with vertex the direct image `a_*𝒢`, whose legs are the
canonical projections of that direct image onto the degreewise direct images. -/
def augmentationAbelianPushforwardCone :
    Cone (augmentationAbelianComponentDiagram J K G) :=
  SimplicialSiteSituation.Augmentation.abelianCechCone (situation J K) (Cat.of C) J
    (situationAugmentation J K) G

/-- **Stacks 09WM, part (4), when `C` has all fibre products.**
The fork of the direct image `a_*𝒢` of an abelian sheaf on the
total site over the two maps `a_{0,*}𝒢_0 ⟶ a_{1,*}𝒢_1` attached to the two vertices of the
one-simplex, which are the two cofaces of the cosimplicial sheaf `n ↦ a_{n,*}𝒢_n`. Its map is the
canonical projection of `a_*𝒢` onto `a_{0,*}𝒢_0`, and it equalises the two because the
projections form a cone. -/
def augmentationAbelianPushforwardFork :
    Fork ((augmentationAbelianComponentDiagram J K G).map
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0))
      ((augmentationAbelianComponentDiagram J K G).map
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)) :=
  Fork.ofι
    (show (SimplicialSiteSituation.Augmentation.abelianTotalPushforward (situation J K)
        (Cat.of C) J (situationAugmentation J K)).obj G ⟶ _ from
      (augmentationAbelianPushforwardCone J K G).π.app (SimplexCategory.mk 0))
    (CosimplicialObject.cone_condition _ _)

/-- The vertex of that fork is the direct image `a_*𝒢` of Stacks 0D70. -/
theorem augmentationAbelianPushforwardFork_pt :
    (augmentationAbelianPushforwardFork J K G).pt =
      (SimplicialSiteSituation.Augmentation.abelianTotalPushforward (situation J K) (Cat.of C) J
        (situationAugmentation J K)).obj G := rfl

/-- **Stacks 09WM, part (4), when `C` has all fibre products.**
That fork is a limit: the direct image `a_*𝒢` is the equalizer of
the two maps `a_{0,*}𝒢_0 ⟶ a_{1,*}𝒢_1`.

The direct image is by construction the limit of the cosimplicial sheaf `n ↦ a_{n,*}𝒢_n` over the
whole simplex category, and the degree-zero leg of such a limit is a limit fork of the two maps
in degrees `0 ⇉ 1`, which is the dual of Simplicial, Lemma 14.20.2. -/
def augmentationAbelianPushforwardForkIsLimit :
    IsLimit (augmentationAbelianPushforwardFork J K G) :=
  CosimplicialObject.isLimitForkOfIsLimit _ _
    (SimplicialSiteSituation.Augmentation.abelianCechCone_isLimit (situation J K) (Cat.of C) J
      (situationAugmentation J K) G)

end SimplicialSemiRepresentable

end CategoryTheory

end
