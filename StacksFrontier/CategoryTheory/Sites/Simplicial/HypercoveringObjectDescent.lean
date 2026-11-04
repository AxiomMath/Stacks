module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Objects
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringLocallyFull

/-!
# Cohomological descent for a hypercovering of an object

Let `(C, J)` be a site with fibre products, let `X` be an object of `C` and let `K` be a
hypercovering of `X` in the sense of Stacks 01G5: a simplicial object of the category
`SR(C, X) = FormalCoproduct (Over X)` of semi-representable objects over `X` whose degree-zero
term covers `X` and whose canonical map to each successive coskeleton is covering.

The site `C/X` has a final object, namely `X` itself, and therefore has equalizers and fibre
products, and `K` is a simplicial semi-representable object *of that site*. So the whole
simplicial-site apparatus applies verbatim with `C/X` in place of `C`: the simplicial family of
sites `n ↦ (C/X)/K_n`, its total site `(C/K)_total`, and the augmentation
`a : Sh((C/K)_total) ⟶ Sh(C/X)` given by the degree-zero localization functor are the objects
`CategoryTheory.SimplicialSemiRepresentable.situation`,
`.totalLocalizationMorphism` and `.augmentation` of Stacks 0D8B, instantiated at the site
`(Over X, J.over X)`. This is the identification Stacks 0D8C makes, and it is what lets
Stacks 0D8K be read off Stacks 0D8E.

Stacks 0D8K asserts that `a^{-1}` is fully faithful with essential image the cartesian sheaves,
for sheaves of sets and for sheaves of abelian groups, with `a_*` as quasi-inverse. This file
proves, for a hypercovering of `X`, the two clauses that follow from the *degree-zero* condition
on `K` alone:

* `a^{-1}` is faithful, and
* every sheaf in the essential image of `a^{-1}` is cartesian.

The input for the first is that the localization functor `j_total : (C/K)_total ⥤ C/X` is cover
dense, which here is immediate from the hypercovering hypothesis and fibre products: the
degree-zero condition says that `{K_{0,i} → X}` is a covering family of `X`, and the sieve it
generates, pulled back along the structure morphism of an object `V` of `C/X`, consists of arrows
whose source maps to a component of `K_0` over `X`. Restriction along a continuous cover-dense
functor is faithful, which is Stacks 04D9. The second is Stacks 0D7H together with invariance of
cartesianness under isomorphism, and uses no condition on `K` at all.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.ofArrows_mem_of_isCoveringOver_terminal`: the
  degree-zero clause of Stacks 01G5 says exactly that the structure morphisms of the summands of
  `K_0` form a covering family of `X`.
* `CategoryTheory.SimplicialSemiRepresentable.degreeZeroSieveOver_mem`: every object of `C/X` is
  covered by objects admitting a morphism over `X` to a component of `K_0`.
* `CategoryTheory.SimplicialSemiRepresentable.isCoverDense_totalForget_over`: the localization
  functor of the total site of a hypercovering of `X` is cover dense over `C/X`.
* `CategoryTheory.SimplicialSemiRepresentable.faithful_inverseImage_over` and
  `.faithful_totalInverseImage_over`: **Stacks 0D8K (1)**, the faithfulness half, for the inverse
  image read as restriction along `j_total` and for the inverse image of the morphism of topoi
  which Stacks 0D70 attaches to the augmentation.
* `CategoryTheory.SimplicialSemiRepresentable.faithful_abelianInverseImage_over`:
  **Stacks 0D8K (2)**, the faithfulness half, on abelian sheaves.
* `CategoryTheory.SimplicialSemiRepresentable.isCartesianSheaf_of_mem_essImage_over` and
  `.isCartesianAbSheaf_of_mem_essImage_over`: **Stacks 0D8K (1) and (2)**, the inclusion of the
  essential image of `a^{-1}` in the cartesian sheaves, of sets and of abelian groups.

## Implementation notes

The hypothesis "`C` has fibre products" of Stacks 0D8K is the `HasPullbacks C` instance. It is
used three times: it makes `Over X` have pullbacks, hence makes the localized topology
`J.over X` admit pullbacks of coverings, which is what the simplicial-site construction of
Stacks 0D8B requires; it makes the coskeleta of simplicial objects of `SR(C, X)` exist, so that
the hypercovering predicate of Stacks 01G5 is well formed; and nothing else. In particular no
fibre product is formed by hand below — the covering sieve of `degreeZeroSieveOver_mem` is
obtained from the pullback of a *sieve*, so the arrows produced are arbitrary local lifts rather
than the projections of a chosen fibre product.

The pretopology `P` on `C` and the topology `P.toGrothendieck` it generates are both named,
because the hypercovering predicate of Stacks 01G5 is stated for a pretopology — a covering
family, not a covering sieve — while the site `C/X` and the whole simplicial-site apparatus are
stated for a Grothendieck topology.

The two remaining clauses of Stacks 0D8K — that `a^{-1}` is full, and that every cartesian sheaf
lies in its essential image, so that `a_*` is a quasi-inverse — are *not* proved here, and no
`0D8K` attribute is placed on anything asserting them. They are the two clauses of Stacks 0D8E
which the library does not carry either; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringDescent.lean`. Both need the higher
conditions on a hypercovering, which the degree-zero condition used here does not supply.

Each of the two reduces to a single missing statement about `K`.

Fullness of `a^{-1}` is `CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous`
applied to `totalForget K`, whose only hypothesis beyond the cover density proved above is
`CategoryTheory.Functor.IsLocallyFull (P.toGrothendieck.over X) (totalForget K)`. Unwound at
objects of simplicial degrees `n` and `m`, that asks for a covering sieve of local lifts of a
morphism of `C/X`, and a morphism of the total site out of a degree-`p` object admits simplex
maps `⦋n⦌ ⟶ ⦋p⦌` and `⦋m⦌ ⟶ ⦋p⦌`; so it is the local existence of a `p`-simplex of `K` carrying
two prescribed charts on two complementary faces, which is the degree-`p` clause of Stacks 01G5
read through the join `⦋n⦌ ⋆ ⦋m⦌`. The library carries the coskeleton form of that clause
(`Stacks.CategoryTheory.Hypercovering.locallySurjective_higherMatchingMap_of_isHypercovering`)
but not the prescribed-faces form.

The unit `G ⟶ a_* a^{-1} G` being an isomorphism gives that `a^{-1}` is **fully faithful**, which
is the first clause above and not the essential-image one: essential surjectivity onto the
cartesian sheaves is the *counit* `a^{-1} a_* F ⟶ F` being an isomorphism for cartesian `F`, and
that is the long second half of the source's proof. The unit is an isomorphism by Stacks 0D70 (3) —
the total direct image is the equalizer of the two degree-one transitions,
`CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalDirectImageForkIsLimit` — and Stacks
0D89, which identifies `a_{n,*} a_n^{-1}` with `SheafHom(F(K_n)^#, -)` on `C/X` and is
`CategoryTheory.SemiRepresentable.componentwiseLocalizationPushforwardPullbackNatIsoSheafHom`, is
the statement that `F(K_1)^# ⇉ F(K_0)^# ⟶ ⊤` is a coequalizer of sheaves on `C/X`; the fork it has
to be compared with is produced by `CategoryTheory.SheafHomAdj.isLimitForkSheafHomContraMap` and
`.sheafHomFunctorTerminalIso` below. The coequalizer itself is within reach of
`CategoryTheory.Sheaf.isColimitCoforkOfEpiOfEpi`, the two epimorphisms being the degree-zero and
degree-one clauses of Stacks 01G5 read through `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`.
What is missing is the comparison of the two forks, which needs Stacks 0D89 to be natural in the
semi-representable object as well as in the sheaf; it is stated only for a fixed object. For the
*base* site this is no longer missing — the naturality in the semi-representable object of Stacks
0D86 is `CategoryTheory.SemiRepresentable.localizationPushforwardPullbackNatIsoSheafHom_naturality`
in `StacksFrontier/CategoryTheory/Sites/SemiRepresentable/PushPullNaturality.lean`. Over `C/X` it is
still absent: `componentwiseLocalizationPushforwardPullbackNatIsoSheafHom` has no naturality-in-`K`
companion.

## References

* [Stacks Project, Tag 0D8K](https://stacks.math.columbia.edu/tag/0D8K)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8C](https://stacks.math.columbia.edu/tag/0D8C)
* [Stacks Project, Tag 0D89](https://stacks.math.columbia.edu/tag/0D89)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 04D9](https://stacks.math.columbia.edu/tag/04D9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasPullbacks C]

/-- The degree-zero clause of Stacks 01G5, unwound: the unique morphism from a semi-representable
object `Z` over `X` to the terminal object of `SR(C, X)` is covering only if the structure
morphisms of the summands of `Z` form a covering family of `X`.

This is the converse of
`Stacks.CategoryTheory.Hypercovering.isCoveringOver_terminal_of_hom_mem`, and is proved the same
way: the terminal object is the one-summand object `X → X`, the morphism to it has `(Z.obj i).hom`
for its components, and reindexing along the bijection of `Z.I` with the fibre over the unique
index identifies the two covering families. -/
theorem ofArrows_mem_of_isCoveringOver_terminal (J : Pretopology C) {X : C}
    (Z : FormalCoproduct.{u} (Over X)) (hZ : IsCoveringOver J (terminal.from Z)) :
    Presieve.ofArrows (fun i : Z.I ↦ (Z.obj i).left) (fun i ↦ (Z.obj i).hom) ∈ J X := by
  let T : FormalCoproduct.{u} (Over X) := ⟨PUnit.{u + 1}, fun _ ↦ Over.mk (𝟙 X)⟩
  have hT : IsTerminal T := FormalCoproduct.isTerminalIncl (Over.mk (𝟙 X)) Over.mkIdTerminal
  let g : Z ⟶ T :=
    { f := fun _ ↦ PUnit.unit
      φ := fun i ↦ (Over.homMk (Z.obj i).hom (by simp) : Z.obj i ⟶ Over.mk (𝟙 X)) }
  have hg : IsCoveringOver J g := by
    rw [hT.hom_ext g (terminal.from Z ≫ (terminalIsTerminal.uniqueUpToIso hT).hom)]
    exact hZ.comp_isIso J _
  have key := hg PUnit.unit
  simp only [eqToHom_refl, Category.comp_id] at key
  have himg : Presieve.ofArrows (fun i : { i : Z.I // g.f i = PUnit.unit } ↦ (Z.obj i.1).left)
      (fun i ↦ (g.φ i.1).left) =
        Presieve.ofArrows (fun i : Z.I ↦ (Z.obj i).left) (fun i ↦ (Z.obj i).hom) :=
    ofArrows_reindex (Equiv.subtypeUnivEquiv fun _ ↦ rfl) (fun i : Z.I ↦ (Z.obj i).left)
      (fun i ↦ (Z.obj i).hom)
  exact himg ▸ key

variable (P : Pretopology C) {X : C} (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- **The degree-zero covering condition of Stacks 0D8K, as a covering sieve of `C/X`.** For a
hypercovering `K` of `X`, every object `V` of `C/X` is covered by objects admitting a morphism
over `X` to a component of `K_0`.

The degree-zero clause of Stacks 01G5 makes `{K_{0,i} → X}` a covering family of `X`; pulling the
sieve it generates back along the structure morphism of `V` gives a covering sieve of the
underlying object of `V`, and an arrow in that sieve factors through some `K_{0,i} → X` by a
morphism which, by the defining square of `Over X`, is a morphism over `X`. -/
theorem degreeZeroSieveOver_mem
    (hK : IsCoveringOver P (terminal.from (K.obj (op ⦋0⦌)))) (V : Over X) :
    degreeZeroSieve K V ∈ (P.toGrothendieck.over X) V := by
  set Z := K.obj (op ⦋0⦌)
  have hgen : Sieve.generate
      (Presieve.ofArrows (fun i : Z.I ↦ (Z.obj i).left) (fun i ↦ (Z.obj i).hom)) ∈
        P.toGrothendieck X :=
    ⟨_, ofArrows_mem_of_isCoveringOver_terminal P Z hK, Sieve.le_generate _⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (P.toGrothendieck.overEquiv_symm_mem_over V _ (P.toGrothendieck.pullback_stable V.hom hgen))
  intro W f hf
  rw [Sieve.overEquiv_symm_iff] at hf
  obtain ⟨Y, p, q, ⟨i⟩, hcomm⟩ := hf
  exact ⟨i, ⟨Over.homMk p (hcomm.trans (Over.w f))⟩⟩

/-- **The cover density of Stacks 0D8K.** The localization functor
`j_total : (C/K)_total ⥤ C/X` of the total site of a hypercovering of `X` is cover dense: the
sieve of arrows factoring through its image contains the covering sieve of
`degreeZeroSieveOver_mem`. -/
theorem isCoverDense_totalForget_over
    (hK : IsCoveringOver P (terminal.from (K.obj (op ⦋0⦌)))) :
    (totalForget K).IsCoverDense (P.toGrothendieck.over X) :=
  ⟨fun V => GrothendieckTopology.superset_covering _
    (degreeZeroSieve_le_coverByImage K V) (degreeZeroSieveOver_mem P K hK V)⟩

/-! ### Faithfulness of the inverse image -/

/-- Restriction along `j_total` is faithful on sheaves with values in any coefficient category. -/
private theorem faithful_sheafPushforwardContinuous_totalForget_over (hK : IsHypercovering P K)
    (A : Type*) [Category A] :
    ((totalForget K).sheafPushforwardContinuous A
      ((situation (P.toGrothendieck.over X) K).totalTopology)
      (P.toGrothendieck.over X)).Faithful :=
  let := isCoverDense_totalForget_over P K hK.1
  sheafPushforwardContinuous_faithful_of_isCoverDense (totalForget K)
    ((situation (P.toGrothendieck.over X) K).totalTopology) (P.toGrothendieck.over X) A

/-- **Stacks 0D8K (1), the faithfulness half.** For a hypercovering `K` of `X` the inverse image
`a^{-1} : Sh(C/X) ⥤ Sh((C/K)_total)` of the augmentation is faithful.

The inverse image is restriction along `j_total`, which is continuous and cover dense, and
restriction along such a functor is faithful by Stacks 04D9. -/
@[stacks 0D8K "part (1): a^{-1} on sheaves of sets is faithful"]
theorem faithful_inverseImage_over (hK : IsHypercovering P K) :
    (totalLocalizationMorphism (P.toGrothendieck.over X) K).inverseImage.Faithful :=
  faithful_sheafPushforwardContinuous_totalForget_over P K hK _

/-- **Stacks 0D8K (1), the faithfulness half**, for the inverse image of the morphism of topoi
which Stacks 0D70 attaches to the augmentation. By Stacks 0D8B that functor is isomorphic to
restriction along `j_total`, and faithfulness is invariant under isomorphism of functors. -/
@[stacks 0D8K "part (1): a^{-1} of Stacks 0D70 on sheaves of sets is faithful"]
theorem faithful_totalInverseImage_over (hK : IsHypercovering P K) :
    Functor.Faithful
      (augmentation (P.toGrothendieck.over X) K).totalMorphismOfTopoi.inverseImage :=
  @Functor.Faithful.of_iso _ _ _ _ _ _ (faithful_inverseImage_over P K hK)
    (totalInverseImageIso (P.toGrothendieck.over X) K).symm

/-- **Stacks 0D8K (2), the faithfulness half.** For a hypercovering `K` of `X` the inverse image
`a^{-1} : Ab(C/X) ⥤ Ab((C/K)_total)` of the augmentation — restriction along `j_total` on abelian
sheaves, as in Stacks 09WM (2) — is faithful.

Cover density of `j_total` is a statement about the site, so the argument of
`faithful_inverseImage_over` applies at any coefficient category. -/
@[stacks 0D8K "part (2): a^{-1} on abelian sheaves is faithful"]
theorem faithful_abelianInverseImage_over (hK : IsHypercovering P K) :
    ((totalForget K).sheafPushforwardContinuous Ab.{u}
      ((situation (P.toGrothendieck.over X) K).totalTopology)
      (P.toGrothendieck.over X)).Faithful :=
  faithful_sheafPushforwardContinuous_totalForget_over P K hK _

/-! ### The essential image consists of cartesian sheaves -/

/-- **Stacks 0D8K (1), the fullness half.** For a hypercovering `K` of `X` the inverse image
`a^{-1} : Sh(C/X) ⥤ Sh((C/K)_total)` of the augmentation is full.

The inverse image is restriction along `j_total`, which is continuous, cover dense by the
degree-zero clause of Stacks 01G5 and locally full by
`CategoryTheory.SimplicialSemiRepresentable.isLocallyFull_totalForget_over`; restriction along
such a functor is full. -/
@[stacks 0D8K "part (1): a^{-1} on sheaves of sets is full"]
theorem full_inverseImage_over (hK : IsHypercovering P K) :
    (totalLocalizationMorphism (P.toGrothendieck.over X) K).inverseImage.Full :=
  full_inverseImage_of_isLocallyFull (P.toGrothendieck.over X) K
    (isCoverDense_totalForget_over P K hK.1) (isLocallyFull_totalForget_over P K hK)

/-- **Stacks 0D8K (1), full faithfulness** of the inverse image of the augmentation. -/
def fullyFaithfulInverseImageOver (hK : IsHypercovering P K) :
    (totalLocalizationMorphism (P.toGrothendieck.over X) K).inverseImage.FullyFaithful :=
  fullyFaithfulInverseImage (P.toGrothendieck.over X) K
    (isCoverDense_totalForget_over P K hK.1) (isLocallyFull_totalForget_over P K hK)

/-- **Stacks 0D8K (1), the degree-zero identification `E = a_* a^{-1} E`.** For a hypercovering
`K` of `X` and every sheaf of sets `E` on `C/X` the canonical map `E ⟶ a_* a^{-1} E` is an
isomorphism, `a^{-1}` being restriction along `j_total`.

The unit of an adjunction with fully faithful left adjoint is invertible, and `a^{-1}` is fully
faithful by `fullyFaithfulInverseImageOver`. -/
@[stacks 0D8K "part (1): the unit E = a_*a⁻¹E on sheaves of sets is an isomorphism"]
theorem isIso_unit_over (hK : IsHypercovering P K) :
    IsIso (totalLocalizationMorphism (P.toGrothendieck.over X) K).adj.unit :=
  isIso_unit_of_isLocallyFull (P.toGrothendieck.over X) K
    (isCoverDense_totalForget_over P K hK.1) (isLocallyFull_totalForget_over P K hK)

/-- **Stacks 0D8K (2), the fullness half.** The inverse image
`a^{-1} : Ab(C/X) ⥤ Ab((C/K)_total)` of the augmentation is full.

Cover density and local fullness of `j_total` are statements about the site, so the argument of
`full_inverseImage_over` applies at any coefficient category. -/
@[stacks 0D8K "part (2): a^{-1} on abelian sheaves is full"]
theorem full_abelianInverseImage_over (hK : IsHypercovering P K) :
    ((totalForget K).sheafPushforwardContinuous Ab.{u}
      ((situation (P.toGrothendieck.over X) K).totalTopology)
      (P.toGrothendieck.over X)).Full :=
  full_abelianInverseImage_of_isLocallyFull (P.toGrothendieck.over X) K
    (isCoverDense_totalForget_over P K hK.1) (isLocallyFull_totalForget_over P K hK)

/-- **Stacks 0D8K (2), the degree-zero identification `M = a_* a^{-1} M`** on sheaves of abelian
groups: for a hypercovering `K` of `X` and every sheaf of abelian groups `M` on `C/X` the
canonical map `M ⟶ a_* a^{-1} M` is an isomorphism, `a^{-1}` being restriction along
`j_total`. -/
@[stacks 0D8K "part (2): the unit M = a_*a⁻¹M on abelian sheaves is an isomorphism"]
theorem isIso_abelianUnit_over (hK : IsHypercovering P K) :
    IsIso (abelianTotalAdjunction (P.toGrothendieck.over X) K).unit :=
  isIso_abelianUnit_of_isLocallyFull (P.toGrothendieck.over X) K
    (isCoverDense_totalForget_over P K hK.1) (isLocallyFull_totalForget_over P K hK)

/-! ### The essential image consists of cartesian sheaves -/

/-- **Stacks 0D8K (1), the inclusion of the essential image in the cartesian sheaves.** Every
sheaf of sets on the total site `(C/K)_total` isomorphic to an inverse image along the
augmentation towards `C/X` is cartesian.

This is Stacks 0D7H (1) together with invariance of cartesianness under isomorphism, and uses no
condition on the simplicial semi-representable object `K`. -/
@[stacks 0D8K "part (1): the essential image of a^{-1} consists of cartesian sheaves of sets"]
theorem isCartesianSheaf_of_mem_essImage_over (J : GrothendieckTopology C)
    {F : Sheaf (situation (J.over X) K).totalTopology (Type u)}
    (hF : (totalLocalizationMorphism (J.over X) K).inverseImage.essImage F) :
    (situation (J.over X) K).IsCartesianSheaf F :=
  isCartesianSheaf_of_mem_essImage (J.over X) K hF

/-- **Stacks 0D8K (2), the inclusion of the essential image in the cartesian sheaves.** Every
sheaf of abelian groups on the total site `(C/K)_total` isomorphic to an inverse image along the
augmentation towards `C/X` is cartesian.

Cartesianness of an abelian sheaf is cartesianness of its underlying sheaf of sets, and the
underlying sheaf of the restriction of `𝒢` along `j_total` is the restriction of the underlying
sheaf of `𝒢`, both being a composition of functors. -/
@[stacks 0D8K "part (2): the essential image of a^{-1} consists of cartesian abelian sheaves"]
theorem isCartesianAbSheaf_of_mem_essImage_over (J : GrothendieckTopology C)
    {F : Sheaf (situation (J.over X) K).totalTopology Ab.{u}}
    (hF : ((totalForget K).sheafPushforwardContinuous Ab.{u}
      ((situation (J.over X) K).totalTopology) (J.over X)).essImage F) :
    (situation (J.over X) K).IsCartesianAbSheaf F :=
  isCartesianAbSheaf_of_mem_essImage (J.over X) K hF

end CategoryTheory.SimplicialSemiRepresentable

end
