module

public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.DerivedComparisonBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceAbutment
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FirstQuadrantAbutment
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The abutment of the hypercovering spectral sequence is cohomology on the covered object

`StacksFrontier/CategoryTheory/Sites/Hypercovering/SpectralSequenceAbutment.lean` builds the
functorial filtered abutment of the hypercovering spectral sequence of clause (3) of
[Stacks, Tag 01GY], abutting to the cohomology of the total complex `Tot(Č^•(K, I^•(F)))` of the
Čech double complex of the chosen injective resolution. What clause (3) asserts is that it abuts
to `H^{p+q}(X, F)`. This file supplies the identification at every object and *naturally in the
hypercovering and in the coefficient sheaf simultaneously*, which is the shape clause (3)
asserts.

The mathematical content is [Stacks, Tag 01GV] together with [Stacks, Tag 01GW] and Weibel's
acyclic assembly lemma, already available as
`Stacks.CategoryTheory.Hypercovering.quasiIso_hypercoverAugCochain`: the augmentation
`Γ(X, I^•) ⟶ Tot(Č^•(K, I^•))` of the hypercover total complex by the complex of sections is a
quasi-isomorphism at a bounded-below complex of injective abelian sheaves. Composed with
[Stacks, Tag 03AY] on a small site -- `Stacks.Cohomology.cohomologyPresheafIsoResolution` at
`op X` -- that is the abutment identification.

## The two double complexes

The augmentation is stated for `hypercoverBicomplexFunctor`, which applies
`hypercoverCochainIntFunctor` degreewise to a `ℤ`-indexed complex of sheaves, while the spectral
sequence is built on `hypercoverDouble`, which applies the Čech complex functor degreewise to the
`ℕ`-indexed resolution and then extends *both* indices by zero. The two agree because the Čech
complex functor and extension by zero are additive, and the comparison is
`CategoryTheory.Functor.mapExtendNatIso` used twice: once for
`hypercoverCochainIntFunctor` itself and once for `ComplexShape.embedding.extendFunctor` in the
inner index. Two of the three composition steps are `rfl` -- `hypercoverCochainNatFunctor J X K`
is `sheafToPresheaf ⋙ (cechComplexOverBifunctor X).obj (op K)` on the nose, and
`Functor.mapHomologicalComplex` of a composite is the composite of the
`Functor.mapHomologicalComplex`es -- so `hypercoverDoubleBridge` is a composite of two instances
of one lemma.

Both comparisons are assembled as isomorphisms of *functors* of the `ℕ`-indexed complex of
sheaves, never of their components. `HomologicalComplex₂.HasTotal` is data rather than a
proposition, so two independently synthesized total complexes of one double complex are distinct
terms that no rewrite identifies; whiskering the functor isomorphism with
`StacksDraft.TotalComplexQuasiIso.totalComplexFunctor` keeps every total complex occurring in the
comparison the value of a single functor, and the obstruction does not arise. This is the device
recorded in the implementation notes of `DerivedComparisonBoundedBelow.lean` for
`hypercoverCochainTotalSingleIso`.

## What is here and what is not

**Nothing here carries the tag `01GY`.** The covering set of that tag is three claim-sites --
the comparison map, the cohomology comparison and the spectral sequence -- which are placed
together; this file supplies the last of the three.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverDoubleBridge`,
  `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverTotalBridge`: the comparison of the two
  double complexes, and of their total complexes, as isomorphisms of functors of the `ℕ`-indexed
  complex of sheaves.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverResolutionTotalFunctor`:
  `Y ↦ Tot(Č^•(K, Y))`, the functor the spectral sequence's total complex is a value of.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAbutmentUnit`: the comparison
  `H^n(Y(X)) ⟶ H^n(Tot(Č^•(K, Y)))` as a natural transformation of functors of `Y`, which is
  what makes the whole identification natural for free.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverResolutionAbutmentIso`:
  `H^n(Tot(Č^•(K, Y))) ≅ H^n(Y(X))` for a complex `Y` of injective abelian sheaves.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAbutmentIso`: **the abutment
  identification** `H^n(Tot(Č^•(K, I^•(F)))) ≅ H^n(X, F)`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoveringAbutment`: the
  `Stacks.Cohomology.Leray.FirstQuadrantAbutsTo` of the hypercovering spectral sequence at a
  hypercovering and a coefficient sheaf, abutting to `H^{p+q}(X, F)`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.cechPullbackNat`,
  `Stacks.CategoryTheory.Hypercovering.Functorial.cechPullbackInt`,
  `Stacks.CategoryTheory.Hypercovering.Functorial.cechPullbackBicomplex`,
  `Stacks.CategoryTheory.Hypercovering.Functorial.cechPullbackResolutionTotal`: the Čech pullback
  along a morphism `ρ : L ⟶ K` of simplicial semi-representable objects over `X`, on the complex of
  sections in `ℕ`- and in `ℤ`-degrees, on the Čech double complex and on its total complex.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoveringCohomologyFunctor`: the asserted
  abutment `H^{p+q}(X, F)` as a functor of the hypercovering and the sheaf.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAbutmentNatIso`: the abutment
  identification as an isomorphism of *functors*.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoveringCohomologyAbutment`: the
  `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` of clause (3) -- the hypercovering
  spectral sequence abutting to `H^{p+q}(X, F)` functorially.

## Main results

* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverResolutionAbutmentIso_inv` and
  `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverResolutionAbutmentIso_naturality`: the
  identification is the inverse of `hypercoverAbutmentUnit`, and therefore natural in the complex
  of injectives -- which is every step of the naturality in the sheaf except [Stacks, Tag 03AY].
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverDoubleMap_id_fst` and
  `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverFilteredMap_id_fst_hom`: at a morphism
  whose hypercovering component is the identity, the morphism of total complexes the spectral
  sequence moves along is `hypercoverResolutionTotalFunctor` of the chosen descent.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAbutmentDescSquare` and
  `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAbutmentIso_naturality_sheaf`: **the
  abutment identification is natural in the coefficient sheaf**, for the chosen descent of a
  morphism of sheaves to the chosen injective resolutions -- the form in which
  `hypercoverFiltrationFunctor` moves.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAbutmentIso_naturality_hypercovering`
  and `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAbutmentIso_naturality`: **the
  abutment identification is natural in the hypercovering**, and therefore in the pair.

## Implementation notes

The naturality of the abutment identification in the **hypercovering** is the one half of
clause (3) of [Stacks, Tag 01GY] that is not formal. It rests on
`Stacks.CategoryTheory.Hypercovering.sectionsComparisonInt_comp` of
`StacksFrontier/AlgebraicGeometry/ProEtale/BigSmall/HypercoverTotalComplex.lean`: the augmentation
`Γ(X, F)[0] ⟶ s(F(K))` followed by a Čech pullback along `ρ : L ⟶ K` is the augmentation at `L`.
That lemma is stated for an arbitrary comparison map whose components are restriction along the
structure morphisms of `ρ`, a hypothesis in the vocabulary of `SectionsOver.evalOpProductIso` and
`Limits.Pi.π`; `cechPullbackNat_pi` discharges it for the actual Čech pullback, which is what
makes the chain usable here. This arrangement is what the `@[no_expose]` on
`sectionsComparisonInt` forces: its body mentions `private` declarations of that module, so no
identification of its degree-`0` component is available outside it, and the naturality has to be
exported as a statement rather than reconstructed.

From there the chain is formal. `sectionsComparisonInt_comp_cechPullback` lifts to the double
complexes by `NatTrans.mapHomologicalComplex` and to the total complexes by the total complex
functor, which gives `hypercoverAugCochain_app_comp_cechPullback` with no analysis of a component
of a total complex -- the `totalSingleRowZeroUnit` prefix of `hypercoverAugCochain` is common to
`K` and `L`. The two bridges are natural in the hypercovering by
`CategoryTheory.Functor.mapExtendNatIso_naturality_natTrans` -- extension by zero commutes with a
natural transformation of additive functors, the companion of the naturality in the complex of
`StacksFrontier/Algebra/Homology/Resolution/NatIntBridge.lean` -- together with one whiskering
interchange. The three remaining factors of
`hypercoverAbutmentUnit` do not mention the hypercovering, so
`hypercoverAbutmentUnit_app_comp_cechPullback` follows, and
`hypercoverResolutionAbutmentIso_naturality_hypercovering` is that read forward.

Assembling the two halves into an isomorphism of functors needs one further step:
`hypercoverDoubleMap (ρ.op, 𝟙 F)` carries `CategoryTheory.InjectiveResolution.desc (𝟙 F)` rather
than the identity, so it is only *homotopic* to the Čech pullback; that is
`homologyMap_hypercoverFilteredMap_id_snd`, by `cechDoubleSheaf₂Homotopy` of
`InjectiveResolution.descIdHomotopy` and homotopy invariance of the cohomology of a total
complex.

## Namespace

The declarations of this file live in `Stacks.CategoryTheory.Hypercovering.Functorial`, the
namespace of the small-site, two-variable-functorial development of clause (3) of
[Stacks, Tag 01GY]; the fixed-hypercovering development of
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence` keeps the enclosing namespace
`Stacks.CategoryTheory.Hypercovering`. See the namespace note of
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceSmallSite`.

## References

* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01GW](https://stacks.math.columbia.edu/tag/01GW)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape Simplicial
open StacksDraft.TotalComplexQuasiIso

universe v

/-! ### Extension by zero commutes with a natural transformation of additive functors -/

namespace CategoryTheory.Functor

section MapExtend

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {D₁ : Type*} {D₂ : Type*} [Category D₁] [Category D₂]
  [Preadditive D₁] [Preadditive D₂] [HasZeroObject D₁] [HasZeroObject D₂]
  (F F' : D₁ ⥤ D₂) [F.Additive] [F'.Additive]

/-- **`CategoryTheory.Functor.mapExtendIso` is natural in the functor.**
`StacksFrontier/Algebra/Homology/Resolution/NatIntBridge.lean` has the naturality in the *complex*;
this is the other variable, and it is proved the same way -- degreewise, through
`Stacks.DerivedIndexing.mapExtendXIsoSymm_hom_of_r_eq_some` in the degrees in the range of the
embedding and by vanishing of the target outside it. -/
lemma mapExtendIso_hom_naturality_natTrans (α : F ⟶ F')
    (Y : HomologicalComplex D₁ c) (e : c.Embedding c') [e.IsRelIff] :
    (NatTrans.mapHomologicalComplex α c').app (Y.extend e) ≫ (F'.mapExtendIso Y e).hom =
      (F.mapExtendIso Y e).hom ≫
        HomologicalComplex.extendMap ((NatTrans.mapHomologicalComplex α c).app Y) e := by
  ext i'
  rcases hi : e.r i' with _ | i
  · exact (HomologicalComplex.isZero_extend_X' _ e i' hi).eq_of_tgt _ _
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, mapExtendIso_hom_f,
      mapExtendIso_hom_f, Stacks.DerivedIndexing.mapExtendXIsoSymm_hom_of_r_eq_some F e Y hi,
      Stacks.DerivedIndexing.mapExtendXIsoSymm_hom_of_r_eq_some F' e Y hi,
      HomologicalComplex.extendMap_f ((NatTrans.mapHomologicalComplex α c).app Y) e
        (ComplexShape.Embedding.f_eq_of_r_eq_some _ hi),
      NatTrans.mapHomologicalComplex_app_f]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, NatTrans.mapHomologicalComplex_app_f]
    rw [← Category.assoc, ← α.naturality, Category.assoc]

/-- **`CategoryTheory.Functor.mapExtendNatIso` is natural in the functor**, the
natural-transformation form of `mapExtendIso_hom_naturality_natTrans`. -/
lemma mapExtendNatIso_naturality_natTrans (α : F ⟶ F') (e : c.Embedding c') [e.IsRelIff] :
    Functor.whiskerLeft (e.extendFunctor D₁) (NatTrans.mapHomologicalComplex α c') ≫
        (F'.mapExtendNatIso e).hom =
      (F.mapExtendNatIso e).hom ≫
        Functor.whiskerRight (NatTrans.mapHomologicalComplex α c) (e.extendFunctor D₂) :=
  NatTrans.ext (funext fun Y ↦ F.mapExtendIso_hom_naturality_natTrans F' α Y e)

end MapExtend

end CategoryTheory.Functor

namespace Stacks.CategoryTheory.Hypercovering.Functorial

variable {C : Type v} [SmallCategory C] [HasPullbacks C] (X : C) (J : Pretopology C)
  (K : SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))

/-! ### The two double complexes agree -/

/-- **The comparison of the two Čech double complexes**, as an isomorphism of functors of the
`ℕ`-indexed complex of sheaves: `hypercoverBicomplexFunctor` applied to the extension by zero of
`Y` is the double complex `hypercoverDouble` is a value of.

Both sides are `Functor.mapHomologicalComplex` and `ComplexShape.embedding.extendFunctor` in one
order or the other, so the comparison is
`CategoryTheory.Functor.mapExtendNatIso` twice: once for `hypercoverCochainIntFunctor` and once
for the extension in the inner index. The remaining steps hold on the nose. -/
def hypercoverDoubleBridge :
    embeddingUpNat.extendFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ⋙
        (hypercoverCochainIntFunctor J X K).mapHomologicalComplex (up ℤ) ≅
      (cechDoubleSheafBifunctor.{v} X J.toGrothendieck).obj (op K) :=
  (hypercoverCochainIntFunctor J X K).mapExtendNatIso embeddingUpNat ≪≫
    Functor.isoWhiskerLeft ((hypercoverCochainNatFunctor J X K).mapHomologicalComplex (up ℕ))
      ((embeddingUpNat.extendFunctor AddCommGrpCat.{v}).mapExtendNatIso embeddingUpNat).symm

/-- **`Y ↦ Tot(Č^•(K, Y))` on `ℕ`-indexed complexes of sheaves.** The total complex of the
spectral sequence is the value of this functor at the chosen injective resolution, so an
isomorphism of functors into it carries the instance-resolved `HomologicalComplex₂.HasTotal` on
both sides. -/
def hypercoverResolutionTotalFunctor :
    CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℕ ⥤
      CochainComplex AddCommGrpCat.{v} ℤ :=
  (cechDoubleSheafBifunctor.{v} X J.toGrothendieck).obj (op K) ⋙
    totalComplexFunctor AddCommGrpCat.{v}

/-- The value of `hypercoverResolutionTotalFunctor` at the chosen injective resolution is the
total complex the hypercovering spectral sequence is built on. -/
lemma hypercoverResolutionTotalFunctor_obj_injectiveResolution
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    (hypercoverResolutionTotalFunctor X J K).obj (injectiveResolution F).cocomplex =
      (hypercoverDouble X J.toGrothendieck (op K, F)).total (up ℤ) :=
  rfl

/-- **The comparison of the two total complexes**, `hypercoverDoubleBridge` whiskered with
`StacksDraft.TotalComplexQuasiIso.totalComplexFunctor`. Whiskering rather than taking components
is what keeps every total complex here the value of one functor; see the module documentation. -/
def hypercoverTotalBridge :
    embeddingUpNat.extendFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ⋙
        hypercoverTotalCochainFunctor J X K ≅ hypercoverResolutionTotalFunctor X J K :=
  Functor.isoWhiskerRight (hypercoverDoubleBridge X J K) (totalComplexFunctor AddCommGrpCat.{v})

/-! ### The augmentation on cohomology -/


/-- **A square of isomorphisms, inverted.** Stated about an abstract category so that the rewrite
happens where every term is a variable; applying it at the concrete spelling is then one
term-mode application, with no unfolding of the functors involved. -/
private theorem comp_inv_eq_inv_comp_of_square {𝒜 : Type*} [Category 𝒜] {A A' B B' : 𝒜}
    (u : A ⟶ B) (u' : A' ⟶ B') [IsIso u] [IsIso u'] (a : A ⟶ A') (b : B ⟶ B')
    (w : a ≫ u' = u ≫ b) : b ≫ inv u' = inv u ≫ a := by
  rw [IsIso.comp_inv_eq, Category.assoc, w, IsIso.inv_hom_id_assoc]


/-! ### The augmentation on cohomology -/


variable {K} in
/-- **The comparison `H^n(Y(X)) ⟶ H^n(Tot(Č^•(K, Y)))`, as a natural transformation** of functors
of the `ℕ`-indexed complex `Y` of abelian sheaves. It is the composite of

* the exactness of evaluation at `X` (`Functor.mapHomologicalComplexHomologyIso`),
* the passage from `ℕ`- to `ℤ`-degrees (`ComplexShape.Embedding.extendFunctorHomologyIso`),
* the commutation of the sections functor with extension by zero
  (`CategoryTheory.Functor.mapExtendNatIso`),
* `H^n` of the augmentation of the hypercover total complex by the complex of sections, and
* `H^n` of the double complex comparison `hypercoverTotalBridge`,

four of which are isomorphisms of functors. Being a composite of natural transformations it is
natural with no work, which is what `hypercoverResolutionAbutmentIso_naturality` is; only the
augmentation fails to be invertible at a general `Y`, and it is invertible as soon as the terms of
`Y` are injective. -/
def hypercoverAbutmentUnit (hK : IsHypercovering J K) (n : ℕ) :
    (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{v}).mapHomologicalComplex (up ℕ) ⋙
        HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{v}) (up ℕ) n ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X) ⟶
      hypercoverResolutionTotalFunctor X J K ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (up ℤ) (n : ℤ) :=
  (Functor.isoWhiskerLeft
        ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{v}).mapHomologicalComplex (up ℕ))
        (((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)).mapHomologicalComplexHomologyIso
          (up ℕ) n)).inv ≫
    (Functor.isoWhiskerLeft ((sheafSectionsFunctor J X).mapHomologicalComplex (up ℕ))
        (embeddingUpNat.extendFunctorHomologyIso AddCommGrpCat.{v} n (n : ℤ) rfl)).inv ≫
    (Functor.isoWhiskerRight ((sheafSectionsFunctor J X).mapExtendNatIso embeddingUpNat)
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (up ℤ) (n : ℤ))).inv ≫
    Functor.whiskerRight
        (Functor.whiskerLeft
          (embeddingUpNat.extendFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{v}))
          (hypercoverAugCochain J X K hK))
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (up ℤ) (n : ℤ)) ≫
    (Functor.isoWhiskerRight (hypercoverTotalBridge X J K)
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (up ℤ) (n : ℤ))).hom


variable {K} in
/-- **The abutment identification at a complex of injective abelian sheaves**:
`H^n(Tot(Č^•(K, Y))) ≅ H^n(Y(X))`.

It is assembled out of the same five factors as `hypercoverAbutmentUnit`, in the opposite order
and as isomorphisms, so that no instance of `CategoryTheory.IsIso` has to be synthesized for a
five-fold composite; `hypercoverResolutionAbutmentIso_inv` records that the two agree. The one
factor that is not an isomorphism of functors is `H^n` of the augmentation, invertible here by
`quasiIso_hypercoverAugCochain`. -/
def hypercoverResolutionAbutmentIso (hK : IsHypercovering J K)
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℕ)
    [∀ p, Injective (Y.X p)] (n : ℕ) :
    ((hypercoverResolutionTotalFunctor X J K).obj Y).homology (n : ℤ) ≅
      (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{v}).mapHomologicalComplex (up ℕ) ⋙
          HomologicalComplex.homologyFunctor _ (up ℕ) n).obj Y).obj (op X) :=
  haveI := quasiIso_hypercoverAugCochain J X K hK (Y.extend embeddingUpNat) 0
  ((Functor.isoWhiskerRight (hypercoverTotalBridge X J K)
          (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (up ℤ) (n : ℤ))).app Y).symm ≪≫
    (asIso (HomologicalComplex.homologyMap
        ((hypercoverAugCochain J X K hK).app (Y.extend embeddingUpNat)) (n : ℤ))).symm ≪≫
    (Functor.isoWhiskerRight ((sheafSectionsFunctor J X).mapExtendNatIso embeddingUpNat)
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (up ℤ) (n : ℤ))).app Y ≪≫
    (Functor.isoWhiskerLeft ((sheafSectionsFunctor J X).mapHomologicalComplex (up ℕ))
        (embeddingUpNat.extendFunctorHomologyIso AddCommGrpCat.{v} n (n : ℤ) rfl)).app Y ≪≫
    (Functor.isoWhiskerLeft
        ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{v}).mapHomologicalComplex (up ℕ))
        (((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)).mapHomologicalComplexHomologyIso
          (up ℕ) n)).app Y

variable {K} in
/-- **The abutment identification is the inverse of `hypercoverAbutmentUnit`**, on the nose: the
inverse of a composite of isomorphisms is the composite of the inverses in the opposite order,
and the component of a composite of natural transformations is the composite of the
components. -/
lemma hypercoverResolutionAbutmentIso_inv (hK : IsHypercovering J K)
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℕ)
    [∀ p, Injective (Y.X p)] (n : ℕ) :
    (hypercoverResolutionAbutmentIso X J hK Y n).inv =
      (hypercoverAbutmentUnit X J hK n).app Y :=
  rfl

variable {K} in
/-- **The abutment identification is natural in the complex of injectives.** This is the
naturality of `hypercoverAbutmentUnit`, which it has for free as a composite of natural
transformations, read in the forward direction. -/
theorem hypercoverResolutionAbutmentIso_naturality (hK : IsHypercovering J K)
    {Y Y' : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℕ}
    [∀ p, Injective (Y.X p)] [∀ p, Injective (Y'.X p)] (ψ : Y ⟶ Y') (n : ℕ) :
    HomologicalComplex.homologyMap ((hypercoverResolutionTotalFunctor X J K).map ψ) (n : ℤ) ≫
        (hypercoverResolutionAbutmentIso X J hK Y' n).hom =
      (hypercoverResolutionAbutmentIso X J hK Y n).hom ≫
        ((((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{v}).mapHomologicalComplex (up ℕ) ⋙
          HomologicalComplex.homologyFunctor _ (up ℕ) n).map ψ)).app (op X) := by
  refine (Iso.eq_comp_inv _).1 ?_
  rw [Category.assoc]
  refine (Iso.inv_comp_eq _).1 ?_
  rw [hypercoverResolutionAbutmentIso_inv, hypercoverResolutionAbutmentIso_inv]
  exact ((hypercoverAbutmentUnit X J hK n).naturality ψ).symm

/-! ### The abutment identification at a coefficient sheaf -/

variable {K} in
/-- **The abutment identification of clause (3) of [Stacks, Tag 01GY]**:
`H^n(Tot(Č^•(K, I^•(F)))) ≅ H^n(X, F)`, the cohomology of the total complex the hypercovering
spectral sequence is built on is the sheaf cohomology of `F` on the covered object.

`hypercoverResolutionAbutmentIso` at the chosen injective resolution, followed by
[Stacks, Tag 03AY] on a small site evaluated at `op X`. -/
def hypercoverAbutmentIso (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (n : ℕ) :
    ((hypercoverDouble X J.toGrothendieck (op K, F)).total (up ℤ)).homology (n : ℤ) ≅
      ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).obj F).obj (op X) :=
  hypercoverResolutionAbutmentIso X J hK (injectiveResolution F).cocomplex n ≪≫
    ((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)).mapIso
      (Stacks.Cohomology.cohomologyPresheafIsoResolution J.toGrothendieck F
        (injectiveResolution F) n)

variable {K} in
/-- The two factors of `hypercoverAbutmentIso`, by definition. Stating them as a `have`-checked
equation is what lets the rewrites below happen: the source of `hypercoverAbutmentIso` is spelled
through `hypercoverDouble` and that of `hypercoverResolutionAbutmentIso` through
`hypercoverResolutionTotalFunctor`, which agree definitionally but not at the `implicit`
transparency a keyed rewrite uses. -/
lemma hypercoverAbutmentIso_hom (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (n : ℕ) :
    (hypercoverAbutmentIso X J hK F n).hom =
      (hypercoverResolutionAbutmentIso X J hK (injectiveResolution F).cocomplex n).hom ≫
        (Stacks.Cohomology.cohomologyPresheafIsoResolution J.toGrothendieck F
          (injectiveResolution F) n).hom.app (op X) :=
  rfl

variable {K} in
/-- **`hypercoverDoubleMap` at a morphism with identity hypercovering component** is the Čech
double complex functor of the fixed hypercovering applied to the chosen descent of the morphism
of sheaves: the `K`-component of the two-variable Čech double complex functor is the identity,
and `CategoryTheory.Functor.uncurry` composes the two components. -/
lemma hypercoverDoubleMap_id_fst {F G : Sheaf J.toGrothendieck AddCommGrpCat.{v}} (g : F ⟶ G) :
    hypercoverDoubleMap X J.toGrothendieck
        ((𝟙 (op K), g) :
          ((op K, F) : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
            Sheaf J.toGrothendieck AddCommGrpCat.{v}) ⟶ (op K, G)) =
      ((cechDoubleSheafBifunctor.{v} X J.toGrothendieck).obj (op K)).map
        (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F)) := by
  dsimp only [hypercoverDoubleMap, cechDoubleSheaf₂, Functor.uncurry_obj_map]
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

variable {K} in
/-- The underlying morphism of complexes of `hypercoverFilteredMap` at a morphism with identity
hypercovering component is `hypercoverResolutionTotalFunctor` of the chosen descent. -/
lemma hypercoverFilteredMap_id_fst_hom {F G : Sheaf J.toGrothendieck AddCommGrpCat.{v}}
    (g : F ⟶ G) :
    (hypercoverFilteredMap X J.toGrothendieck
        ((𝟙 (op K), g) :
          ((op K, F) : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
            Sheaf J.toGrothendieck AddCommGrpCat.{v}) ⟶ (op K, G))).hom =
      (hypercoverResolutionTotalFunctor X J K).map
        (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F)) := by
  rw [hypercoverFilteredMap_hom, hypercoverDoubleMap_id_fst]
  rfl

variable {K} in
/-- **The naturality square of the abutment identification, in the spelling it is proved in.**
Every type here is written through `hypercoverResolutionTotalFunctor`, which is what makes the
goal type-correct at the `implicit` transparency a keyed rewrite uses;
`hypercoverAbutmentIso_naturality_sheaf` is this statement read through `hypercoverDouble`, one
term-mode step away.

It is `hypercoverResolutionAbutmentIso_naturality` at the chosen descent pasted with
`Stacks.Cohomology.cohomologyPresheafIsoResolution_hom_naturality` -- [Stacks, Tag 03AY] natural
in the sheaf -- evaluated at `op X`. -/
theorem hypercoverAbutmentDescSquare (hK : IsHypercovering J K)
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{v}} (g : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap ((hypercoverResolutionTotalFunctor X J K).map
          (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F)))
          (n : ℤ) ≫
        ((hypercoverResolutionAbutmentIso X J hK (injectiveResolution G).cocomplex n).hom ≫
          (Stacks.Cohomology.cohomologyPresheafIsoResolution J.toGrothendieck G
            (injectiveResolution G) n).hom.app (op X)) =
      ((hypercoverResolutionAbutmentIso X J hK (injectiveResolution F).cocomplex n).hom ≫
          (Stacks.Cohomology.cohomologyPresheafIsoResolution J.toGrothendieck F
            (injectiveResolution F) n).hom.app (op X)) ≫
        ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).map g).app (op X) := by
  have key := NatTrans.congr_app
    (Stacks.Cohomology.cohomologyPresheafIsoResolution_hom_naturality J.toGrothendieck g
      (injectiveResolution F) (injectiveResolution G)
      ⟨InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F), by
        simpa using InjectiveResolution.desc_commutes_zero g (injectiveResolution G)
          (injectiveResolution F)⟩ n) (op X)
  simp only [NatTrans.comp_app] at key
  rw [← Category.assoc, hypercoverResolutionAbutmentIso_naturality X J hK
      (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F)) n,
    Category.assoc, key, Category.assoc]

variable {K} in
/-- **The abutment identification is natural in the coefficient sheaf.** The hypercovering
spectral sequence moves along the chosen descent of a morphism of sheaves to the chosen injective
resolutions, so this is `hypercoverResolutionAbutmentIso_naturality` at that descent pasted with
[Stacks, Tag 03AY] naturally in the sheaf
(`Stacks.Cohomology.cohomologyPresheafIsoResolution_hom_naturality`) evaluated at `op X`. -/
theorem hypercoverAbutmentIso_naturality_sheaf (hK : IsHypercovering J K)
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{v}} (g : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap
          (hypercoverFilteredMap X J.toGrothendieck
            ((𝟙 (op K), g) :
              ((op K, F) : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
                Sheaf J.toGrothendieck AddCommGrpCat.{v}) ⟶ (op K, G))).hom (n : ℤ) ≫
        (hypercoverAbutmentIso X J hK G n).hom =
      (hypercoverAbutmentIso X J hK F n).hom ≫
        ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).map g).app (op X) := by
  rw [hypercoverAbutmentIso_hom, hypercoverAbutmentIso_hom, hypercoverFilteredMap_id_fst_hom]
  exact hypercoverAbutmentDescSquare X J hK g n

/-! ### The Čech pullback along a morphism of hypercoverings -/

section Pullback

/-! #### Diagram chasing in an abstract category

Every square below is pasted at an abstract category, where each term is a variable, and applied
at the concrete spelling by a single term-mode step. This is forced rather than stylistic: the two
sides of each square are typed through different -- definitionally equal -- spellings of one
`Hom`, and a rewrite, which matches at the `instances` transparency, cannot see through them. -/

/-- **Two pasted squares.** -/
private theorem comp_square_paste {𝒜 : Type*} [Category 𝒜] {A A' B B' Z Z' : 𝒜}
    (w : A ⟶ A') (b₁ : A ⟶ B) (b₁' : A' ⟶ B') (m : B ⟶ B') (b₂ : B ⟶ Z) (b₂' : B' ⟶ Z')
    (p : Z ⟶ Z') (h₁ : w ≫ b₁' = b₁ ≫ m) (h₂ : m ≫ b₂' = b₂ ≫ p) :
    w ≫ b₁' ≫ b₂' = (b₁ ≫ b₂) ≫ p := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- **A square whose two edges are each given by a triangle.** -/
private theorem comp_eq_comp_of_square {𝒜 : Type*} [Category 𝒜] {A B B' Z : 𝒜}
    (a : A ⟶ B) (a' : A ⟶ B') (m : B ⟶ B') (b : B ⟶ Z) (b' : B' ⟶ Z)
    (h₁ : a ≫ m = a') (h₂ : m ≫ b' = b) : a ≫ b = a' ≫ b' := by
  rw [← h₂, ← h₁, Category.assoc]

/-- **A functor applied to a square of three composites.** -/
private theorem map_comp_square {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] (Φ : 𝒜 ⥤ ℬ)
    {A P Q Q' P' : 𝒜} (a : A ⟶ P) (b : P ⟶ Q) (c : Q ⟶ Q') (a' : A ⟶ P') (b' : P' ⟶ Q')
    (h : a ≫ b ≫ c = a' ≫ b') :
    (Φ.map a ≫ Φ.map b) ≫ Φ.map c = Φ.map a' ≫ Φ.map b' := by
  rw [← Φ.map_comp, ← Φ.map_comp, ← Φ.map_comp, Category.assoc, h]

/-- **Peeling a common left factor off a square whose right edge is an identity.** The composite
is split by unification rather than by a rewrite; applied repeatedly it strips the factors of
`hypercoverAbutmentUnit` that do not mention the hypercovering. -/
private theorem comp_right_of_tail {𝒜 : Type*} [Category 𝒜] {A B Z Z' : 𝒜}
    (p : A ⟶ B) (q : B ⟶ Z) (q' : B ⟶ Z') (h : Z ⟶ Z') (w : q ≫ h = q') :
    (p ≫ q) ≫ h = p ≫ q' := by
  rw [Category.assoc, w]

/-- **A naturality square factored through an intermediate object.** -/
private theorem paste_naturality {𝒜 : Type*} [Category 𝒜] {A P R S S' : 𝒜}
    (t : A ⟶ R) (m : A ⟶ P) (q : P ⟶ R) (eA : A ⟶ S) (eP : P ⟶ S) (eR : R ⟶ S') (g : S ⟶ S')
    (ht : t = m ≫ q) (h₁ : m ≫ eP = eA) (h₂ : q ≫ eR = eP ≫ g) :
    t ≫ eR = eA ≫ g := by
  rw [ht, Category.assoc, h₂, ← Category.assoc, h₁]

/-- **Rewriting the left factor of a composite.** -/
private theorem comp_congr_fst {𝒜 : Type*} [Category 𝒜] {A B Z : 𝒜} {m m' : A ⟶ B} (q : B ⟶ Z)
    (h : m = m') : m ≫ q = m' ≫ q := by
  rw [h]

variable {K}
variable {L : SimplicialObject (Limits.FormalCoproduct.{v} (Over X))}

/-! #### The pullback on the complexes of sections -/

/-- **The Čech pullback along `ρ : L ⟶ K`** on the `ℕ`-indexed complexes of sections: restriction
along the structure morphisms of `ρ` in each Čech degree. It is `cechComplexOverBifunctor` --
the two-variable Čech complex of `SpectralSequencePageTwo.lean` -- read in its simplicial
variable, which is possible because `hypercoverCochainNatFunctor J X K` *is*
`sheafToPresheaf ⋙ (cechComplexOverBifunctor X).obj (op K)` on the nose. -/
def cechPullbackNat (ρ : L ⟶ K) :
    hypercoverCochainNatFunctor J X K ⟶ hypercoverCochainNatFunctor J X L :=
  Functor.whiskerLeft (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{v})
    ((cechComplexOverBifunctor.{v} X).map ρ.op)

/-- **The Čech pullback is a Čech pullback in the sense of `sectionsComparisonInt_comp`**: its
components are restriction along the structure morphisms of `ρ`, in the vocabulary of
`SectionsOver.evalOpProductIso` and `Pi.π` that the hypothesis of that lemma is stated in.

The morphism-level identity is `Limits.Pi.lift_π`; it has to be used at the level of morphisms
and transported by `ConcreteCategory.congr_hom`, because the two spellings of the index family
give two `Limits.HasProduct` instance terms that an element-level `exact` will not identify. -/
theorem cechPullbackNat_pi (ρ : L ⟶ K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (n : ℕ)
    (z : ((hypercoverCochainNatFunctor J X K).obj F).X n) (i : (L.obj (op ⦋n⦌)).I) :
    ConcreteCategory.hom
        (Pi.π (fun i ↦ F.obj.obj (op ((L.obj (op ⦋n⦌)).obj i).left)) i)
        (ConcreteCategory.hom
          (SectionsOver.evalOpProductIso J.toGrothendieck (L.obj (op ⦋n⦌)) F).hom
          (ConcreteCategory.hom (((cechPullbackNat X J ρ).app F).f n) z)) =
      ConcreteCategory.hom
        (F.obj.map ((Over.forget X).map ((ρ.app (op ⦋n⦌)).φ i)).op)
        (ConcreteCategory.hom
          (Pi.π (fun l ↦ F.obj.obj (op ((K.obj (op ⦋n⦌)).obj l).left))
            ((ρ.app (op ⦋n⦌)).f i))
          (ConcreteCategory.hom
            (SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) F).hom z)) := by
  change ConcreteCategory.hom
      (Pi.π (fun l ↦ F.obj.obj (op ((L.obj (op ⦋n⦌)).obj l).left)) i)
      (ConcreteCategory.hom (Pi.lift (fun l ↦
        Pi.π (fun m ↦ F.obj.obj (op ((K.obj (op ⦋n⦌)).obj m).left))
            ((ρ.app (op ⦋n⦌)).f l) ≫
          F.obj.map ((Over.forget X).map ((ρ.app (op ⦋n⦌)).φ l)).op)) z) =
    ConcreteCategory.hom
      (Pi.π (fun m ↦ F.obj.obj (op ((K.obj (op ⦋n⦌)).obj m).left))
          ((ρ.app (op ⦋n⦌)).f i) ≫
        F.obj.map ((Over.forget X).map ((ρ.app (op ⦋n⦌)).φ i)).op) z
  exact ConcreteCategory.congr_hom (Pi.lift_π _ i) z

/-- The Čech pullback on the `ℤ`-indexed complexes of sections. -/
def cechPullbackInt (ρ : L ⟶ K) :
    hypercoverCochainIntFunctor J X K ⟶ hypercoverCochainIntFunctor J X L :=
  Functor.whiskerRight (cechPullbackNat X J ρ) (embeddingUpNat.extendFunctor AddCommGrpCat.{v})

/-- **[Stacks, Tag 01GX] is natural in the hypercovering, for the actual Čech pullback**:
`sectionsComparisonInt_comp` with its hypothesis discharged by `cechPullbackNat_pi`. -/
theorem sectionsComparisonInt_comp_cechPullback (ρ : L ⟶ K)
    (hK : IsHypercovering J K) (hL : IsHypercovering J L) :
    sectionsComparisonInt J X K hK ≫ cechPullbackInt X J ρ =
      sectionsComparisonInt J X L hL :=
  sectionsComparisonInt_comp J X ρ hK hL (cechPullbackNat X J ρ)
    (fun F n z i ↦ cechPullbackNat_pi X J ρ F n z i)

/-- The Čech pullback on the hypercover double complexes, i.e. degreewise in the complex of
sheaves. -/
def cechPullbackBicomplex (ρ : L ⟶ K) :
    hypercoverBicomplexFunctor J X K ⟶ hypercoverBicomplexFunctor J X L :=
  NatTrans.mapHomologicalComplex (cechPullbackInt X J ρ) (up ℤ)

/-- **The comparison of double complexes is natural in the hypercovering**:
`sectionsComparisonInt_comp_cechPullback` with `NatTrans.mapHomologicalComplex` applied to it,
read at a complex. -/
theorem hypercoverBicomplexComparison_comp_cechPullback (ρ : L ⟶ K)
    (hK : IsHypercovering J K) (hL : IsHypercovering J L)
    (E : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℤ) :
    hypercoverBicomplexComparison J X K hK E ≫ (cechPullbackBicomplex X J ρ).app E =
      hypercoverBicomplexComparison J X L hL E := by
  have h : NatTrans.mapHomologicalComplex (sectionsComparisonInt J X K hK) (up ℤ) ≫
      cechPullbackBicomplex X J ρ =
      NatTrans.mapHomologicalComplex (sectionsComparisonInt J X L hL) (up ℤ) :=
    Eq.trans (NatTrans.mapHomologicalComplex_comp (up ℤ)
        (sectionsComparisonInt J X K hK) (cechPullbackInt X J ρ)).symm
      (congrArg (fun α ↦ NatTrans.mapHomologicalComplex α (up ℤ))
        (sectionsComparisonInt_comp_cechPullback X J ρ hK hL))
  exact (NatTrans.comp_app _ _ E).symm.trans (NatTrans.congr_app h E)

/-- **The augmentation of the hypercover total complex is natural in the hypercovering.** The
prefix `totalSingleRowZeroUnit` of `hypercoverAugCochain` is common to `K` and `L`, so this is
`hypercoverBicomplexComparison_comp_cechPullback` with the total complex functor applied to it;
no component of the total complex has to be analysed. -/
theorem hypercoverAugCochain_app_comp_cechPullback (ρ : L ⟶ K)
    (hK : IsHypercovering J K) (hL : IsHypercovering J L)
    (E : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℤ) :
    (hypercoverAugCochain J X K hK).app E ≫
        (totalComplexFunctor AddCommGrpCat.{v}).map ((cechPullbackBicomplex X J ρ).app E) =
      (hypercoverAugCochain J X L hL).app E := by
  have step : (totalComplexFunctor AddCommGrpCat.{v}).map
          (hypercoverBicomplexComparison J X K hK E) ≫
        (totalComplexFunctor AddCommGrpCat.{v}).map ((cechPullbackBicomplex X J ρ).app E) =
      (totalComplexFunctor AddCommGrpCat.{v}).map
        (hypercoverBicomplexComparison J X L hL E) :=
    Eq.trans ((totalComplexFunctor AddCommGrpCat.{v}).map_comp _ _).symm
      (congrArg ((totalComplexFunctor AddCommGrpCat.{v}).map)
        (hypercoverBicomplexComparison_comp_cechPullback X J ρ hK hL E))
  exact Eq.trans (Category.assoc _ _ _)
    (congrArg (fun φ ↦ totalSingleRowZeroUnit
        (((sheafSectionsFunctor J X).mapHomologicalComplex (up ℤ)).obj E) ≫ φ) step)

/-! ### The double complex comparison is natural in the hypercovering -/

/-- **`hypercoverDoubleBridge` is natural in the hypercovering.** It is `mapExtendNatIso` twice;
the outer factor is `CategoryTheory.Functor.mapExtendNatIso_naturality_natTrans`, and the inner
one is free, being the naturality of a fixed natural transformation whiskered on the left by a
functor that varies with the hypercovering. -/
theorem hypercoverDoubleBridge_hom_naturality (ρ : L ⟶ K) :
    Functor.whiskerLeft (embeddingUpNat.extendFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{v}))
          (cechPullbackBicomplex X J ρ) ≫ (hypercoverDoubleBridge X J L).hom =
      (hypercoverDoubleBridge X J K).hom ≫
        (cechDoubleSheafBifunctor.{v} X J.toGrothendieck).map ρ.op := by
  have h1 := (hypercoverCochainIntFunctor J X K).mapExtendNatIso_naturality_natTrans
    (hypercoverCochainIntFunctor J X L) (cechPullbackInt X J ρ) embeddingUpNat
  have h2 : Functor.whiskerRight
          (NatTrans.mapHomologicalComplex (cechPullbackInt X J ρ) (up ℕ))
          (embeddingUpNat.extendFunctor (CochainComplex AddCommGrpCat.{v} ℤ)) ≫
        Functor.whiskerLeft ((hypercoverCochainNatFunctor J X L).mapHomologicalComplex (up ℕ))
          ((embeddingUpNat.extendFunctor AddCommGrpCat.{v}).mapExtendNatIso
            embeddingUpNat).symm.hom =
      Functor.whiskerLeft ((hypercoverCochainNatFunctor J X K).mapHomologicalComplex (up ℕ))
          ((embeddingUpNat.extendFunctor AddCommGrpCat.{v}).mapExtendNatIso
            embeddingUpNat).symm.hom ≫
        (cechDoubleSheafBifunctor.{v} X J.toGrothendieck).map ρ.op :=
    NatTrans.ext (funext fun Y ↦
      ((embeddingUpNat.extendFunctor AddCommGrpCat.{v}).mapExtendNatIso
          embeddingUpNat).symm.hom.naturality
        ((NatTrans.mapHomologicalComplex (cechPullbackNat X J ρ) (up ℕ)).app Y))
  exact comp_square_paste _ _ _ _ _ _ _ h1 h2

/-- **The Čech pullback on `hypercoverResolutionTotalFunctor`**: the morphism of total complexes
of Čech double complexes along `ρ : L ⟶ K`, as a natural transformation of functors of the
`ℕ`-indexed complex of sheaves, so that every total complex occurring in it is the value of one
functor. -/
def cechPullbackResolutionTotal (ρ : L ⟶ K) :
    hypercoverResolutionTotalFunctor X J K ⟶ hypercoverResolutionTotalFunctor X J L :=
  Functor.whiskerRight ((cechDoubleSheafBifunctor.{v} X J.toGrothendieck).map ρ.op)
    (totalComplexFunctor AddCommGrpCat.{v})

/-- **`hypercoverTotalBridge` is natural in the hypercovering**, at a complex of sheaves: the
total complex functor applied to `hypercoverDoubleBridge_hom_naturality`. -/
theorem hypercoverTotalBridge_hom_app_naturality (ρ : L ⟶ K)
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℕ) :
    (totalComplexFunctor AddCommGrpCat.{v}).map
          ((cechPullbackBicomplex X J ρ).app (Y.extend embeddingUpNat)) ≫
        (hypercoverTotalBridge X J L).hom.app Y =
      (hypercoverTotalBridge X J K).hom.app Y ≫ (cechPullbackResolutionTotal X J ρ).app Y :=
  Eq.trans ((totalComplexFunctor AddCommGrpCat.{v}).map_comp _ _).symm
    (Eq.trans
      (congrArg ((totalComplexFunctor AddCommGrpCat.{v}).map)
        (NatTrans.congr_app (hypercoverDoubleBridge_hom_naturality X J ρ) Y))
      ((totalComplexFunctor AddCommGrpCat.{v}).map_comp _ _))

/-! #### The abutment identification is natural in the hypercovering -/

/-- **`hypercoverAbutmentUnit` is natural in the hypercovering**: the comparison at `K` followed
by the Čech pullback along `ρ : L ⟶ K` is the comparison at `L`.

Three of the five factors of `hypercoverAbutmentUnit` do not mention the hypercovering and are
peeled off by `comp_right_of_tail`; what is left is `H^n` of
`hypercoverAugCochain_app_comp_cechPullback` pasted with `H^n` of
`hypercoverTotalBridge_hom_app_naturality`. -/
theorem hypercoverAbutmentUnit_app_comp_cechPullback (ρ : L ⟶ K)
    (hK : IsHypercovering J K) (hL : IsHypercovering J L) (n : ℕ)
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℕ) :
    (hypercoverAbutmentUnit X J hK n).app Y ≫
        HomologicalComplex.homologyMap ((cechPullbackResolutionTotal X J ρ).app Y) (n : ℤ) =
      (hypercoverAbutmentUnit X J hL n).app Y := by
  have sq := comp_eq_comp_of_square
    ((hypercoverAugCochain J X K hK).app (Y.extend embeddingUpNat))
    ((hypercoverAugCochain J X L hL).app (Y.extend embeddingUpNat))
    ((totalComplexFunctor AddCommGrpCat.{v}).map
      ((cechPullbackBicomplex X J ρ).app (Y.extend embeddingUpNat)))
    ((hypercoverTotalBridge X J K).hom.app Y ≫ (cechPullbackResolutionTotal X J ρ).app Y)
    ((hypercoverTotalBridge X J L).hom.app Y)
    (hypercoverAugCochain_app_comp_cechPullback X J ρ hK hL (Y.extend embeddingUpNat))
    (hypercoverTotalBridge_hom_app_naturality X J ρ Y)
  refine comp_right_of_tail _ _ _ _ ?_
  refine comp_right_of_tail _ _ _ _ ?_
  refine comp_right_of_tail _ _ _ _ ?_
  exact map_comp_square (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (up ℤ) (n : ℤ))
    _ _ _ _ _ sq

/-- **The abutment identification at a complex of injective abelian sheaves is natural in the
hypercovering.** This is `hypercoverAbutmentUnit_app_comp_cechPullback` read in the forward
direction; the target of the identification does not mention the hypercovering, so the right edge
of the square is an identity. -/
theorem hypercoverResolutionAbutmentIso_naturality_hypercovering (ρ : L ⟶ K)
    (hK : IsHypercovering J K) (hL : IsHypercovering J L)
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℕ)
    [∀ p, Injective (Y.X p)] (n : ℕ) :
    HomologicalComplex.homologyMap ((cechPullbackResolutionTotal X J ρ).app Y) (n : ℤ) ≫
        (hypercoverResolutionAbutmentIso X J hL Y n).hom =
      (hypercoverResolutionAbutmentIso X J hK Y n).hom :=
  (Iso.eq_comp_inv _).1 ((Iso.inv_comp_eq _).1
    (hypercoverAbutmentUnit_app_comp_cechPullback X J ρ hK hL n Y))

/-- **The abutment identification of clause (3) of [Stacks, Tag 01GY] is natural in the
hypercovering.** The second factor of `hypercoverAbutmentIso`, [Stacks, Tag 03AY], does not
mention the hypercovering, so this is
`hypercoverResolutionAbutmentIso_naturality_hypercovering` at the chosen injective
resolution. -/
theorem hypercoverAbutmentIso_naturality_hypercovering (ρ : L ⟶ K)
    (hK : IsHypercovering J K) (hL : IsHypercovering J L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (n : ℕ) :
    HomologicalComplex.homologyMap
          ((cechPullbackResolutionTotal X J ρ).app (injectiveResolution F).cocomplex) (n : ℤ) ≫
        (hypercoverAbutmentIso X J hL F n).hom =
      (hypercoverAbutmentIso X J hK F n).hom := by
  rw [hypercoverAbutmentIso_hom, hypercoverAbutmentIso_hom, ← Category.assoc,
    hypercoverResolutionAbutmentIso_naturality_hypercovering X J ρ hK hL
      (injectiveResolution F).cocomplex n]

/-- **`hypercoverFilteredMap` at a morphism whose sheaf component is the identity** induces on
cohomology the Čech pullback.

`hypercoverDoubleMap` carries `CategoryTheory.InjectiveResolution.desc (𝟙 F)` rather than the
identity, so the two morphisms of double complexes differ by `cechDoubleSheaf₂Homotopy` of
`InjectiveResolution.descIdHomotopy`; `HomologicalComplex₂.totalMapHomotopy₁` carries that
homotopy to the total complexes and cohomology is homotopy invariant. -/
theorem homologyMap_hypercoverFilteredMap_id_snd (ρ : L ⟶ K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (n : ℤ) :
    HomologicalComplex.homologyMap
        (hypercoverFilteredMap X J.toGrothendieck
          ((ρ.op, 𝟙 F) :
            ((op K, F) : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
              Sheaf J.toGrothendieck AddCommGrpCat.{v}) ⟶ (op L, F))).hom n =
      HomologicalComplex.homologyMap
        ((cechPullbackResolutionTotal X J ρ).app (injectiveResolution F).cocomplex) n := by
  have hmap : (cechDoubleSheaf₂ X J.toGrothendieck).map
        ((ρ.op, 𝟙 (injectiveResolution F).cocomplex) :
          ((op K, (injectiveResolution F).cocomplex) :
            (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
              CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℕ) ⟶
            (op L, (injectiveResolution F).cocomplex)) =
      ((cechDoubleSheafBifunctor.{v} X J.toGrothendieck).map ρ.op).app
        (injectiveResolution F).cocomplex := by
    dsimp only [cechDoubleSheaf₂, Functor.uncurry_obj_map]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hhtp := cechDoubleSheaf₂Homotopy X J.toGrothendieck
    (P := ((op K, (injectiveResolution F).cocomplex) :
      (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
        CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℕ))
    (Q := ((op L, (injectiveResolution F).cocomplex) :
      (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
        CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{v}) ℕ))
    ρ.op (InjectiveResolution.descIdHomotopy F (injectiveResolution F))
  exact Eq.trans ((HomologicalComplex₂.totalMapHomotopy₁ hhtp (up ℤ)).homologyMap_eq n)
    (congrArg (fun φ ↦ HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map φ (up ℤ)) n) hmap)

/-- **The abutment identification is natural in the hypercovering and in the coefficient sheaf
simultaneously**, which is the naturality clause (3) of [Stacks, Tag 01GY] asserts.

A morphism of pairs factors as a morphism of hypercoverings at a fixed sheaf followed by a
morphism of sheaves at a fixed hypercovering. The first square is
`hypercoverAbutmentIso_naturality_hypercovering` read through
`homologyMap_hypercoverFilteredMap_id_snd`, the second is
`hypercoverAbutmentIso_naturality_sheaf`. -/
theorem hypercoverAbutmentIso_naturality
    (hK : IsHypercovering J K) (hL : IsHypercovering J L)
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{v}}
    (fg : ((op K, F) : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J.toGrothendieck AddCommGrpCat.{v}) ⟶ (op L, G)) (n : ℕ) :
    HomologicalComplex.homologyMap
          (hypercoverFilteredMap X J.toGrothendieck fg).hom (n : ℤ) ≫
        (hypercoverAbutmentIso X J hL G n).hom =
      (hypercoverAbutmentIso X J hK F n).hom ≫
        ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).map fg.2).app (op X) := by
  have hsplit : fg =
      ((fg.1, 𝟙 F) :
          ((op K, F) : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
            Sheaf J.toGrothendieck AddCommGrpCat.{v}) ⟶ (op L, F)) ≫
        ((𝟙 (op L), fg.2) :
          ((op L, F) : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
            Sheaf J.toGrothendieck AddCommGrpCat.{v}) ⟶ (op L, G)) := by
    simp
  have ht₀ := Eq.trans
    (congrArg (fun fg' ↦ HomologicalComplex.homologyMap
        (hypercoverFilteredMap X J.toGrothendieck fg').hom (n : ℤ)) hsplit)
    (homologyMap_hypercoverFilteredMap_comp X J.toGrothendieck
      ((fg.1, 𝟙 F) :
        ((op K, F) : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
          Sheaf J.toGrothendieck AddCommGrpCat.{v}) ⟶ (op L, F))
      ((𝟙 (op L), fg.2) :
        ((op L, F) : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
          Sheaf J.toGrothendieck AddCommGrpCat.{v}) ⟶ (op L, G)) (n : ℤ))
  exact paste_naturality _ _ _ _ _ _ _
    (ht₀.trans
      (comp_congr_fst _
        (homologyMap_hypercoverFilteredMap_id_snd X J fg.1.unop F (n : ℤ))))
    (hypercoverAbutmentIso_naturality_hypercovering X J fg.1.unop hK hL F n)
    (hypercoverAbutmentIso_naturality_sheaf X J hL fg.2 n)

end Pullback

/-! ### The abutment -/

/-- **The abutment of clause (3) of [Stacks, Tag 01GY] at a hypercovering and a coefficient
sheaf**: the hypercovering spectral sequence abuts to `H^{p+q}(X, F)`.

`hypercoveringFunctorialAbutment` read at the object, with the cohomology of the total complex
replaced by sheaf cohomology through `hypercoverAbutmentIso`;
`Stacks.Cohomology.Leray.FirstQuadrantAbutsTo.ofIsoAbutment` touches no other field.

This is the abutment at each object. The *functorial* abutment that clause (3) asserts needs, in
addition, the naturality of `hypercoverAbutmentIso` in the hypercovering; see the implementation
notes of this file. -/
def hypercoveringAbutment
    (KF : (HypercoveringCat X J)ᵒᵖ × Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    _root_.Stacks.Cohomology.Leray.FirstQuadrantAbutsTo
      ((hypercoveringSpectralSequence X J).obj KF)
      (fun n => ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).obj KF.2).obj (op X)) :=
  ((hypercoveringFunctorialAbutment X J).obj KF).ofIsoAbutment
    (fun n => hypercoverAbutmentIso X J KF.1.unop.property KF.2 n)

/-- **The asserted abutment of clause (3) of [Stacks, Tag 01GY]** `H^{p+q}(X, F)`, as a functor of
the hypercovering and the coefficient sheaf: it is the second projection followed by
[Stacks, Tag 03AY]'s cohomology presheaf evaluated at the covered object, so it does not depend
on the hypercovering at all. -/
def hypercoveringCohomologyFunctor (n : ℕ) :
    (HypercoveringCat X J)ᵒᵖ × Sheaf J.toGrothendieck AddCommGrpCat.{v} ⥤
      AddCommGrpCat.{v} where
  obj KF := ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).obj KF.2).obj (op X)
  map fg := ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).map fg.2).app (op X)
  map_id KF := by
    change ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).map (𝟙 KF.2)).app (op X) = _
    rw [CategoryTheory.Functor.map_id, NatTrans.id_app]
  map_comp fg f'g' := by
    change ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).map
      (fg.2 ≫ f'g'.2)).app (op X) = _
    rw [CategoryTheory.Functor.map_comp, NatTrans.comp_app]

/-- The morphism of cohomology the functorial abutment moves along is `H^n` of
`hypercoverFilteredMap`, by definition: `CochainComplex.Filtered.inducedFilteredObjectMap_hom`
under three functor compositions. Named because the two spellings are definitionally but not
syntactically equal. -/
private theorem filtrationForget_map_eq
    {KF LG : (HypercoveringCat X J)ᵒᵖ × Sheaf J.toGrothendieck AddCommGrpCat.{v}}
    (fg : KF ⟶ LG) (n : ℕ) :
    ((ObjectProperty.ι _).op.prod (𝟭 (Sheaf J.toGrothendieck AddCommGrpCat.{v})) ⋙
          hypercoverFiltrationFunctor X J.toGrothendieck (n : ℤ) ⋙
            FilteredObject.forget).map fg =
      HomologicalComplex.homologyMap (hypercoverFilteredMap X J.toGrothendieck
        (((ObjectProperty.ι _).op.prod
          (𝟭 (Sheaf J.toGrothendieck AddCommGrpCat.{v}))).map fg)).hom (n : ℤ) :=
  rfl

/-- **The naturality square of the abutment identification, in the spelling
`CategoryTheory.NatIso.ofComponents` asks for.** This is `hypercoverAbutmentIso_naturality`
restricted to the full subcategory of hypercoverings, with the morphism of cohomology written
through the filtration functor.

It is stated separately, rather than inline in `hypercoverAbutmentNatIso`, and every implicit
argument of `hypercoverAbutmentIso_naturality` is spelled out: left to unification, the
hypercovering and the sheaf of the pair are recovered by unfolding a product-category `Hom`,
which costs more than the heartbeat budget. -/
theorem hypercoverAbutmentIso_naturality_hypercoveringCat
    {KF LG : (HypercoveringCat X J)ᵒᵖ × Sheaf J.toGrothendieck AddCommGrpCat.{v}}
    (fg : KF ⟶ LG) (n : ℕ) :
    ((ObjectProperty.ι _).op.prod (𝟭 (Sheaf J.toGrothendieck AddCommGrpCat.{v})) ⋙
          hypercoverFiltrationFunctor X J.toGrothendieck (n : ℤ) ⋙
            FilteredObject.forget).map fg ≫
        (hypercoverAbutmentIso X J LG.1.unop.property LG.2 n).hom =
      (hypercoverAbutmentIso X J KF.1.unop.property KF.2 n).hom ≫
        (hypercoveringCohomologyFunctor X J n).map fg :=
  Eq.trans (comp_congr_fst _ (filtrationForget_map_eq X J fg n))
    (hypercoverAbutmentIso_naturality X J (K := KF.1.unop.obj) (L := LG.1.unop.obj)
      KF.1.unop.property LG.1.unop.property (F := KF.2) (G := LG.2)
      (((ObjectProperty.ι _).op.prod
        (𝟭 (Sheaf J.toGrothendieck AddCommGrpCat.{v}))).map fg) n)

/-- **The abutment identification of clause (3) of [Stacks, Tag 01GY], as an isomorphism of
functors** on `(HypercoveringCat X J)ᵒᵖ × Sheaf J AddCommGrpCat`: the cohomology of the total
complex the hypercovering spectral sequence is built on is `H^n(X, F)`, naturally in the
hypercovering and in the coefficient sheaf simultaneously.

The components are `hypercoverAbutmentIso` and the naturality is
`hypercoverAbutmentIso_naturality`. -/
def hypercoverAbutmentNatIso (n : ℕ) :
    (ObjectProperty.ι _).op.prod (𝟭 (Sheaf J.toGrothendieck AddCommGrpCat.{v})) ⋙
        hypercoverFiltrationFunctor X J.toGrothendieck (n : ℤ) ⋙ FilteredObject.forget ≅
      hypercoveringCohomologyFunctor X J n :=
  NatIso.ofComponents (fun KF ↦ hypercoverAbutmentIso X J KF.1.unop.property KF.2 n)
    (fun {_ _} fg ↦ hypercoverAbutmentIso_naturality_hypercoveringCat X J fg n)

/-- **Clause (3) of [Stacks, Tag 01GY], the functorial abutment**: the hypercovering spectral
sequence abuts to `H^{p+q}(X, F)`, functorially in the hypercovering and in the coefficient
sheaf.

`hypercoveringFunctorialAbutment` with the cohomology of the total complex replaced by sheaf
cohomology through `hypercoverAbutmentNatIso`;
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofIsoAbutment` touches no other field --
the structure mentions the asserted abutment in `abutmentIso` alone. -/
@[stacks 01GY "spectral_sequence", sga "4 V 7.4.0" "(7.4.0.3) abutment"]
def hypercoveringCohomologyAbutment :
    _root_.Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo
      (hypercoveringSpectralSequence X J)
      (fun n ↦ hypercoveringCohomologyFunctor X J n) :=
  (hypercoveringFunctorialAbutment X J).ofIsoAbutment
    (fun n ↦ hypercoverAbutmentNatIso X J n)

end Stacks.CategoryTheory.Hypercovering.Functorial

end
