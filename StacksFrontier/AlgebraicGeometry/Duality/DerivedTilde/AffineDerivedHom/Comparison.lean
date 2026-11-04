module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.InternalHomTilde.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.AffineInternalHom
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.CategoryTheory.IsoNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.ModuleSpecGammaAdditive
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom.PerfectSource
import all StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom.HomComplexTilde
import all StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom.PerfectSource

/-!
# The canonical affine comparison `(R Hom_R(K, L))~ ⟶ R𝓗om_{𝒪_X}(K̃, L̃)`

Let `R` be a commutative ring and `X = Spec R`. Without the perfectness hypothesis of clause
(3)(b) of [Stacks, Tag 0A6H] the same ingredients still produce a canonical morphism

`(R Hom_R(K, L))~  ⟶  R𝓗om_{𝒪_X}(K̃, L̃)`

for arbitrary `K` and `L`, in the direction in which no hypothesis is needed: the degreewise
map of [Stacks, Tag 01I8] exists for all modules, and the map of [Stacks, Tag 08JH] to derived
internal Hom exists for all complexes of sheaves. That morphism is
`AlgebraicGeometry.affineDerivedTildeHomComparison`. For `K` perfect it is the inverse of the
isomorphism `AlgebraicGeometry.affinePerfectDerivedSheafHomIso` of clause (3)(b), proved in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom.PerfectSource`.

## Main definitions

* `AlgebraicGeometry.affineHomComplexTildeMap`: the complex-level comparison
  `(Hom^•_R(P, L))~ ⟶ SheafHom^•(P̃, L̃)` for *arbitrary* complexes `P` and `L` of
  `R`-modules, degreewise the map of [Stacks, Tag 01I8].
* `AlgebraicGeometry.affineDerivedTildeHomComparison`: the canonical morphism
  `(R Hom_R(K, L))~ ⟶ R𝓗om_{𝒪_X}(K̃, L̃)` for arbitrary objects `K` and `L` of `D(R)`, with
  no perfectness, pseudo-coherence or boundedness hypothesis.

## Main results

* `AlgebraicGeometry.affineHomComplexTildeMap_toOpen` normalizes the hypothesis-free
  complex-level comparison on canonical global sections, and
  `AlgebraicGeometry.isIso_affineHomComplexTildeMap` records that it is invertible for a
  bounded finite-projective source, where it is the inverse of `affineHomComplexTildeIso`.
* `AlgebraicGeometry.affineDerivedTildeHomComparison_model` identifies the hypothesis-free
  comparison on K-injective representatives of both arguments, and
  `AlgebraicGeometry.affineDerivedTildeHomComparison_natural_left` and `_natural_right` give
  its naturality.
* `AlgebraicGeometry.affineDerivedTildeHomComparison_perfect` and
  `AlgebraicGeometry.isIso_affineDerivedTildeHomComparison`: for `K` perfect the
  hypothesis-free comparison is the inverse of `affinePerfectDerivedSheafHomIso`, and so is
  invertible. This is what makes the comparison the morphism of the clause rather than a
  morphism between the right two objects.

## Implementation notes

**The substrate of the clause is hypothesis-free.** Finiteness and projectivity of the terms of
`P` enter the complex-level comparison only through the statement that each term of the
internal Hom complex is the sheafification of its global sections. Consequently the clause
(3)(b) substrate `affineHomComplexTildeIso` and the general comparison
`affineHomComplexTildeMap` are the *same* morphism, the former merely known to be invertible,
and the same holds one level up by `affineDerivedTildeHomComparison_perfect`.

**K-injective models in both variables.** The hypothesis-free comparison is also built on
models and extended along an essentially surjective functor, but its models are a K-injective
representative of *each* argument rather than a finite-projective representative of the source.
The extension needs every derived morphism between models to be the class of a chain map; for
the contravariant argument that would ask for a K-projective resolution of an unbounded
complex, for which there is no existence theorem available —
`CochainComplex.isKProjective_of_projective` produces K-projectives only from bounded-above
complexes of projectives — whereas a K-injective source model asks instead that the *target* of
the lifted morphism be K-injective, which is what `CochainComplex.exists_quasiIso_isKInjective`
supplies.
The module side of the comparison is correspondingly the K-injective comparison of
[Stacks, Tag 0A63] rather than the bounded-above projective one of [Stacks, Tag 0A66].

The derived rewrites here are written `rw (transparency := .default) [...]` for the reason
explained in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom.PerfectSource`.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.RingedSite Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.tilde.preservesFiniteLimits
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

attribute [local instance] PerfectModel.upper PerfectModel.projective PerfectModel.finite

/-! ### The canonical comparison, with no hypothesis on either argument -/

/-- **The complex-level comparison `(Hom^•_R(P, L))~ ⟶ SheafHom^•(P̃, L̃)`** for arbitrary
complexes of `R`-modules. In each degree it is the transpose, under the sheafification
adjunction, of the degreewise map of [Stacks, Tag 01I8] carrying a module Hom cochain to the
sheaf Hom cochain of the sheafifications of its components. -/
@[no_expose]
public def affineHomComplexTildeMap (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tildeCx R).obj (CochainComplex.HomComplexR R P L) ⟶
      (sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj :=
  (tildeCx R).map (affineHomSectionsComplexIso R P L).inv ≫
    fromTildeΓComplex R
      (sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj

private theorem affineHomComplexTildeMap_eq_inv (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite) :
    affineHomComplexTildeMap R P L = (affineHomComplexTildeIso R P L hP).inv :=
  rfl

/-- For `P` a bounded complex of finite projective modules the complex-level comparison is
invertible: it is the inverse of `affineHomComplexTildeIso`. -/
public lemma isIso_affineHomComplexTildeMap (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite) :
    IsIso (affineHomComplexTildeMap R P L) := by
  rw [affineHomComplexTildeMap_eq_inv R P L hP]
  exact (affineHomComplexTildeIso R P L hP).isIso_inv

/-- **The normalization of `affineHomComplexTildeMap`.** It takes the canonical global section
attached to a module Hom cochain `α` to the sheaf Hom cochain whose components are the sheaf
maps induced by the components of `α`; this is the degreewise map of [Stacks, Tag 01I8], and in
particular it excludes a global sign. -/
public theorem affineHomComplexTildeMap_toOpen (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    (n p q : ℤ) (hpq : p + n = q) (α : CochainComplex.HomComplex.Cochain P L n) :
    (((sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).sectionsEquiv ⊤ n
        (((affineHomComplexTildeMap R P L).f n).val.app (op ⊤)
          (tilde.toOpen ((CochainComplex.HomComplexR R P L).X n) ⊤ α))).v p q hpq) =
      (tilde.map (α.v p q hpq)).over ⊤ := by
  let H := sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)
  let e := affineHomSectionsLinearEquiv R P L n
  have hc := congrArg (fun k : (CochainComplex.HomComplexR R P L).X n ⟶
      (moduleSpecΓFunctor (R := R)).obj (H.obj.X n) => k α)
    (tilde_adjunction_unit_map_counit (R := R) (H.obj.X n) e.toModuleIso.inv)
  have he : affineHomSectionsLinearMap R P L n
      (((affineHomComplexTildeMap R P L).f n).val.app (op ⊤)
        (tilde.toOpen ((CochainComplex.HomComplexR R P L).X n) ⊤ α)) = α := by
    show e _ = α
    convert e.apply_symm_apply α using 1
    exact congrArg e hc
  have hv : (fullyFaithfulTildeOverTop R).preimage
      ((H.sectionsEquiv ⊤ n
        (((affineHomComplexTildeMap R P L).f n).val.app (op ⊤)
          (tilde.toOpen ((CochainComplex.HomComplexR R P L).X n) ⊤ α))).v p q hpq) =
      α.v p q hpq :=
    (affineHomSectionsLinearMap_v R P L n p q hpq _).symm.trans
      (congrArg (fun z : CochainComplex.HomComplex.Cochain P L n => z.v p q hpq) he)
  exact ((fullyFaithfulTildeOverTop R).map_preimage _).symm.trans (congrArg (tildeTop R).map hv)

/-- The components of the functorial map of Hom complexes: precomposition by `f` and
postcomposition by `g` act on a Hom cochain by composing its components with those of `f` and
`g`. -/
private lemma affineTildePrecompPostcompApply (R : CommRingCat.{u})
    (P P' L L' : CochainComplex (ModuleCat.{u} R) ℤ) (f : P' ⟶ P) (g : L ⟶ L')
    (n : ℤ) (α : CochainComplex.HomComplex.Cochain P L n) :
    ((Stacks.HomComplex.TensorHomMap.precomp R P' P L f ≫
        Stacks.HomComplex.TensorHomMap.postcomp R P' L L' g).f n).hom α =
      ((CochainComplex.HomComplex.Cochain.ofHom f).comp α (zero_add n)).comp
        (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero n) :=
  rfl

private lemma precomp_postcomp_v (R : CommRingCat.{u})
    (P P' L L' : CochainComplex (ModuleCat.{u} R) ℤ) (f : P' ⟶ P) (g : L ⟶ L')
    (n : ℤ) (α : CochainComplex.HomComplex.Cochain P L n) (p q : ℤ) (hpq : p + n = q) :
    (((Stacks.HomComplex.TensorHomMap.precomp R P' P L f ≫
          Stacks.HomComplex.TensorHomMap.postcomp R P' L L' g).f n).hom α).v p q hpq =
      f.f p ≫ α.v p q hpq ≫ g.f q := by
  rw [affineTildePrecompPostcompApply R P P' L L' f g n α,
    CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, Category.assoc]

/-- **The complex-level comparison is natural**, contravariantly in the source and covariantly
in the target, for the functorial maps of Hom complexes and of internal Hom complexes.

Both sides are pinned down by their action on canonical global sections, where
`affineHomComplexTildeMap_toOpen` and `AlgebraicGeometry.RingedSite.sectionsIso_homMap_v` turn
each into the same pre- and postcomposition of sheafified components. -/
private lemma affineHomComplexTildeMap_naturality (R : CommRingCat.{u})
    (P P' L L' : CochainComplex (ModuleCat.{u} R) ℤ) (f : P' ⟶ P) (g : L ⟶ L') :
    (tildeCx R).map (Stacks.HomComplex.TensorHomMap.precomp R P' P L f ≫
          Stacks.HomComplex.TensorHomMap.postcomp R P' L L' g) ≫
        affineHomComplexTildeMap R P' L' =
      affineHomComplexTildeMap R P L ≫
        homMap (specSite R) ((tildeCx R).map f) ((tildeCx R).map g) := by
  ext n : 1
  apply tildeHom_ext_globalSections R
  intro α
  apply ((sheafHomComplex (specSite R) ((tildeCx R).obj P')
    ((tildeCx R).obj L')).sectionsEquiv ⊤ n).injective
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  refine Eq.trans (congrArg (fun z =>
      (((sheafHomComplex (specSite R) ((tildeCx R).obj P')
          ((tildeCx R).obj L')).sectionsEquiv ⊤ n)
        (((affineHomComplexTildeMap R P' L').f n).val.app (op ⊤) z)).v p q hpq)
    (tilde_toOpen_map_app_apply
      ((Stacks.HomComplex.TensorHomMap.precomp R P' P L f ≫
        Stacks.HomComplex.TensorHomMap.postcomp R P' L L' g).f n) α)) ?_
  trans (tildeTop R).map (f.f p) ≫ (tildeTop R).map (α.v p q hpq) ≫ (tildeTop R).map (g.f q)
  · refine (affineHomComplexTildeMap_toOpen R P' L' n p q hpq _).trans ?_
    refine (congrArg (fun h => (tildeTop R).map h)
      (precomp_postcomp_v R P P' L L' f g n α p q hpq)).trans ?_
    exact ((tildeTop R).map_comp _ _).trans
      (congrArg (fun v => (tildeTop R).map (f.f p) ≫ v) ((tildeTop R).map_comp _ _))
  · refine Eq.trans (congrArg (fun v => (tildeTop R).map (f.f p) ≫ v ≫
      (tildeTop R).map (g.f q))
        (affineHomComplexTildeMap_toOpen R P L n p q hpq α).symm) ?_
    exact (sectionsIso_homMap_v (specSite R) ((tildeCx R).map f) ((tildeCx R).map g) ⊤ n p q hpq
      _).symm

/-! ### Extension from K-injective models -/

/-- A natural transformation given on the image of an essentially surjective functor extends. -/
private def extendNatTrans {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : C ⥤ D) [J.EssSurj] (F G : D ⥤ E)
    (e : ∀ Y, F.obj (J.obj Y) ⟶ G.obj (J.obj Y))
    (he : ∀ {Y Z} (f : J.obj Y ⟶ J.obj Z), F.map f ≫ e Z = e Y ≫ G.map f) :
    F ⟶ G where
  app Y := F.map (J.objObjPreimageIso Y).inv ≫ e (J.objPreimage Y) ≫
    G.map (J.objObjPreimageIso Y).hom
  naturality Y Z f := by
    have h := he ((J.objObjPreimageIso Y).hom ≫ f ≫ (J.objObjPreimageIso Z).inv)
    apply (cancel_epi (F.map (J.objObjPreimageIso Y).hom)).mp
    simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [reassoc_of% h]
    simp only [← G.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem extendNatTrans_app {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : C ⥤ D) [J.EssSurj] (F G : D ⥤ E)
    (e : ∀ Y, F.obj (J.obj Y) ⟶ G.obj (J.obj Y))
    (he : ∀ {Y Z} (f : J.obj Y ⟶ J.obj Z), F.map f ≫ e Z = e Y ≫ G.map f)
    (Y : C) : (extendNatTrans J F G e he).app (J.obj Y) = e Y := by
  dsimp [extendNatTrans]
  rw [reassoc_of% he (J.objObjPreimageIso (J.obj Y)).inv]
  simp only [← G.map_comp, Iso.inv_hom_id, Category.comp_id, CategoryTheory.Functor.map_id]

/-- The models for the comparison: a K-injective representative of each of the two arguments.
Both are K-injective so that every derived morphism between models is the class of a chain
map, the source being contravariant. -/
private abbrev affineKInjectiveModels (R : CommRingCat.{u}) :=
  {I : CochainComplex (ModuleCat.{u} R) ℤ // I.IsKInjective} ×
    {I : CochainComplex (ModuleCat.{u} R) ℤ // I.IsKInjective}

private abbrev affineKInjectiveModelObject (R : CommRingCat.{u})
    (A : affineKInjectiveModels R) :
    (DerivedCategory (ModuleCat.{u} R))ᵒᵖ × DerivedCategory (ModuleCat.{u} R) :=
  (op (DerivedCategory.Q.obj A.1.val), DerivedCategory.Q.obj A.2.val)

private abbrev affineKInjectiveModelsFunctor (R : CommRingCat.{u}) :=
  inducedFunctor (affineKInjectiveModelObject R)

private lemma affineKInjectiveModelsFunctor_essSurj (R : CommRingCat.{u}) :
    (affineKInjectiveModelsFunctor R).EssSurj := by
  constructor
  rintro ⟨K, L⟩
  obtain ⟨I, i, hi, hI⟩ := CochainComplex.exists_quasiIso_isKInjective
    (DerivedCategory.Q.objPreimage K.unop)
  obtain ⟨J, j, hj, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective
    (DerivedCategory.Q.objPreimage L)
  let eI : DerivedCategory.Q.obj I ≅ K.unop :=
    (asIso (DerivedCategory.Q.map i)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K.unop
  let eJ : DerivedCategory.Q.obj J ≅ L :=
    (asIso (DerivedCategory.Q.map j)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso L
  exact ⟨(⟨I, hI⟩, ⟨J, hJ⟩), ⟨Iso.prod eI.symm.op eJ⟩⟩

/-- **The comparison on K-injective models.** On a pair of complexes with the target
K-injective both sides are computed by ordinary Hom complexes — the module side by the
K-injective comparison of [Stacks, Tag 0A63], the sheaf side by the canonical map of
[Stacks, Tag 08JH] — and the comparison is the complex-level `affineHomComplexTildeMap`
between them. -/
private def affineKInjectiveModelMap (R : CommRingCat.{u})
    (I J : CochainComplex (ModuleCat.{u} R) ℤ) (hJ : J.IsKInjective) :
    (affineModuleDerivedHom R).obj (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J) ⟶
      (affineSheafDerivedHom R).obj (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J) :=
  haveI := hJ
  (tildeDer R).map ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso I J).hom ≫
    ((tilde.functor R).mapDerivedCategoryFactors.app
      (CochainComplex.HomComplexR R I J)).hom ≫
    DerivedCategory.Q.map (affineHomComplexTildeMap R I J) ≫
    strictlyPerfectHomComparison (specSite R) (specRHom R)
      ((tildeCx R).obj I) ((tildeCx R).obj J) ≫
    ((sheafDerivedHom R).mapIso
      (Iso.prod ((tilde.functor R).mapDerivedCategoryFactors.app I).symm.op
        ((tilde.functor R).mapDerivedCategoryFactors.app J))).inv

/-- The comparison on models is natural for actual chain maps in both variables. -/
private lemma affineKInjectiveModelMap_naturality (R : CommRingCat.{u})
    (I I' J J' : CochainComplex (ModuleCat.{u} R) ℤ)
    (hJ : J.IsKInjective) (hJ' : J'.IsKInjective) (f : I' ⟶ I) (g : J ⟶ J') :
    (affineModuleDerivedHom R).map ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
        affineKInjectiveModelMap R I' J' hJ' =
      affineKInjectiveModelMap R I J hJ ≫
        (affineSheafDerivedHom R).map
          ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) := by
  let c := (tilde.functor R).mapDerivedCategoryFactors
  let S := sheafDerivedHom R
  let E := CategoryTheory.Functor.isoWhiskerRight
    (NatIso.prod (NatIso.op c.symm) c) S
  have h₁ := map_comp_naturality (tildeDer R)
    ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso_naturality f g)
  have h₂ := c.hom.naturality (Stacks.HomComplex.TensorHomMap.precomp R I' I J f ≫
    Stacks.HomComplex.TensorHomMap.postcomp R I' J J' g)
  have h₃ := map_comp_naturality DerivedCategory.Q
    (affineHomComplexTildeMap_naturality R I I' J J' f g)
  have h₄ := RingedSite.strictlyPerfectHomComparison_naturality (specSite R) (specRHom R)
    ((tildeCx R).obj I) ((tildeCx R).obj I') ((tildeCx R).obj J) ((tildeCx R).obj J')
    ((tildeCx R).map f) ((tildeCx R).map g)
  have h₅ := iso_inv_naturality (E.app (op I, J)) (E.app (op I', J')) _ _
    (E.hom.naturality (show (op I, J) ⟶ (op I', J') from (f.op, g)))
  exact paste_five_squares h₁ h₂ h₃ h₄ h₅

/-- The comparison on models is natural for every morphism between the chosen models, by
lifting the derived morphisms to actual chain maps. -/
private lemma affineKInjectiveModelMap_naturality_models (R : CommRingCat.{u})
    {A B : affineKInjectiveModels R}
    (m : (affineKInjectiveModelsFunctor R).obj A ⟶ (affineKInjectiveModelsFunctor R).obj B) :
    (affineModuleDerivedHom R).map m ≫
        affineKInjectiveModelMap R B.1.val B.2.val B.2.property =
      affineKInjectiveModelMap R A.1.val A.2.val A.2.property ≫
        (affineSheafDerivedHom R).map m := by
  have := A.1.property
  have := A.2.property
  have := B.2.property
  obtain ⟨f, hf⟩ := Q_map_surjective_of_isKInjective B.1.val A.1.val m.1.unop
  obtain ⟨g, hg⟩ := Q_map_surjective_of_isKInjective A.2.val B.2.val m.2
  have h := affineKInjectiveModelMap_naturality R A.1.val B.1.val A.2.val B.2.val
    A.2.property B.2.property f g
  have hm : (((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) :
        (affineKInjectiveModelsFunctor R).obj A ⟶
          (affineKInjectiveModelsFunctor R).obj B) = m :=
    Prod.ext (congrArg Quiver.Hom.op hf) hg
  exact naturality_of_hom_eq (affineModuleDerivedHom R) (affineSheafDerivedHom R) hm _ _ h

/-- The comparison of the two bifunctors, on all pairs of objects of `D(R)`. -/
private def affineGeneralComparison (R : CommRingCat.{u}) :
    affineModuleDerivedHom R ⟶ affineSheafDerivedHom R :=
  have := affineKInjectiveModelsFunctor_essSurj R
  extendNatTrans (affineKInjectiveModelsFunctor R) _ _
    (fun A => affineKInjectiveModelMap R A.1.val A.2.val A.2.property)
    (fun {_ _} m => affineKInjectiveModelMap_naturality_models R m)

/-! ### The canonical comparison -/

/-- **The canonical comparison of [Stacks, Tag 0A6H].** Let `R` be a commutative ring,
`X = Spec R`, and let `K`, `L` be objects of `D(R)`. The derived sheafification of the derived
Hom over `R` maps canonically to the derived internal Hom of the derived sheafifications:

`(R Hom_R(K, L))~  ⟶  R𝓗om_{𝒪_X}(K̃, L̃)`.

There is no hypothesis on either argument. On a K-injective representative of the target it is
the composite of the K-injective comparison of [Stacks, Tag 0A63], the complex-level
`affineHomComplexTildeMap`, and the canonical map of [Stacks, Tag 08JH], by
`affineDerivedTildeHomComparison_model`; it is natural in both arguments by
`affineDerivedTildeHomComparison_natural_left` and `_natural_right`. -/
@[no_expose]
public def affineDerivedTildeHomComparison (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R)) :
    (tildeDer R).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj (op K, L)) ⟶
      ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
        (op ((tildeDer R).obj K))).obj ((tildeDer R).obj L) :=
  (affineGeneralComparison R).app (op K, L)

/-- The general comparison at a pair of K-injective complexes is the model comparison. -/
private lemma affineGeneralComparison_app_models (R : CommRingCat.{u})
    (I J : CochainComplex (ModuleCat.{u} R) ℤ) [hI : I.IsKInjective] [hJ : J.IsKInjective] :
    (affineGeneralComparison R).app
        (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J) =
      affineKInjectiveModelMap R I J hJ := by
  have := affineKInjectiveModelsFunctor_essSurj R
  exact extendNatTrans_app (affineKInjectiveModelsFunctor R)
    (affineModuleDerivedHom R) (affineSheafDerivedHom R)
    (fun A => affineKInjectiveModelMap R A.1.val A.2.val A.2.property)
    (fun {_ _} m => affineKInjectiveModelMap_naturality_models R m) (⟨I, hI⟩, ⟨J, hJ⟩)

/-- The model comparison, with the last factor rewritten in terms of `specRHom`. -/
private lemma affineKInjectiveModelMap_eq_expanded (R : CommRingCat.{u})
    (I J : CochainComplex (ModuleCat.{u} R) ℤ) [hJ : J.IsKInjective] :
    affineKInjectiveModelMap R I J hJ =
      (tildeDer R).map
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso I J).hom ≫
        ((tilde.functor R).mapDerivedCategoryFactors.app
          (CochainComplex.HomComplexR R I J)).hom ≫
        DerivedCategory.Q.map (affineHomComplexTildeMap R I J) ≫
        strictlyPerfectHomComparison (specSite R) (specRHom R)
          ((tildeCx R).obj I) ((tildeCx R).obj J) ≫
        ((specRHom R).hom.map
            ((tilde.functor R).mapDerivedCategoryFactors.hom.app I).op).app
          (DerivedCategory.Q.obj ((tildeCx R).obj J)) ≫
        ((specRHom R).hom.obj
            (op ((tildeDer R).obj (DerivedCategory.Q.obj I)))).map
          ((tilde.functor R).mapDerivedCategoryFactors.inv.app J) :=
  congrArg (fun z =>
    (tildeDer R).map ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso I J).hom ≫
      ((tilde.functor R).mapDerivedCategoryFactors.app
        (CochainComplex.HomComplexR R I J)).hom ≫
      DerivedCategory.Q.map (affineHomComplexTildeMap R I J) ≫
      strictlyPerfectHomComparison (specSite R) (specRHom R)
        ((tildeCx R).obj I) ((tildeCx R).obj J) ≫ z) (affineModelProdIso_inv R I J)

/-- **The normalization of the canonical comparison.** On K-injective representatives of both
arguments it is the K-injective comparison of [Stacks, Tag 0A63], followed by the sheafified
complex-level comparison `affineHomComplexTildeMap`, followed by the canonical map to derived
internal Hom of [Stacks, Tag 08JH]. This identifies the morphism, not just its source and
target. -/
public theorem affineDerivedTildeHomComparison_model (R : CommRingCat.{u})
    (I J : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] [J.IsKInjective] :
    affineDerivedTildeHomComparison R (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj J) =
      (tildeDer R).map
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso I J).hom ≫
        ((tilde.functor R).mapDerivedCategoryFactors.app
          (CochainComplex.HomComplexR R I J)).hom ≫
        DerivedCategory.Q.map (affineHomComplexTildeMap R I J) ≫
        strictlyPerfectHomComparison (specSite R) (specRHom R)
          ((tildeCx R).obj I) ((tildeCx R).obj J) ≫
        ((specRHom R).hom.map
            ((tilde.functor R).mapDerivedCategoryFactors.hom.app I).op).app
          (DerivedCategory.Q.obj ((tildeCx R).obj J)) ≫
        ((specRHom R).hom.obj
            (op ((tildeDer R).obj (DerivedCategory.Q.obj I)))).map
          ((tilde.functor R).mapDerivedCategoryFactors.inv.app J) := by
  exact (affineGeneralComparison_app_models R I J).trans
    (affineKInjectiveModelMap_eq_expanded R I J)

/-- Dropping an identity first factor from a composite on the right of a hypothesis. -/
private lemma eq_comp_of_fst_eq_id {C : Type*} [Category* C] {W Y Z : C}
    {d : W ⟶ Y} {a : Y ⟶ Y} (ha : a = 𝟙 Y) {b : Y ⟶ Z} {e : W ⟶ Z}
    (h : e = d ≫ a ≫ b) : e = d ≫ b := by
  simpa only [ha, Category.id_comp] using h

/-- Dropping an identity second factor from a composite on the right of a hypothesis. -/
private lemma eq_comp_of_snd_eq_id {C : Type*} [Category* C] {W Y Z : C}
    {d : W ⟶ Y} {a : Y ⟶ Z} {b : Z ⟶ Z} (hb : b = 𝟙 Z) {e : W ⟶ Z}
    (h : e = d ≫ a ≫ b) : e = d ≫ a := by
  simpa only [hb, Category.comp_id] using h

/-- **The canonical comparison is natural in the target.** -/
public theorem affineDerivedTildeHomComparison_natural_right (R : CommRingCat.{u})
    (K : DerivedCategory (ModuleCat.{u} R))
    {L L' : DerivedCategory (ModuleCat.{u} R)} (g : L ⟶ L') :
    (tildeDer R).map ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
          (𝟙 (op K), g)) ≫ affineDerivedTildeHomComparison R K L' =
      affineDerivedTildeHomComparison R K L ≫
        ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tildeDer R).obj K))).map ((tildeDer R).map g) := by
  have h := (affineGeneralComparison R).naturality
    (show ((op K, L) : (DerivedCategory (ModuleCat.{u} R))ᵒᵖ ×
      DerivedCategory (ModuleCat.{u} R)) ⟶ (op K, L') from (𝟙 _, g))
  change _ = affineDerivedTildeHomComparison R K L ≫
    ((specRHom R).hom.map ((tildeDer R).map (𝟙 K)).op).app ((tildeDer R).obj L) ≫
      ((specRHom R).hom.obj (op ((tildeDer R).obj K))).map ((tildeDer R).map g) at h
  have hid : ((specRHom R).hom.map ((tildeDer R).map (𝟙 K)).op).app ((tildeDer R).obj L) =
      𝟙 _ :=
    (congrArg (fun u => NatTrans.app ((specRHom R).hom.map u) ((tildeDer R).obj L))
      (congrArg Quiver.Hom.op (CategoryTheory.Functor.map_id (tildeDer R) K))).trans
      (congrArg (fun u => NatTrans.app u ((tildeDer R).obj L))
        (CategoryTheory.Functor.map_id (specRHom R).hom (op ((tildeDer R).obj K))))
  exact eq_comp_of_fst_eq_id hid h

/-- **The canonical comparison is contravariantly natural in the source.** -/
public theorem affineDerivedTildeHomComparison_natural_left (R : CommRingCat.{u})
    {K K' : DerivedCategory (ModuleCat.{u} R)} (f : K' ⟶ K)
    (L : DerivedCategory (ModuleCat.{u} R)) :
    (tildeDer R).map ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
          (f.op, 𝟙 L)) ≫ affineDerivedTildeHomComparison R K' L =
      affineDerivedTildeHomComparison R K L ≫
        ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).map
          ((tildeDer R).map f).op).app ((tildeDer R).obj L) := by
  have h := (affineGeneralComparison R).naturality
    (show ((op K, L) : (DerivedCategory (ModuleCat.{u} R))ᵒᵖ ×
      DerivedCategory (ModuleCat.{u} R)) ⟶ (op K', L) from (f.op, 𝟙 L))
  change _ = affineDerivedTildeHomComparison R K L ≫
    ((specRHom R).hom.map ((tildeDer R).map f).op).app ((tildeDer R).obj L) ≫
      ((specRHom R).hom.obj (op ((tildeDer R).obj K'))).map ((tildeDer R).map (𝟙 L)) at h
  have hid : ((specRHom R).hom.obj (op ((tildeDer R).obj K'))).map
      ((tildeDer R).map (𝟙 L)) = 𝟙 _ :=
    (congrArg (fun u => ((specRHom R).hom.obj (op ((tildeDer R).obj K'))).map u)
      (CategoryTheory.Functor.map_id (tildeDer R) L)).trans
      (CategoryTheory.Functor.map_id ((specRHom R).hom.obj (op ((tildeDer R).obj K')))
        ((tildeDer R).obj L))
  exact eq_comp_of_snd_eq_id hid h

/-! ### Agreement with clause (3)(b) -/

private lemma affineKInjectiveModelMap_eq (R : CommRingCat.{u})
    (I J : CochainComplex (ModuleCat.{u} R) ℤ) [hJ : J.IsKInjective] :
    affineKInjectiveModelMap R I J hJ =
      (tildeDer R).map ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso I J).hom ≫
        ((tilde.functor R).mapDerivedCategoryFactors.app
          (CochainComplex.HomComplexR R I J)).hom ≫
        DerivedCategory.Q.map (affineHomComplexTildeMap R I J) ≫
        strictlyPerfectHomComparison (specSite R) (specRHom R)
          ((tildeCx R).obj I) ((tildeCx R).obj J) ≫
        ((sheafDerivedHom R).mapIso
          (Iso.prod ((tilde.functor R).mapDerivedCategoryFactors.app I).symm.op
            ((tilde.functor R).mapDerivedCategoryFactors.app J))).inv :=
  rfl

/-- Cancelling four isomorphism factors surrounding a composite, in the direction opposite to
`cancel_iso_factors`. -/
private lemma cancel_four_iso_factors {C : Type*} [Category* C]
    {M H₁ H₂ G T Y S : C} (p : G ≅ T) (q : G ≅ H₂) (r : H₁ ≅ H₂) (s : M ≅ H₁)
    (A : T ⟶ Y) (B : Y ⟶ S) (m : S ⟶ M)
    (h : A ≫ B ≫ m = p.inv ≫ q.hom ≫ r.inv ≫ s.inv) :
    (s.hom ≫ r.hom ≫ q.inv ≫ p.hom ≫ A ≫ B) ≫ m = 𝟙 M := by
  simp [h]

/-- On a bounded finite-projective source with K-injective target the comparison on models is
the inverse of the model isomorphism of clause (3)(b): the two are composites of the same five
factors, in opposite directions. -/
private lemma affineKInjectiveModelMap_eq_affineModelIso_inv (R : CommRingCat.{u})
    (P I : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    [hI : I.IsKInjective] (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite) :
    affineKInjectiveModelMap R P I hI = (affineModelIso R P I b hP).inv := by
  have hiso : IsIso (strictlyPerfectHomComparison (specSite R) (specRHom R)
      ((tildeCx R).obj P) ((tildeCx R).obj I)) :=
    strictlyPerfectHomComparison_isIso (specSite R) (specRHom R) _ _
      (tildeComplex_bounded_isFiniteFreeSummand R P hP).1
      (tildeComplex_bounded_isFiniteFreeSummand R P hP).2
  refine (Iso.comp_hom_eq_id (affineModelIso R P I b hP)).mp ?_
  rw (transparency := .default) [affineKInjectiveModelMap_eq R P I,
    affineModelProdIso_inv R P I,
    ← StacksDraft.DerivedHom.projectiveHomComparison.iso_eq_homIso P I b,
    affineHomComplexTildeMap_eq_inv R P I hP]
  exact cancel_four_iso_factors
    (asIso (strictlyPerfectHomComparison (specSite R) (specRHom R)
      ((tildeCx R).obj P) ((tildeCx R).obj I)))
    (DerivedCategory.Q.mapIso (affineHomComplexTildeIso R P I hP))
    ((tilde.functor R).mapDerivedCategoryFactors.app (CochainComplex.HomComplexR R P I))
    ((tildeDer R).mapIso (StacksDraft.DerivedHom.projectiveHomComparison.iso P I b))
    _ _ _ (affineModelIso_comp_hom R P I b hP hiso)

/-- **The comparison is computed by a K-injective representative of the target alone.** For
every complex `F` and every K-injective `J`, the component at `(QF, QJ)` is the model
comparison, with no hypothesis on `F`: both it and the model comparison satisfy the same
naturality square for a K-injective resolution of `F`, whose leading factor is invertible. -/
private lemma affineGeneralComparison_app_model (R : CommRingCat.{u})
    (F J : CochainComplex (ModuleCat.{u} R) ℤ) [hJ : J.IsKInjective] :
    (affineGeneralComparison R).app
        (op (DerivedCategory.Q.obj F), DerivedCategory.Q.obj J) =
      affineKInjectiveModelMap R F J hJ := by
  obtain ⟨I, i, hi, hI⟩ := CochainComplex.exists_quasiIso_isKInjective F
  have hQ : IsIso (DerivedCategory.Q.map i) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let m : ((op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J) :
      (DerivedCategory (ModuleCat.{u} R))ᵒᵖ × DerivedCategory (ModuleCat.{u} R)) ⟶
      (op (DerivedCategory.Q.obj F), DerivedCategory.Q.obj J) :=
    ((DerivedCategory.Q.map i).op, DerivedCategory.Q.map (𝟙 J))
  have : IsIso m := (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have h1 := (affineGeneralComparison R).naturality m
  have h2 := affineKInjectiveModelMap_naturality R I F J J hJ hJ i (𝟙 J)
  have h3 := affineGeneralComparison_app_models R I J
  rw [h3] at h1
  exact (cancel_epi ((affineModuleDerivedHom R).map m)).mp (h1.trans h2.symm)

/-- **The canonical comparison on a K-injective target.** For an arbitrary complex `F` and a
K-injective complex `J`, the component at `(QF, QJ)` is the K-injective comparison of
[Stacks, Tag 0A63], followed by the sheafified complex-level comparison
`affineHomComplexTildeMap`, followed by the canonical map to derived internal Hom of
[Stacks, Tag 08JH]. -/
public theorem affineDerivedTildeHomComparison_app_of_isKInjective (R : CommRingCat.{u})
    (F J : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] :
    affineDerivedTildeHomComparison R (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj J) =
      (tildeDer R).map
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso F J).hom ≫
        ((tilde.functor R).mapDerivedCategoryFactors.app
          (CochainComplex.HomComplexR R F J)).hom ≫
        DerivedCategory.Q.map (affineHomComplexTildeMap R F J) ≫
        strictlyPerfectHomComparison (specSite R) (specRHom R)
          ((tildeCx R).obj F) ((tildeCx R).obj J) ≫
        ((specRHom R).hom.map
            ((tilde.functor R).mapDerivedCategoryFactors.hom.app F).op).app
          (DerivedCategory.Q.obj ((tildeCx R).obj J)) ≫
        ((specRHom R).hom.obj
            (op ((tildeDer R).obj (DerivedCategory.Q.obj F)))).map
          ((tilde.functor R).mapDerivedCategoryFactors.inv.app J) :=
  (affineGeneralComparison_app_model R F J).trans (affineKInjectiveModelMap_eq_expanded R F J)

/-- Two natural transformations that agree on the image of an essentially surjective functor
are equal. -/
private lemma natTrans_ext_of_essSurj {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : C ⥤ D) [J.EssSurj] {F G : D ⥤ E} (τ σ : F ⟶ G)
    (h : ∀ Y, τ.app (J.obj Y) = σ.app (J.obj Y)) : τ = σ := by
  ext X
  apply (cancel_epi (F.map (J.objObjPreimageIso X).hom)).mp
  rw [τ.naturality, σ.naturality, h (J.objPreimage X)]

/-- **The canonical comparison agrees with clause (3)(b).** For `K` perfect it is the inverse
of the isomorphism `affinePerfectDerivedSheafHomIso`, hence invertible. This is what identifies
the comparison as the morphism whose invertibility clause (3)(b) asserts, rather than as some
morphism between the right two objects: the two are equal because they agree on bounded
finite-projective sources with K-injective targets, where both are the five-fold model
composite, and because both are natural. -/
@[stacks 0A6H "(3)(b) K perfect and L arbitrary: the canonical comparison is the inverse of \
the isomorphism"]
public theorem affineDerivedTildeHomComparison_perfect (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.Perfect.IsPerfect K) :
    affineDerivedTildeHomComparison R K L =
      (affinePerfectDerivedSheafHomIso R K L hK).inv := by
  have hess := affineModelsFunctor_essSurj R
  have key : CategoryTheory.Functor.whiskerLeft (perfectPairInclusion R)
      (affineGeneralComparison R) = (affinePerfectComparison R).inv := by
    refine natTrans_ext_of_essSurj (affineModelsFunctor R) _ _ (fun A => ?_)
    have hJ := A.2.property
    have h1 : (affineGeneralComparison R).app
        (op (DerivedCategory.Q.obj A.1.complex), DerivedCategory.Q.obj A.2.val) =
        (affineModelIso R A.1.complex A.2.val A.1.bound A.1.bdd).inv :=
      (affineGeneralComparison_app_model R A.1.complex A.2.val).trans
        (affineKInjectiveModelMap_eq_affineModelIso_inv R A.1.complex A.2.val A.1.bound A.1.bdd)
    have h2 : ((affinePerfectComparison R).app
        (op (⟨DerivedCategory.Q.obj A.1.complex, A.1.perfect⟩ : PerfectObjects R),
          DerivedCategory.Q.obj A.2.val)).inv =
        (affineModelIso R A.1.complex A.2.val A.1.bound A.1.bdd).inv :=
      (Iso.inv_eq_inv _ _).mpr
        (affinePerfectComparison_app_model R A.1.complex A.2.val A.1.bound A.1.bdd A.1.perfect)
    exact h1.trans h2.symm
  exact NatTrans.congr_app key (op (⟨K, hK⟩ : PerfectObjects R), L)

/-- **Stacks Tag 0A88, for a perfect source.** For `X = Spec R` and `K, L` in `D(R)` the
canonical comparison

`R SheafHom_{O_X}(K̃, L̃) ⟶ (R Hom_R(K, L))̃`

is invertible when `K` is perfect, with no hypothesis on `L`. This is the conclusion of Tag 0A88
— that the two objects agree in `D(O_X)` — read for the canonical morphism between them, which
is what `affineDerivedTildeHomComparison_perfect` identifies it as.

The source's hypotheses are `K` in `D_Coh(R)` and `L` of finite injective dimension, over a
Noetherian `R`. The form proved here replaces the condition on `K` by perfectness and drops the
condition on `L` and the Noetherian hypothesis on `R` altogether: the proof is the reduction of
clause (3)(b) of Tag 0A6H to bounded finite-projective sources with K-injective targets, where
both the comparison and the model isomorphism are the same five-fold composite, and that
reduction asks nothing of `L`. Neither hypothesis set contains the other, so this is Tag 0A88 in
the form this development's proof supports rather than in the source's form. -/
@[stacks 0A88 "proved for K perfect and L arbitrary over any R, rather than for K in D_Coh(R) \
  and L of finite injective dimension over a Noetherian R; the comparison is the canonical \
  morphism, identified as such by affineDerivedTildeHomComparison_perfect"]
public lemma isIso_affineDerivedTildeHomComparison (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.Perfect.IsPerfect K) :
    IsIso (affineDerivedTildeHomComparison R K L) := by
  rw [affineDerivedTildeHomComparison_perfect R K L hK]
  exact (affinePerfectDerivedSheafHomIso R K L hK).isIso_inv

end AlgebraicGeometry

end
