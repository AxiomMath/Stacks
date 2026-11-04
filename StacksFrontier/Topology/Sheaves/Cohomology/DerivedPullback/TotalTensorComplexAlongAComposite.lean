module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorAlongAComposite

/-!
# The comparison of total tensor complexes along a composite

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso` is the comparison of total
tensor complexes

`f^*Tot(K ⊗_{𝒪_Y} L) ≅ Tot(f^*K ⊗_{𝒪_X} f^*L)`,

and `Stacks.DerivedPullback.Composition.modulePullbackComp` is the composition law
`g^* ⋙ f^* ≅ (f ≫ g)^*` for pullback.  This file proves that the two are compatible: reading
the comparison for `f ≫ g` after the composition law is the same as reading the comparison for
`g`, then the comparison for `f`, and then the composition law in each tensor factor of the
target total complex.

This is the complex-level statement the K-flat reduction of Stacks 079U along a composite needs,
and it is the degreewise statement `Stacks.PullbackTensorComposition.comparison_comp` — the
compatibility of the comparison of Stacks 01CD with the composition law — assembled over the
summands of a total complex.

## Main results

* `Stacks.TotalTensorComplexComposite.totalComplexComparison_comp`: the statement in the
  abstract.  Three functors related by a composition isomorphism, three bifunctors compared
  degreewise, and three comparisons of total complexes described on their summands give the
  composite identity.
* `Stacks.Cohomology.DerivedPullbackTensor.ι_pullbackTensorComplexIsoOfIsIso_hom` and
  `Stacks.Cohomology.DerivedPullbackTensor.ι_pullbackTensorComplexIsoOfIsIso_inv`: **the
  comparison of total tensor complexes on the summand indexed by `(p, q)`** is the degreewise
  comparison of Stacks 01CD there.
* `Stacks.PullbackTensorComposition.tensorSheaf_map_pair`: the tensor product on a morphism of
  the product category is the two partial morphism actions of the curried bifunctor, composed —
  the bridge between the two spellings of the tensor product on morphisms.
* `Stacks.PullbackTensorComposition.pullbackComplexCompIso`: the composition law for pullback on
  cochain complexes, with its type read at
  `Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex`.
* `Stacks.PullbackTensorComposition.pullbackTensorComplexIsoOfIsIso_comp` and
  `Stacks.PullbackTensorComposition.pullbackTensorComplexNatIso_comp`: **the comparison of total
  tensor complexes is compatible with the composition law for pullback**, on the pointwise
  comparison and on the comparison as an isomorphism of bifunctors.

## Implementation notes

*Why the abstract lemma.*  The concrete bifunctors here are the tensor product of sheaves of
modules at two different spellings of the structure sheaf, and a goal mixing them is not
type-correct at `implicit` transparency without the `implicit_reducible` attributes below.
Inside the abstract lemma every object is a variable, so the rewrites that assemble the
summandwise identities — reassociation, functoriality, naturality — are ordinary rewrites.  The
concrete statement is then one application of it, in which the only definitional work is
matching the bifunctors and functors against the variables.

*Why the abstract lemma takes the composition isomorphism twice.*  It takes the natural
isomorphism `γ` of the underlying functors, and separately the three components it needs of the
induced isomorphism of functors on complexes, with their degreewise descriptions.  Written
instead as `(CategoryTheory.Functor.mapHomologicalComplexCompIso γ _).hom.app K`, the source of
that morphism is `(Pg.mapHomologicalComplex _ ⋙ Pf.mapHomologicalComplex _).obj K` rather than
`(Pf.mapHomologicalComplex _).obj ((Pg.mapHomologicalComplex _).obj K)`, and the
`HomologicalComplex.HasMapBifunctor` hypothesis stated at the second spelling is then not found
by instance search at the first.

*Why `pullbackComplexCompIso` exists.*  It is
`CategoryTheory.Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)` and nothing else,
as `pullbackComplexCompIso_eq` records; what the declaration adds is its *type*.  Read at
`Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex`, its components are morphisms of
complexes of modules in the spelling carrying the instances of
`Stacks.SheafOfModules.Tensor.sheafTensor`; read at
`RingedSpaceModuleAdjunction.modulePullback` they are not, and
`HomologicalComplex.mapBifunctorMap` applied to them then fails to synthesize
`(Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).PreservesZeroMorphisms`.

*Why `mapBifunctorTotalIso` is named explicitly.*  Applying
`CategoryTheory.Functor.ι_mapBifunctorTotalIso_hom` to an expected type phrased with
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso` makes the elaborator
unfold that definition under metavariables standing for the instance arguments, which does not
terminate inside the heartbeat budget.  Rewriting with
`pullbackTensorComplexIsoOfIsIso_eq_mapBifunctorTotalIso` first — an equation holding by `rfl`,
with every argument explicit — puts `CategoryTheory.Functor.mapBifunctorTotalIso` in the goal
syntactically, after which the application is immediate and the two naturality arguments of the
degreewise comparison are determined by unification.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

universe u

/-! ### The composite identity, in the abstract -/

namespace Stacks.TotalTensorComplexComposite

section Helpers

variable {C : Type*} [Category C]

/-- Cancelling an isomorphism in the image of a functor and an isomorphism, from the left. -/
private lemma map_comp_eq {C' : Type*} [Category C'] {A B : C} {D E : C'}
    (G : C ⥤ C') (a : A ≅ B) (b : G.obj B ≅ D) (m : D ⟶ E) (t : G.obj A ⟶ E)
    (h : m = b.inv ≫ G.map a.inv ≫ t) : G.map a.hom ≫ b.hom ≫ m = t := by
  rw [h, Iso.hom_inv_id_assoc, ← G.map_comp_assoc, a.hom_inv_id, G.map_id, Category.id_comp]

/-- The same cancellation, read as a description of the middle morphism. -/
private lemma eq_inv_comp_of_comp {C' : Type*} [Category C'] {A B : C} {D E : C'}
    (G : C ⥤ C') (a : A ≅ B) (b : G.obj B ≅ D) (m : D ⟶ E) (t : G.obj A ⟶ E)
    (h : G.map a.hom ≫ b.hom ≫ m = t) : m = b.inv ≫ G.map a.inv ≫ t := by
  rw [← h, ← G.map_comp_assoc, a.inv_hom_id, G.map_id, Category.id_comp, Iso.inv_hom_id_assoc]

/-- A square describing a morphism through an isomorphism, transported to the inverse of that
isomorphism.  The isomorphism whose inverse appears is given as a two-sided pair rather than as
an `Iso`, because in use it is the degree-`n` component of an isomorphism of complexes. -/
private lemma inv_of_hom {A₁ A₂ B₁ B₂ : C} (eh : A₁ ⟶ A₂) (ei : A₂ ⟶ A₁)
    (hei : eh ≫ ei = 𝟙 A₁) (ε : B₁ ≅ B₂) (u : B₁ ⟶ A₁) (v : B₂ ⟶ A₂)
    (h : u ≫ eh = ε.hom ≫ v) : v ≫ ei = ε.inv ≫ u := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, hei, Category.comp_id]

end Helpers

section Abstract

variable {A₁ A₂ A₃ : Type*} [Category A₁] [Category A₂] [Category A₃]
  [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
  (F₁ : A₁ ⥤ A₁ ⥤ A₁) (F₂ : A₂ ⥤ A₂ ⥤ A₂) (F₃ : A₃ ⥤ A₃ ⥤ A₃)
  [F₁.PreservesZeroMorphisms] [∀ a, (F₁.obj a).PreservesZeroMorphisms]
  [F₂.PreservesZeroMorphisms] [∀ a, (F₂.obj a).PreservesZeroMorphisms]
  [F₃.PreservesZeroMorphisms] [∀ a, (F₃.obj a).PreservesZeroMorphisms]
  (Pg : A₁ ⥤ A₂) (Pf : A₂ ⥤ A₃) (Ph : A₁ ⥤ A₃)
  [Pg.Additive] [Pf.Additive] [Ph.Additive]
  (γ : Pg ⋙ Pf ≅ Ph)
  (εg : ∀ a b : A₁, Pg.obj ((F₁.obj a).obj b) ≅ (F₂.obj (Pg.obj a)).obj (Pg.obj b))
  (εf : ∀ a b : A₂, Pf.obj ((F₂.obj a).obj b) ≅ (F₃.obj (Pf.obj a)).obj (Pf.obj b))
  (εh : ∀ a b : A₁, Ph.obj ((F₁.obj a).obj b) ≅ (F₃.obj (Ph.obj a)).obj (Ph.obj b))
  (K L : CochainComplex A₁ ℤ)
  [HomologicalComplex.HasMapBifunctor K L F₁ (ComplexShape.up ℤ)]
  [HomologicalComplex.HasMapBifunctor ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₂ (ComplexShape.up ℤ)]
  [HomologicalComplex.HasMapBifunctor
    ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F₃ (ComplexShape.up ℤ)]
  [HomologicalComplex.HasMapBifunctor ((Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    ((Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₃ (ComplexShape.up ℤ)]

/-- **The comparison of total complexes is compatible with a composition isomorphism.**

Given three comparisons of total complexes, each described on the summands of its target by the
corresponding degreewise comparison, and given that the three degreewise comparisons are
compatible with the composition isomorphism `γ : Pg ⋙ Pf ≅ Ph`, the comparison for `Ph` read
after `γ` is the comparison for `Pg`, then the comparison for `Pf`, then `γ` in each tensor
factor.

Checked on the summands of the total complex `Tot(F₃(Pf Pg K, Pf Pg L))`: there the left side is
`HomologicalComplex.ι_mapBifunctorMap` and the right side is the two comparisons followed by the
naturality of `γ` at the inclusion of a summand. -/
lemma totalComplexComparison_comp
    (hε : ∀ a b : A₁,
      Pf.map (εg a b).hom ≫ (εf (Pg.obj a) (Pg.obj b)).hom ≫
          ((F₃.map (γ.hom.app a)).app (Pf.obj (Pg.obj b)) ≫
            (F₃.obj (Ph.obj a)).map (γ.hom.app b)) =
        γ.hom.app ((F₁.obj a).obj b) ≫ (εh a b).hom)
    (βg : (Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (HomologicalComplex.mapBifunctor K L F₁ (ComplexShape.up ℤ)) ≅
        HomologicalComplex.mapBifunctor
          ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₂ (ComplexShape.up ℤ))
    (βf : (Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (HomologicalComplex.mapBifunctor
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₂ (ComplexShape.up ℤ)) ≅
        HomologicalComplex.mapBifunctor
          ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
          ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F₃ (ComplexShape.up ℤ))
    (βh : (Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (HomologicalComplex.mapBifunctor K L F₁ (ComplexShape.up ℤ)) ≅
        HomologicalComplex.mapBifunctor
          ((Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₃ (ComplexShape.up ℤ))
    (hg : ∀ (p q n : ℤ) (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = n),
      Pg.map (HomologicalComplex.ιMapBifunctor K L F₁ (ComplexShape.up ℤ) p q n h) ≫
          βg.hom.f n =
        (εg (K.X p) (L.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₂
            (ComplexShape.up ℤ) p q n h)
    (hf : ∀ (p q n : ℤ) (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = n),
      Pf.map (HomologicalComplex.ιMapBifunctor
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₂
            (ComplexShape.up ℤ) p q n h) ≫ βf.hom.f n =
        (εf (Pg.obj (K.X p)) (Pg.obj (L.X q))).hom ≫
          HomologicalComplex.ιMapBifunctor
            ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
            ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F₃
            (ComplexShape.up ℤ) p q n h)
    (hh : ∀ (p q n : ℤ) (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = n),
      Ph.map (HomologicalComplex.ιMapBifunctor K L F₁ (ComplexShape.up ℤ) p q n h) ≫
          βh.hom.f n =
        (εh (K.X p) (L.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            ((Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            ((Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₃
            (ComplexShape.up ℤ) p q n h)
    (δK : (Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
        (Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (δL : (Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ⟶
        (Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    (δT : (Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (HomologicalComplex.mapBifunctor K L F₁ (ComplexShape.up ℤ))) ⟶
        (Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (HomologicalComplex.mapBifunctor K L F₁ (ComplexShape.up ℤ)))
    (hδK : ∀ p : ℤ, δK.f p = γ.hom.app (K.X p))
    (hδL : ∀ q : ℤ, δL.f q = γ.hom.app (L.X q))
    (hδT : ∀ n : ℤ, δT.f n =
      γ.hom.app ((HomologicalComplex.mapBifunctor K L F₁ (ComplexShape.up ℤ)).X n)) :
    (Pf.mapHomologicalComplex (ComplexShape.up ℤ)).map βg.hom ≫ βf.hom ≫
        HomologicalComplex.mapBifunctorMap δK δL F₃ (ComplexShape.up ℤ) =
      δT ≫ βh.hom := by
  refine map_comp_eq (Pf.mapHomologicalComplex (ComplexShape.up ℤ)) βg βf _ _ ?_
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  have hβg : βg.hom.f n ≫ βg.inv.f n = 𝟙 _ :=
    congrArg (fun t => HomologicalComplex.Hom.f t n) βg.hom_inv_id
  have hβf : βf.hom.f n ≫ βf.inv.f n = 𝟙 _ :=
    congrArg (fun t => HomologicalComplex.Hom.f t n) βf.hom_inv_id
  have hgI := inv_of_hom (βg.hom.f n) (βg.inv.f n) hβg (εg (K.X p) (L.X q)) _ _ (hg p q n hpq)
  have hfI := inv_of_hom (βf.hom.f n) (βf.inv.f n) hβf
    (εf (Pg.obj (K.X p)) (Pg.obj (L.X q))) _ _ (hf p q n hpq)
  have hnat := γ.hom.naturality
    (HomologicalComplex.ιMapBifunctor K L F₁ (ComplexShape.up ℤ) p q n hpq)
  rw [Functor.comp_map] at hnat
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.ι_mapBifunctorMap, Functor.mapHomologicalComplex_map_f]
  simp only [hδK, hδL, hδT]
  rw [reassoc_of% hfI, ← Pf.map_comp_assoc, hgI, Pf.map_comp_assoc, reassoc_of% hnat,
    hh p q n hpq]
  exact (reassoc_of% (eq_inv_comp_of_comp Pf (εg (K.X p) (L.X q))
    (εf (Pg.obj (K.X p)) (Pg.obj (L.X q))) _ _ (hε (K.X p) (L.X q)))) _

end Abstract

end Stacks.TotalTensorComplexComposite

/-! ### The comparison of total tensor complexes on a summand -/

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] modulePullback_preservesAntidiagonalCoproducts

-- The two attributes of `PullbackTensorComparison.lean`: the pullback development and the
-- tensor-product development name the structure sheaf of a ringed space differently, and a
-- statement mixing them is not type-correct at `implicit` transparency unless the first is
-- unfolded there.
attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The comparison of total tensor complexes is `CategoryTheory.Functor.mapBifunctorTotalIso`**
at the tensor bifunctors of `Y` and `X`, the degreewise comparison of Stacks 01CD, and the
degreewise pullback.  This holds by `rfl`; it is stated so that the summand descriptions of
`mapBifunctorTotalIso` can be rewritten into a goal rather than unified against it. -/
private lemma pullbackTensorComplexIsoOfIsIso_eq_mapBifunctorTotalIso
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexIsoOfIsIso f K L =
      CategoryTheory.Functor.mapBifunctorTotalIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
        (StacksDraft.KFlat.modulePullback f) (StacksDraft.KFlat.modulePullback f)
        (StacksDraft.KFlat.modulePullback f) (comparisonAppIso f)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (fun {_ _} v B => comparisonAppIso_naturality_left f v B)
        (fun A {_ _} w => comparisonAppIso_naturality_right f A w) K L :=
  rfl

/-- **The comparison of total tensor complexes, on the summand indexed by `(p, q)`:** it is the
degreewise comparison of Stacks 01CD, `f^*(K^p ⊗_{𝒪_Y} L^q) ≅ f^*K^p ⊗_{𝒪_X} f^*L^q`, followed
by the inclusion of that summand of the target. -/
lemma ι_pullbackTensorComplexIsoOfIsIso_hom
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex.ιMapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) (ComplexShape.up ℤ) p q n h) ≫
        (pullbackTensorComplexIsoOfIsIso f K L).hom.f n =
      (comparisonAppIso f (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) p q n h := by
  rw [pullbackTensorComplexIsoOfIsIso_eq_mapBifunctorTotalIso f K L]
  refine CategoryTheory.Functor.ι_mapBifunctorTotalIso_hom _ _ _ _ _ _ _ _ ?_ ?_ K L p q n h

/-- The same on the inverse, which is the direction extensionality on the summands of the target
total complex applies to. -/
lemma ι_pullbackTensorComplexIsoOfIsIso_inv
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) p q n h ≫
        (pullbackTensorComplexIsoOfIsIso f K L).inv.f n =
      (comparisonAppIso f (K.X p) (L.X q)).inv ≫
        (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex.ιMapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) (ComplexShape.up ℤ)
            p q n h) := by
  rw [pullbackTensorComplexIsoOfIsIso_eq_mapBifunctorTotalIso f K L]
  refine CategoryTheory.Functor.ι_mapBifunctorTotalIso_inv _ _ _ _ _ _ _ _ ?_ ?_ K L p q n h

/-- The value of the comparison of total tensor complexes, as an isomorphism of bifunctors, at a
pair of complexes.  This holds by `rfl`: the natural isomorphism is
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPairTransport`, whose components are
exactly the pointwise comparison. -/
lemma pullbackTensorComplexNatIso_hom_app
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackTensorComplexNatIso f).hom.app (K, L) =
      (pullbackTensorComplexIsoOfIsIso f K L).hom :=
  rfl

/-- `pullbackTensorComplexNatIso_hom_app` on the inverse. -/
lemma pullbackTensorComplexNatIso_inv_app
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackTensorComplexNatIso f).inv.app (K, L) =
      (pullbackTensorComplexIsoOfIsIso f K L).inv :=
  rfl

end Stacks.Cohomology.DerivedPullbackTensor

/-! ### The comparison of total tensor complexes along a composite -/

namespace Stacks.PullbackTensorComposition

open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] modulePullback_preservesAntidiagonalCoproducts

-- `Stacks.SheafOfModules.Tensor.ringSheaf` is on this list for the reason the others are: the
-- modules `A` and `B` below are typed over `Stacks.RingedSpace.structureRingSheaf`, the tensor
-- bifunctor over `Tensor.ringSheaf`, and the reducts of the two meet only once
-- `Tensor.ringSheaf` unfolds.  Until it does, a goal mixing them is not type-correct at
-- `implicit` transparency, and the `simp only` rewrites below are silently discarded.
attribute [local implicit_reducible] structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf
  StacksDraft.KFlat.modulePullback TopCat.Presheaf.IsSheaf TopCat.Sheaf
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The composition law for pullback on cochain complexes**, with its type read at
`Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex`.  It is
`CategoryTheory.Functor.mapHomologicalComplexCompIso` applied to
`Stacks.DerivedPullback.Composition.modulePullbackComp` and nothing else; see
`pullbackComplexCompIso_eq`. -/
def pullbackComplexCompIso :
    pullbackComplex g ⋙ pullbackComplex f ≅ pullbackComplex (f ≫ g) :=
  Functor.mapHomologicalComplexCompIso
    (Stacks.DerivedPullback.Composition.modulePullbackComp f g) (ComplexShape.up ℤ)

/-- `pullbackComplexCompIso` is the induced isomorphism of functors on complexes: the
declaration changes the type and no data. -/
lemma pullbackComplexCompIso_eq :
    pullbackComplexCompIso f g =
      Functor.mapHomologicalComplexCompIso
        (Stacks.DerivedPullback.Composition.modulePullbackComp f g) (ComplexShape.up ℤ) :=
  rfl

/-- The composition law for pullback on complexes, in a single degree: it is the composition
law at the term of that degree. -/
lemma pullbackComplexCompIso_hom_app_f
    (M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (n : ℤ) :
    ((pullbackComplexCompIso f g).hom.app M).f n =
      (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app (M.X n) :=
  rfl

/-- The tensor product bifunctor on pairs, on a morphism of pairs: it is the two partial
morphism actions of the curried bifunctor, composed.

This is the bridge between the product-category spelling `Stacks.RingedSpace.tensorSheaf` of
the tensor product and the curried spelling `Stacks.SheafOfModules.Tensor.sheafTensor`, on
morphisms; every statement that reads a summand of a total tensor complex against a map of the
product category needs it. -/
lemma tensorSheaf_map_pair {W : RingedSpace.{u, u}}
    {A A' B B' : SheafOfModules.{u} (structureRingSheaf W)} (a : A ⟶ A') (b : B ⟶ B') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf))).map ((a, b) : ((A, B) : _ × _) ⟶ (A', B')) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).map a).app B ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj A').map b :=
  rfl

/-- **Stacks 01CD along a composite, in the shape the total-complex statement consumes.**  This
is `comparison_comp`, with the comparison written as the `hom` of
`Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso`, the action of the tensor product on
a pair of morphisms written through the curried bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, and the pullback functor written at the spelling
that bifunctor's instances are carried at.  Every passage between the two spellings is the
conversion check of this one `exact`. -/
private lemma comparisonAppIso_comp
    (A B : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :
    (StacksDraft.KFlat.modulePullback f).map (comparisonAppIso g A B).hom ≫
        (comparisonAppIso f ((StacksDraft.KFlat.modulePullback g).obj A)
            ((StacksDraft.KFlat.modulePullback g).obj B)).hom ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
                ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app A)).app
              ((StacksDraft.KFlat.modulePullback f).obj
                ((StacksDraft.KFlat.modulePullback g).obj B)) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
                ((StacksDraft.KFlat.modulePullback (f ≫ g)).obj A)).map
              ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app B)) =
      (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj A).obj B) ≫
        (comparisonAppIso (f ≫ g) A B).hom := by
  simpa only [comparisonAppIso, comparisonNatTrans, asIso_hom,
    StacksDraft.KFlat.modulePullback_eq_modulePullback, pullbackFunctor,
    AlgebraicGeometry.SheafedSpace.sheaf, Functor.comp_obj,
    Functor.uncurry_obj_obj, Functor.uncurry_obj_map, Category.assoc] using
    (comparison_comp f g A B).symm

/-- **The comparison of total tensor complexes is compatible with the composition law for
pullback.**  For cochain complexes `K` and `L` of `𝒪_Z`-modules, the composition law followed by
the comparison

`(f ≫ g)^*Tot(K ⊗_{𝒪_Z} L) ≅ Tot((f ≫ g)^*K ⊗_{𝒪_X} (f ≫ g)^*L)`

is the comparison for `g`, then the comparison for `f`, then the composition law in each tensor
factor.

This is the complex-level form of `Stacks.PullbackTensorComposition.comparison_comp`: after
cancelling the two comparisons both sides are morphisms out of the total complex
`Tot(f^*g^*K ⊗_{𝒪_X} f^*g^*L)`, extensionality holds on its summands, and there the identity is
that degreewise statement together with the naturality of the composition law at the inclusion
of a summand. -/
theorem pullbackTensorComplexIsoOfIsIso_comp
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (pullbackComplex f).map (pullbackTensorComplexIsoOfIsIso g K L).hom ≫
        (pullbackTensorComplexIsoOfIsIso f ((pullbackComplex g).obj K)
            ((pullbackComplex g).obj L)).hom ≫
          HomologicalComplex.mapBifunctorMap ((pullbackComplexCompIso f g).hom.app K)
            ((pullbackComplexCompIso f g).hom.app L)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) =
      (pullbackComplexCompIso f g).hom.app
          (HomologicalComplex.mapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (ComplexShape.up ℤ)) ≫
        (pullbackTensorComplexIsoOfIsIso (f ≫ g) K L).hom :=
  Stacks.TotalTensorComplexComposite.totalComplexComparison_comp
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
    (StacksDraft.KFlat.modulePullback g) (StacksDraft.KFlat.modulePullback f)
    (StacksDraft.KFlat.modulePullback (f ≫ g))
    (Stacks.DerivedPullback.Composition.modulePullbackComp f g)
    (comparisonAppIso g) (comparisonAppIso f) (comparisonAppIso (f ≫ g)) K L
    (comparisonAppIso_comp f g)
    (pullbackTensorComplexIsoOfIsIso g K L)
    (pullbackTensorComplexIsoOfIsIso f ((pullbackComplex g).obj K)
      ((pullbackComplex g).obj L))
    (pullbackTensorComplexIsoOfIsIso (f ≫ g) K L)
    (ι_pullbackTensorComplexIsoOfIsIso_hom g K L)
    (ι_pullbackTensorComplexIsoOfIsIso_hom f ((pullbackComplex g).obj K)
      ((pullbackComplex g).obj L))
    (ι_pullbackTensorComplexIsoOfIsIso_hom (f ≫ g) K L)
    ((pullbackComplexCompIso f g).hom.app K) ((pullbackComplexCompIso f g).hom.app L)
    ((pullbackComplexCompIso f g).hom.app
      (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (ComplexShape.up ℤ)))
    (pullbackComplexCompIso_hom_app_f f g K) (pullbackComplexCompIso_hom_app_f f g L)
    (pullbackComplexCompIso_hom_app_f f g
      (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (ComplexShape.up ℤ)))

/-- `pullbackTensorComplexIsoOfIsIso_comp` read on the comparison as an isomorphism of
bifunctors, which is the form the K-flat reduction of Stacks 079U uses. -/
theorem pullbackTensorComplexNatIso_comp
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (pullbackComplex f).map ((pullbackTensorComplexNatIso g).hom.app (K, L)) ≫
        (pullbackTensorComplexNatIso f).hom.app
            ((pullbackComplex g).obj K, (pullbackComplex g).obj L) ≫
          HomologicalComplex.mapBifunctorMap ((pullbackComplexCompIso f g).hom.app K)
            ((pullbackComplexCompIso f g).hom.app L)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) =
      (pullbackComplexCompIso f g).hom.app
          (HomologicalComplex.mapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (ComplexShape.up ℤ)) ≫
        (pullbackTensorComplexNatIso (f ≫ g)).hom.app (K, L) :=
  pullbackTensorComplexIsoOfIsIso_comp f g K L

end Stacks.PullbackTensorComposition

end
