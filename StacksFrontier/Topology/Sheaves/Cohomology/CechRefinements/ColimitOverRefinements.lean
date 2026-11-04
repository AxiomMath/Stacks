module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ToSheafCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology of a space as the colimit over its open coverings

Let `X` be a topological space and `F` an abelian sheaf on `X`.  For a single open covering
`𝒰` of `X` the Čech cohomology `Ȟ^p(𝒰, F)` comes with a canonical map to the sheaf cohomology
`H^p(X, F)`, by Stacks 03AX applied to the site of open subsets of `X`.  A refinement of
coverings induces a map of Čech complexes, by Stacks 03F4, and the resulting maps on Čech
cohomology are compatible with the maps to sheaf cohomology.  Taking the colimit over all
open coverings of `X` therefore produces

`Ȟ^p(X, F) = colim_𝒰 Ȟ^p(𝒰, F) ⟶ H^p(X, F)`,

which is Stacks 09UZ.

## Main definitions

* `Stacks.Cohomology.CechRefinement.OpenCoverSet`: an open covering of `X` given by a *set* of
  open subsets, and `Hom` the refinements between two such coverings.
* `Stacks.Cohomology.CechRefinement.hypercover`: such a covering as a covering family of the
  terminal object of the site of opens of `X`.
* `Stacks.Cohomology.CechRefinement.refinementCochainMap`: the map of Čech complexes induced
  by a refinement.
* `Stacks.Cohomology.CechRefinement.cechDiagram`: Čech cohomology in a fixed degree, as a
  functor of the covering.
* `Stacks.Cohomology.CechRefinement.colimitToCohomology`: the canonical map from global Čech
  cohomology, the colimit of `cechDiagram`, to sheaf cohomology.
* `Stacks.Cohomology.CechRefinement.uliftSheaf`: an abelian sheaf with its values raised to a
  universe containing the one of the space.

## Main results

* `Stacks.Cohomology.CechRefinement.exists_common_refinement`: any two open coverings admit a
  common refinement, so the colimit above is a colimit over a connected index category.
* `Stacks.Cohomology.CechRefinement.ι_colimitToCohomology`: on each covering the map out of
  the colimit is the fixed-covering comparison of Stacks 03AX.

## Implementation notes

The index category must be small for the colimit to exist, so a covering is recorded as a set
of open subsets rather than as an indexed family; this loses only repetitions, which do not
change Čech cohomology.  A morphism of coverings carries a *chosen* refinement function, which
is what makes the coverings into a category rather than a preorder, and which the induced map
of Čech complexes depends on.  Over a topological space the comparison maps of the iterated
intersections are not part of that choice: `Opens X` is a partial order, so all its parallel
morphisms are equal, and consequently the refinement maps of Čech complexes are functorial
without any further compatibility being imposed — this is what
`refinementCochainMap_id` and `refinementCochainMap_comp` come down to.

The abelian sheaf is allowed to take values in a universe independent of the one of the space;
`uliftSheaf` raises its values so that the products over a covering and the colimit over all
coverings can be formed.

## References

* [Stacks Project, Tag 09UZ](https://stacks.math.columbia.edu/tag/09UZ)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
* [Stacks Project, Tag 03F4](https://stacks.math.columbia.edu/tag/03F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.Cohomology.CechRefinement

variable {X : Type u} [TopologicalSpace X]

/-- Finite products exist in the category of opens over a fixed open: the category of opens of
a space has all finite wide pullbacks, being a complete lattice. -/
instance hasFiniteProducts_overOpens (U : Opens X) : HasFiniteProducts (Over U) :=
  CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- An open covering of the whole space, recorded as a set of open subsets.  Using a set rather
than an indexed family keeps the collection of all coverings small, which is what allows the
colimit over all coverings to be formed; it loses only repetitions, which do not affect Čech
cohomology. -/
structure OpenCoverSet (X : Type u) [TopologicalSpace X] where
  /-- The members of the covering. -/
  members : Set (Opens X)
  /-- The members cover the whole space. -/
  iSup_eq_top : ⨆ V : members, V.1 = ⊤

namespace OpenCoverSet

/-- A morphism `U ⟶ V` of open coverings exhibits `V` as a refinement of `U`: it chooses, for
each member of `V`, a member of `U` containing it. -/
@[ext]
structure Hom (U V : OpenCoverSet X) where
  /-- The chosen member of `U` containing a given member of `V`. -/
  index : V.members → U.members
  /-- Each member of the refining covering lies in its chosen member. -/
  le_index (j : V.members) : j.1 ≤ (index j).1

/-- Open coverings of a space, with the refinements between them, form a category. -/
instance : Category (OpenCoverSet X) where
  Hom := Hom
  id _ := ⟨id, fun _ ↦ le_rfl⟩
  comp f g := ⟨f.index ∘ g.index, fun j ↦ (g.le_index j).trans (f.le_index (g.index j))⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The identity refinement chooses each member of a covering as its own containing member. -/
@[simp] theorem id_index (U : OpenCoverSet X) : Hom.index (𝟙 U) = id := rfl

/-- The index map of a composite refinement is the composite of the index maps. -/
@[simp] theorem comp_index {U V W : OpenCoverSet X} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).index = f.index ∘ g.index := rfl

/-- An open covering, as a covering family of the terminal object of the site of open subsets
of the space. -/
def hypercover (U : OpenCoverSet X) : PreZeroHypercover.{u} (⊤ : Opens X) where
  I₀ := U.members
  X i := i.1
  f _ := homOfLE le_top

/-- The object of the covering family indexed by a member of the covering is that member. -/
@[simp] theorem hypercover_X (U : OpenCoverSet X) (i : U.members) :
    (hypercover U).X i = i.1 := rfl

/-- The covering family attached to an open covering generates a covering sieve. -/
theorem hypercover_mem_grothendieckTopology (U : OpenCoverSet X) :
    Sieve.generate (hypercover U).presieve₀ ∈
      Opens.grothendieckTopology X (⊤ : Opens X) := by
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  have hx' : x ∈ (⨆ i : U.members, i.1) := by simp [U.iSup_eq_top]
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
  refine ⟨i.1, homOfLE le_top, ?_, hi⟩
  exact ⟨i.1, 𝟙 _, homOfLE le_top, (hypercover U).presieve₀_f i, by simp⟩

/-- A refinement of open coverings, as a morphism of the associated covering families over the
identity of the covered object. -/
def homOver {U V : OpenCoverSet X} (f : U ⟶ V) :
    (hypercover V).HomOver (hypercover U) (𝟙 (⊤ : Opens X)) where
  s₀ j := f.index j
  h₀ j := homOfLE (f.le_index j)
  w₀ _ := Subsingleton.elim _ _

/-- Any two open coverings of a space have a common refinement, namely the covering by the
pairwise intersections of their members. -/
theorem exists_common_refinement (U V : OpenCoverSet X) :
    ∃ W : OpenCoverSet X, Nonempty (U ⟶ W) ∧ Nonempty (V ⟶ W) := by
  classical
  refine ⟨{ members := Set.range (fun ij : U.members × V.members ↦ ij.1.1 ⊓ ij.2.1)
            iSup_eq_top := le_antisymm le_top ?_ }, ?_, ?_⟩
  · calc (⊤ : Opens X) = (⨆ i : U.members, i.1) ⊓ ⨆ j : V.members, j.1 := by
          rw [U.iSup_eq_top, V.iSup_eq_top, inf_top_eq]
      _ = ⨆ ij : U.members × V.members, ij.1.1 ⊓ ij.2.1 := iSup_inf_iSup
      _ ≤ _ := iSup_le fun ij ↦ le_iSup_of_le ⟨ij.1.1 ⊓ ij.2.1, ⟨ij, rfl⟩⟩ le_rfl
  · exact ⟨{ index := fun j ↦ (Classical.choose j.2).1
             le_index := fun j ↦ (Classical.choose_spec j.2).symm.le.trans inf_le_left }⟩
  · exact ⟨{ index := fun j ↦ (Classical.choose j.2).2
             le_index := fun j ↦ (Classical.choose_spec j.2).symm.le.trans inf_le_right }⟩

end OpenCoverSet

open OpenCoverSet

section Refinement

variable {U V W : OpenCoverSet X}

/-- Parallel morphisms of opens agree, so the restriction maps of a presheaf of abelian groups
between two fixed opens all coincide. -/
theorem map_op_apply_eq (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) {A B : Opens X}
    (g h : A ⟶ B) (y : P.obj (op B)) : P.map g.op y = P.map h.op y := by
  rw [Subsingleton.elim g h]

/-- A restriction map of a presheaf of abelian groups along an endomorphism of an open is the
identity, since that endomorphism is the identity. -/
private theorem map_op_apply_self (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) {A : Opens X}
    (g : A ⟶ A) (y : P.obj (op A)) : P.map g.op y = y := by
  simp [Subsingleton.elim g (𝟙 A)]

/-- A morphism of presheaves of abelian groups commutes with restriction. -/
theorem app_map_op {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}} (φ : P ⟶ Q)
    {A B : Opens X} (h : A ⟶ B) (z : P.obj (op B)) :
    Q.map h.op (φ.app (op B) z) = φ.app (op A) (P.map h.op z) :=
  (ConcreteCategory.comp_apply (φ.app (op B)) (Q.map h.op) z).symm.trans
    ((ConcreteCategory.congr_hom (φ.naturality h.op) z).symm.trans
      (ConcreteCategory.comp_apply (P.map h.op) (φ.app (op A)) z))

/-- **Stacks 03F4** for open coverings: the map of Čech complexes induced by a refinement. -/
def refinementCochainMap (f : U ⟶ V) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    CechSite.cechComplex (hypercover U) P ⟶ CechSite.cechComplex (hypercover V) P :=
  CechSite.cechComplexMap (hypercover V) (hypercover U) (homOver f) P

/-- In every degree, the refinement map restricts the component indexed by a tuple of members
of the refining covering from the component indexed by the chosen members of the refined
covering. -/
theorem refinementCochainMap_f_π (f : U ⟶ V) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (n : ℕ) (i : Fin (n + 1) → V.members) :
    (refinementCochainMap f P).f n ≫ Pi.π (CechSite.cochainFactor (hypercover V) P n) i =
      Pi.π (CechSite.cochainFactor (hypercover U) P n) (f.index ∘ i) ≫
        P.map (CechSite.cechProductMap (hypercover V) (hypercover U) (homOver f) n i).op :=
  CechSite.cechComplexMap_f_Pi_π (hypercover V) (hypercover U) (homOver f) P n i

/-- The degreewise description of the refinement map, on elements. -/
theorem refinementCochainMap_f_π_apply (f : U ⟶ V)
    (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) (i : Fin (n + 1) → V.members)
    (x : (CechSite.cechComplex (hypercover U) P).X n) :
    Pi.π (CechSite.cochainFactor (hypercover V) P n) i ((refinementCochainMap f P).f n x) =
      P.map (CechSite.cechProductMap (hypercover V) (hypercover U) (homOver f) n i).op
        (Pi.π (CechSite.cochainFactor (hypercover U) P n) (f.index ∘ i) x) :=
  ConcreteCategory.congr_hom (refinementCochainMap_f_π f P n i) x

/-- Composing two restriction maps of a presheaf of abelian groups is a single restriction
map, along any morphism with the same source and target. -/
public theorem map_op_comp_apply_eq (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {A B C' : Opens X} (a : C' ⟶ B) (b : B ⟶ A) (c : C' ⟶ A) (y : P.obj (op A)) :
    P.map a.op (P.map b.op y) = P.map c.op y := by
  have h : P.map a.op (P.map b.op y) = P.map (a ≫ b).op y := by
    rw [op_comp, P.map_comp]; rfl
  exact h.trans (map_op_apply_eq P _ c y)

/-- Two elements of a degree of a Čech complex are equal when all their components agree. -/
private theorem cechComplex_X_ext (V : OpenCoverSet X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {n : ℕ} {x y : (CechSite.cechComplex (hypercover V) P).X n}
    (h : ∀ i, Pi.π (CechSite.cochainFactor (hypercover V) P n) i x =
      Pi.π (CechSite.cochainFactor (hypercover V) P n) i y) : x = y := by
  apply (CechSite.productAddEquiv (CechSite.cochainFactor (hypercover V) P n)).injective
  ext i
  exact h i

/-- The refinement map attached to the identity refinement is the identity. -/
@[simp]
theorem refinementCochainMap_id (U : OpenCoverSet X)
    (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) : refinementCochainMap (𝟙 U) P = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  ext x
  refine cechComplex_X_ext U P fun i ↦ ?_
  exact (refinementCochainMap_f_π_apply (𝟙 U) P n i x).trans (map_op_apply_self P _ _)

/-- The refinement maps compose contravariantly. -/
theorem refinementCochainMap_comp (f : U ⟶ V) (g : V ⟶ W)
    (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    refinementCochainMap f P ≫ refinementCochainMap g P = refinementCochainMap (f ≫ g) P := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  ext x
  refine cechComplex_X_ext W P fun i ↦ ?_
  refine (refinementCochainMap_f_π_apply g P n i _).trans ?_
  refine (congrArg (fun z ↦ P.map
    (CechSite.cechProductMap (hypercover W) (hypercover V) (homOver g) n i).op z)
      (refinementCochainMap_f_π_apply f P n (g.index ∘ i) x)).trans ?_
  exact (map_op_comp_apply_eq P _ _ _ _).trans
    (refinementCochainMap_f_π_apply (f ≫ g) P n i x).symm

/-- The refinement maps form a natural transformation of the Čech complex functors. -/
def refinementCochainNat (f : U ⟶ V) :
    CechSite.cechComplexFunctor (hypercover U) (A := AddCommGrpCat.{max u v}) ⟶
      CechSite.cechComplexFunctor (hypercover V) where
  app P := refinementCochainMap f P
  naturality P Q φ := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    ext x
    apply (CechSite.productAddEquiv (CechSite.cochainFactor (hypercover V) Q n)).injective
    ext i
    change Pi.π (CechSite.cochainFactor (hypercover V) Q n) i
        ((refinementCochainMap f Q).f n
          (((CechSite.cechComplexFunctor (hypercover U)).map φ).f n x)) =
      Pi.π (CechSite.cochainFactor (hypercover V) Q n) i
        (((CechSite.cechComplexFunctor (hypercover V)).map φ).f n
          ((refinementCochainMap f P).f n x))
    refine (refinementCochainMap_f_π_apply f Q n i _).trans ?_
    refine (congrArg (fun z ↦ Q.map
      (CechSite.cechProductMap (hypercover V) (hypercover U) (homOver f) n i).op z)
        (CechSite.cechComplexFunctor_map_f_π_apply.{max u v} (hypercover U) φ n
          (f.index ∘ i) x)).trans ?_
    refine (app_map_op φ
      (CechSite.cechProductMap (hypercover V) (hypercover U) (homOver f) n i) _).trans ?_
    refine (congrArg (fun z ↦ φ.app
      (op ((∏ᶜ fun a ↦ Over.mk ((hypercover V).f (i a)) : Over (⊤ : Opens X)).left)) z)
        (refinementCochainMap_f_π_apply f P n i x).symm).trans ?_
    exact (CechSite.cechComplexFunctor_map_f_π_apply.{max u v} (hypercover V) φ n i
      ((refinementCochainMap f P).f n x)).symm

/-- The refinement maps, as a natural transformation of the Čech complex functors on
sheaves. -/
def refinementComplexNat (f : U ⟶ V) :
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} ⋙
        CechSite.cechComplexFunctor (hypercover U) ⟶
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} ⋙
        CechSite.cechComplexFunctor (hypercover V) :=
  Functor.whiskerLeft _ (refinementCochainNat f)

/-- The refinement maps, as a natural transformation of the integer-graded Čech complex
functors. -/
def refinementComplexIntNat (f : U ⟶ V) :
    CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover U) ⟶
      CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover V) :=
  Functor.whiskerRight (refinementComplexNat f)
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v})

/-- The integer-graded refinement map is the extension by zero of the Čech cochain map. -/
theorem refinementComplexIntNat_app (f : U ⟶ V)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    (refinementComplexIntNat f).app G =
      HomologicalComplex.extendMap (refinementCochainMap f G.obj)
        ComplexShape.embeddingUpNat := by
  dsimp only [refinementComplexIntNat, refinementComplexNat, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, ComplexShape.Embedding.extendFunctor_map]
  rfl

/-- The refinement map on Čech complexes, viewed in bounded-below cochain complexes. -/
def refinementPlusMap (f : U ⟶ V)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    (CechSite.cechComplexPlusFunctor (hypercover U)).obj G.obj ⟶
      (CechSite.cechComplexPlusFunctor (hypercover V)).obj G.obj :=
  ObjectProperty.homMk ((refinementComplexIntNat f).app G)

/-- The underlying cochain map of `refinementPlusMap`. -/
theorem refinementPlusMap_hom (f : U ⟶ V)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    (refinementPlusMap f G).hom = (refinementComplexIntNat f).app G := rfl

/-- The identity refinement induces the identity of bounded-below Čech complexes. -/
@[simp]
theorem refinementPlusMap_id (U : OpenCoverSet X)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    refinementPlusMap (𝟙 U) G = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  rw [refinementPlusMap_hom, refinementComplexIntNat_app, refinementCochainMap_id]
  exact HomologicalComplex.extendMap_id _ _

/-- The refinement maps of bounded-below Čech complexes compose contravariantly. -/
theorem refinementPlusMap_comp (f : U ⟶ V) (g : V ⟶ W)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    refinementPlusMap f G ≫ refinementPlusMap g G = refinementPlusMap (f ≫ g) G := by
  apply ObjectProperty.hom_ext
  have h := congrArg
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v}).map
      (refinementCochainMap_comp f g G.obj)
  rwa [Functor.map_comp] at h

end Refinement

section Comparison

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})]
  {U V : OpenCoverSet X}

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- A refinement is compatible with the augmentations of the Čech complexes by the sections
over the whole space. -/
theorem cechAugmentationPre_refinement (f : U ⟶ V)
    (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    CechSite.cechAugmentationPre.{v} (hypercover U) P ≫ (refinementCochainMap f P).f 0 =
      CechSite.cechAugmentationPre.{v} (hypercover V) P := by
  ext s
  refine cechComplex_X_ext V P fun i ↦ ?_
  refine (refinementCochainMap_f_π_apply f P 0 i _).trans ?_
  refine (congrArg (fun z ↦ P.map
    (CechSite.cechProductMap (hypercover V) (hypercover U) (homOver f) 0 i).op z)
      (CechSite.cechAugmentationPre_π_apply.{v} (hypercover U) P (f.index ∘ i) s)).trans ?_
  exact (map_op_comp_apply_eq P _ _ _ s).trans
    (CechSite.cechAugmentationPre_π_apply.{v} (hypercover V) P i s).symm

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- A refinement is compatible with the augmentations of the integer-graded Čech complexes. -/
theorem cechAugmentationInt_refinement (f : U ⟶ V)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    CechSite.cechAugmentationInt.{v} (Opens.grothendieckTopology X) (hypercover U) G ≫
        ((refinementComplexIntNat f).app G).f 0 =
      CechSite.cechAugmentationInt.{v} (Opens.grothendieckTopology X) (hypercover V) G := by
  have h : ((refinementComplexIntNat f).app G).f 0 =
      (CechSite.cechIntXZeroIsoPre.{v} (hypercover U) G.obj).hom ≫
        (refinementCochainMap f G.obj).f 0 ≫
        (CechSite.cechIntXZeroIsoPre.{v} (hypercover V) G.obj).inv := by
    rw [refinementComplexIntNat_app]
    exact HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) rfl
  dsimp only [CechSite.cechAugmentationInt, CechSite.cechAugmentationIntPre]
  rw [h, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
    cechAugmentationPre_refinement]

variable (f : U ⟶ V)
  {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}}

/-- The map of Čech bicomplexes of an injective resolution induced by a refinement. -/
def refinementBicomplexMap (J : InjectiveResolution G) :
    CechSite.cechBicomplex.{v} (Opens.grothendieckTopology X) (hypercover U)
        J.cochainComplex ⟶
      CechSite.cechBicomplex.{v} (Opens.grothendieckTopology X) (hypercover V)
        J.cochainComplex :=
  (NatTrans.mapHomologicalComplex (refinementComplexIntNat f) (ComplexShape.up ℤ)).app
    J.cochainComplex

/-- The map of total Čech complexes of an injective resolution induced by a refinement. -/
def refinementTotalMap (J : InjectiveResolution G) :
    (CechSite.cechBicomplex.{v} (Opens.grothendieckTopology X) (hypercover U)
        J.cochainComplex).total (ComplexShape.up ℤ) ⟶
      (CechSite.cechBicomplex.{v} (Opens.grothendieckTopology X) (hypercover V)
        J.cochainComplex).total (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.map (refinementBicomplexMap f J) (ComplexShape.up ℤ)

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- **Stacks 09UZ**, the key compatibility: the comparison of Stacks 03AX from the Čech complex
of a covering to the derived sections is unchanged by passing to a refinement. -/
theorem cechToDerivedSections_refinement (J : InjectiveResolution G) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map (refinementPlusMap f G)) ≫
        ((CechSite.cechToDerivedSections.{v} (Opens.grothendieckTopology X) (hypercover V)
          (hypercover_mem_grothendieckTopology V)).app G).hom =
      ((CechSite.cechToDerivedSections.{v} (Opens.grothendieckTopology X) (hypercover U)
        (hypercover_mem_grothendieckTopology U)).app G).hom := by
  obtain ⟨rU⟩ := CechSite.nonempty_cechResolutionComparison.{v}
    (Opens.grothendieckTopology X) (hypercover U)
    (hypercover_mem_grothendieckTopology U) G J
  obtain ⟨rV⟩ := CechSite.nonempty_cechResolutionComparison.{v}
    (Opens.grothendieckTopology X) (hypercover V)
    (hypercover_mem_grothendieckTopology V) G J
  have hα : rU.α ≫ refinementTotalMap f J = rV.α := by
    refine HomologicalComplex.hom_ext _ _ fun q ↦ ?_
    rw [HomologicalComplex.comp_f, rU.α_f]
    dsimp only [refinementTotalMap, refinementBicomplexMap]
    simp only [Category.assoc, HomologicalComplex₂.ιTotal_map]
    rw [rV.α_f]
    have hAug := congrArg (fun k ↦ k ≫
      (CechSite.cechBicomplex.{v} (Opens.grothendieckTopology X) (hypercover V)
        J.cochainComplex).ιTotal (ComplexShape.up ℤ) q 0 q (by simp))
      (cechAugmentationInt_refinement f (J.cochainComplex.X q))
    simpa only [NatTrans.mapHomologicalComplex, Category.assoc] using hAug
  have hβ : (refinementComplexIntNat f).app G ≫ rV.β = rU.β ≫ refinementTotalMap f J := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    rw [HomologicalComplex.comp_f, rV.β_f, HomologicalComplex.comp_f, rU.β_f]
    dsimp only [refinementTotalMap, refinementBicomplexMap]
    simp only [Category.assoc, HomologicalComplex₂.ιTotal_map]
    have hn := congrArg (fun η ↦ HomologicalComplex.Hom.f η n)
      ((refinementComplexIntNat f).naturality
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ J.ι'.f 0))
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at hn
    have hηJ :
        ((NatTrans.mapHomologicalComplex (refinementComplexIntNat f)
          (ComplexShape.up ℤ)).app J.cochainComplex).f 0 =
        (refinementComplexIntNat f).app (J.cochainComplex.X 0) := rfl
    rw [hηJ]
    simpa only [Functor.comp_map, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex, Category.assoc] using congrArg
      (fun h ↦ h ≫ (CechSite.cechBicomplex.{v} (Opens.grothendieckTopology X) (hypercover V)
        J.cochainComplex).ιTotal (ComplexShape.up ℤ) 0 n n (by simp)) hn.symm
  have hIso : DerivedCategory.Q.map (refinementTotalMap f J) ≫ rV.αIso.inv = rU.αIso.inv := by
    apply (cancel_epi rU.αIso.hom).mp
    calc _ = (rU.αIso.hom ≫ DerivedCategory.Q.map (refinementTotalMap f J)) ≫
          rV.αIso.inv := by rw [← Category.assoc]
      _ = (DerivedCategory.Q.map rU.α ≫
          DerivedCategory.Q.map (refinementTotalMap f J)) ≫ rV.αIso.inv := by rw [rU.αIso_hom]
      _ = DerivedCategory.Q.map rV.α ≫ rV.αIso.inv := by
        rw [← DerivedCategory.Q.map_comp, hα]
      _ = rV.αIso.hom ≫ rV.αIso.inv := by rw [← rV.αIso_hom]
      _ = _ := by simp
  have hβQ : DerivedCategory.Q.map ((refinementComplexIntNat f).app G) ≫
      DerivedCategory.Q.map rV.β =
      DerivedCategory.Q.map rU.β ≫ DerivedCategory.Q.map (refinementTotalMap f J) := by
    simpa only [DerivedCategory.Q.map_comp] using congrArg DerivedCategory.Q.map hβ
  have hmain : DerivedCategory.Q.map ((refinementComplexIntNat f).app G) ≫
        DerivedCategory.Q.map rV.β ≫ rV.αIso.inv ≫
          J.toRightDerived ((sheafSections (Opens.grothendieckTopology X)
            AddCommGrpCat.{max u v}).obj (op (⊤ : Opens X))) =
      DerivedCategory.Q.map rU.β ≫ rU.αIso.inv ≫
        J.toRightDerived ((sheafSections (Opens.grothendieckTopology X)
          AddCommGrpCat.{max u v}).obj (op (⊤ : Opens X))) := by
    calc _ = (DerivedCategory.Q.map ((refinementComplexIntNat f).app G) ≫
          DerivedCategory.Q.map rV.β) ≫ rV.αIso.inv ≫
            J.toRightDerived _ := by rw [← Category.assoc]
      _ = (DerivedCategory.Q.map rU.β ≫
          DerivedCategory.Q.map (refinementTotalMap f J)) ≫ rV.αIso.inv ≫
            J.toRightDerived _ := by rw [hβQ]
      _ = DerivedCategory.Q.map rU.β ≫ rU.αIso.inv ≫ J.toRightDerived _ := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ DerivedCategory.Q.map rU.β ≫ k ≫ J.toRightDerived _) hIso
  rw [rU.comparison, rV.comparison]
  exact hmain

variable (G) (p : ℤ)

/-- **Stacks Project, Tag 09UZ.** Čech cohomology of an abelian sheaf in a fixed degree, as a
functor of the open covering: a refinement acts through the induced map of Čech complexes. -/
@[stacks 09UZ "the diagram of Čech cohomology over refinements"]
def cechDiagram : OpenCoverSet X ⥤ AddCommGrpCat.{max u v} where
  obj U := (CechSite.cechDerivedFunctor.{v} (Opens.grothendieckTopology X) (hypercover U) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v} p).obj G
  map f := (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v} p).map
    (DerivedCategory.Plus.Q.map (refinementPlusMap f G))
  map_id U := (congrArg (fun k ↦ (DerivedCategory.Plus.homologyFunctor
        AddCommGrpCat.{max u v} p).map (DerivedCategory.Plus.Q.map k))
      (refinementPlusMap_id U G)).trans
    ((congrArg (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v} p).map
      (DerivedCategory.Plus.Q.map_id _)).trans
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v} p).map_id _))
  map_comp f g := (congrArg (fun k ↦ (DerivedCategory.Plus.homologyFunctor
        AddCommGrpCat.{max u v} p).map (DerivedCategory.Plus.Q.map k))
      (refinementPlusMap_comp f g G).symm).trans
    ((congrArg (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v} p).map
      (DerivedCategory.Plus.Q.map_comp _ _)).trans
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v} p).map_comp _ _))

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- The fixed-covering comparisons of Stacks 03AX form a cocone on the Čech-cohomology
diagram: they are unchanged by passing to a refinement. -/
theorem cechDiagram_map_comp_cechCohomologyToCohomology {U V : OpenCoverSet X} (f : U ⟶ V) :
    (cechDiagram G p).map f ≫
        (CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X) (hypercover V)
          (hypercover_mem_grothendieckTopology V) p).app G =
      (CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X) (hypercover U)
        (hypercover_mem_grothendieckTopology U) p).app G := by
  have h := congrArg (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).map
    (cechToDerivedSections_refinement f (InjectiveResolution.of G))
  exact (((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).map_comp
    (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map (refinementPlusMap f G)))
    ((CechSite.cechToDerivedSections.{v} (Opens.grothendieckTopology X) (hypercover V)
      (hypercover_mem_grothendieckTopology V)).app G).hom).symm).trans h

/-- The cocone on the Čech-cohomology diagram given by the fixed-covering comparisons of
Stacks 03AX. -/
def cechCohomologyCocone : Limits.Cocone (cechDiagram G p) where
  pt := (CechSite.derivedSectionsFunctor.{max u v} (Opens.grothendieckTopology X)
      (⊤ : Opens X) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v} p).obj G
  ι :=
    { app := fun U ↦ (CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X)
        (hypercover U) (hypercover_mem_grothendieckTopology U) p).app G
      naturality := fun _ _ f ↦
        (cechDiagram_map_comp_cechCohomologyToCohomology G p f).trans
          (Category.comp_id _).symm }

/-- **Stacks Project, Tag 09UZ.** The canonical comparison from the Čech cohomology of a
topological space — the colimit, over all open coverings, of the Čech cohomology of the
covering — to sheaf cohomology. -/
@[stacks 09UZ "the comparison from the colimit"]
def colimitToCohomology :
    colimit (cechDiagram G p) ⟶
      (CechSite.derivedSectionsFunctor.{max u v} (Opens.grothendieckTopology X)
          (⊤ : Opens X) ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v} p).obj G :=
  colimit.desc _ (cechCohomologyCocone G p)

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- **Stacks Project, Tag 09UZ.** On each open covering, the comparison out of the colimit
restricts to the fixed-covering comparison of Stacks 03AX. -/
@[stacks 09UZ "compatibility with the fixed-covering comparison"]
theorem ι_colimitToCohomology (U : OpenCoverSet X) :
    colimit.ι (cechDiagram G p) U ≫ colimitToCohomology G p =
      (CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X) (hypercover U)
        (hypercover_mem_grothendieckTopology U) p).app G :=
  colimit.ι_desc (cechCohomologyCocone G p) U

end Comparison

section Ulift

/-- An abelian sheaf whose values lie in a universe smaller than the one of the space, with its
values raised so that the products over an open covering and the colimit over all open
coverings can be formed. -/
def uliftSheaf (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} :=
  (sheafCompose (Opens.grothendieckTopology X) AddCommGrpCat.uliftFunctor.{u, v}).obj F

end Ulift

end Stacks.Cohomology.CechRefinement

end
