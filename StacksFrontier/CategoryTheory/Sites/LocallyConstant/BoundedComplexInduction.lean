module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexes
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantSheafLocalChainMaps
public import StacksFrontier.CategoryTheory.Triangulated.Elementary

/-!
# Complexes with locally constant cohomology sheaves: the general case of Tag 094G

Let `(C, J)` be a site and `Λ` a Noetherian commutative ring. Stacks Tag 094G asserts that an
object `K` of `D^b(C, Λ)` whose cohomology sheaves are locally constant sheaves of `Λ`-modules
of finite type is, locally on the site, represented by a bounded complex of locally constant
sheaves of `Λ`-modules of finite type.

`StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexes` proves the base case of the
source's induction, namely the case of at most one nonzero cohomology sheaf. This file carries
out the induction on the length `b - a` of the interval containing the nonzero cohomology
sheaves and so proves the general statement.

## Main results

* `Stacks.ConstantSheaf.exists_cover_isRepresentedByLocallyConstantComplex_of_isGE_of_isLE`:
  **Tag 094G in general**, in the house form of
  `Stacks.ConstantSheaf.IsRepresentedByLocallyConstantComplex`.
* `Stacks.ConstantSheaf.exists_cover_constantComplex_representation`: the same conclusion for an
  object of `DerivedCategory.Bounded`, with the representing complex and the bounds produced
  rather than given, and with the local models exhibited as *constant* sheaf complexes.

## Implementation notes

**The shape of the induction.** The statement proved by induction on the amplitude is
`Stacks.ConstantSheaf.HasLocalModelUpToAmplitude`. It quantifies over sites whose object type is
`Type (max u v)`, which is the shape that is stable under slicing: the objects of `C/U` live in
`Type (max u v)` whatever the object universe of `C`, so the induction step, which passes to a
slice site, stays inside the statement being proved. The conclusion is transported to a site with
an arbitrary object universe by `Stacks.ConstantSheaf.hasLocalConstantComplexModel_of_le`, which
takes the one-element covering `{𝟙 X}` of `X` and applies the induction on the slice site `C/X`.

**The module universe.** `Λ` lives in `Type w` and modules in `Type (max u v w)`. Unlike the
base case, the induction needs the finite free module `Λ^{⊕n}` to be an *object* of the module
category, and a finite free `Λ`-module has `Λ` itself as a summand; so the module universe has to
dominate the universe of `Λ`. Taking `Λ : Type w` with modules at `max u v w` is the general
instance of `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf` in which that holds,
and `Stacks.ConstantSheaf.freeMod` is the resulting object.

## References

* [Stacks Project, Tag 094G](https://stacks.math.columbia.edu/tag/094G)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 093N](https://stacks.math.columbia.edu/tag/093N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace Stacks.ConstantSheaf

universe v u w m

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] constantSheaf Functor.sheafPushforwardContinuous
  HomologicalComplex.homologyFunctor HomologicalComplex.homology
  ShortComplex.LeftHomologyData.map

attribute [local instance] overPullback_preservesFiniteLimits
  overPullback_preservesFiniteColimits overPullback_preservesZeroMorphisms overPullback_additive
private noncomputable def constantComplexOverIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    (U : C) [HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (P : CochainComplex (ModuleCat.{max u v w} Λ) ℤ) :
    ((constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).mapHomologicalComplex (.up ℤ)).obj P ≅
      ((J.overPullback (ModuleCat.{max u v w} Λ) U).mapHomologicalComplex (.up ℤ)).obj
        (((constantSheaf J (ModuleCat.{max u v w} Λ)).mapHomologicalComplex (.up ℤ)).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => constantSheafOverIso J U (P.X n))
    (fun i j _ => (constantSheafOverIso_naturality J U (P.d i j)).symm)

private abbrev HasConstantComplexModel
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (a b : ℤ) : Prop :=
  ∃ P : CochainComplex (ModuleCat.{max u v w} Λ) ℤ,
    (∀ n, n ∉ Set.Icc a b → IsZero (P.X n)) ∧
    (∀ n, ModuleCat.isFG Λ (P.X n)) ∧
    Nonempty (DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj
      (((constantSheaf J (ModuleCat.{max u v w} Λ)).mapHomologicalComplex (.up ℤ)).obj P))

private abbrev HasLocalConstantComplexModel
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (a b : ℤ) (X : C) : Prop :=
  ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
    Sieve.ofArrows U f ∈ J X ∧ ∀ i,
      HasConstantComplexModel (J.over (U i))
        (((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).mapHomologicalComplex (.up ℤ)).obj T) a b

/-- An isomorphism in the derived category between two complexes is carried by an exact functor
to an isomorphism between their images. -/
private noncomputable def mapQObjIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {T T' : CochainComplex A ℤ} (e : DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj T') :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj T') :=
  (F.mapDerivedCategoryFactors.app T).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫
    F.mapDerivedCategoryFactors.app T'

/-- Finite-type local constancy of the cohomology sheaves transfers along an isomorphism in the
derived category from an object to a complex. -/
private lemma finiteTypeLocallyConstant_homology_of_iso_Q
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    {K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))}
    {T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ} (e : K ≅ DerivedCategory.Q.obj T)
    (hK : ∀ q : ℤ, IsFiniteTypeLocallyConstantModuleSheaf J Λ
      ((DerivedCategory.homologyFunctor _ q).obj K)) (q : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf J Λ (T.homology q) :=
  finiteTypeLocallyConstant_of_iso J Λ
    ((DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app T) (hK q)

private lemma hasConstantComplexModel_of_iteratedSlice
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (a b : ℤ)
    (U : C) (V : Over U)
    (h : HasConstantComplexModel ((J.over U).over V)
      ((((J.over U).overPullback (ModuleCat.{max u v w} Λ) V).mapHomologicalComplex (.up ℤ)).obj
        (((J.overPullback (ModuleCat.{max u v w} Λ) U).mapHomologicalComplex (.up ℤ)).obj T)) a b) :
    HasConstantComplexModel (J.over V.left)
      (((J.overPullback (ModuleCat.{max u v w} Λ) V.left).mapHomologicalComplex
        (.up ℤ)).obj T) a b := by
  obtain ⟨P, hP, hfg, ⟨e⟩⟩ := h
  let G := V.iteratedSliceBackward
  let F := G.sheafPushforwardContinuous (ModuleCat.{max u v w} Λ)
    (J.over V.left) ((J.over U).over V)
  have : F.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits F := by
    have : PreservesFiniteLimits
        (F ⋙ sheafToPresheaf (J.over V.left) (ModuleCat.{max u v w} Λ)) := by
      change PreservesFiniteLimits
        (sheafToPresheaf ((J.over U).over V) (ModuleCat.{max u v w} Λ) ⋙
          (Functor.whiskeringLeft _ _ _).obj G.op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _
      (sheafToPresheaf (J.over V.left) (ModuleCat.{max u v w} Λ))
  have : PreservesFiniteColimits F := by
    have : PreservesColimitsOfSize.{0, 0} F :=
      (G.sheafAdjunctionCocontinuous (ModuleCat.{max u v w} Λ)
        (J.over V.left) ((J.over U).over V)).leftAdjoint_preservesColimits
    infer_instance
  let eP : ((constantSheaf (J.over V.left) (ModuleCat.{max u v w} Λ)).mapHomologicalComplex
      (.up ℤ)).obj P ≅ (F.mapHomologicalComplex (.up ℤ)).obj
        (((constantSheaf ((J.over U).over V) (ModuleCat.{max u v w} Λ)).mapHomologicalComplex
          (.up ℤ)).obj P) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => constantSheafContinuousIso _ _ G (P.X n)) (fun i j _ =>
        ((G.pushforwardContinuousSheafificationCompatibility (ModuleCat.{max u v w} Λ)
          (J.over V.left) ((J.over U).over V)).hom.naturality
            ((Functor.const _).map (P.d i j))).symm)
  refine ⟨P, hP, hfg, ⟨?_⟩⟩
  exact mapQObjIso F e ≪≫ DerivedCategory.Q.mapIso eP.symm

private lemma hasLocalConstantComplexModel_of_cover
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (a b : ℤ)
    {X : C} {I : Type (max u v)} (U : I → C) (f : ∀ i, U i ⟶ X)
    (hf : Sieve.ofArrows U f ∈ J X)
    (h : ∀ i, HasLocalConstantComplexModel (J.over (U i))
      (((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).mapHomologicalComplex (.up ℤ)).obj T)
      a b (Over.mk (𝟙 (U i)))) :
    HasLocalConstantComplexModel J T a b X := by
  choose A V g hg hV using h
  have hcov (i : I) : Sieve.ofArrows (fun j => (V i j).left)
      (fun j => (g i j).left) ∈ J (U i) := by
    have hh := (J.mem_over_iff _).mp (hg i)
    rwa [Sieve.overEquiv_ofArrows] at hh
  exact ⟨Σ i, A i, (fun p => (V p.1 p.2).left), (fun p => (g p.1 p.2).left ≫ f p.1),
    covering_ofArrows_comp J U f hf _ _ hcov,
    fun p => hasConstantComplexModel_of_iteratedSlice J T a b (U p.1) (V p.1 p.2) (hV p.1 p.2)⟩

private lemma hasLocalConstantComplexModel_of_iso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    {T T' : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ} (a b : ℤ) (X : C)
    (e : DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj T')
    (h : HasLocalConstantComplexModel J T' a b X) :
    HasLocalConstantComplexModel J T a b X := by
  obtain ⟨I, U, f, hf, h⟩ := h
  refine ⟨I, U, f, hf, fun i => ?_⟩
  obtain ⟨P, hP, hfg, ⟨eP⟩⟩ := h i
  exact ⟨P, hP, hfg, ⟨mapQObjIso (J.overPullback (ModuleCat.{max u v w} Λ) (U i)) e ≪≫ eP⟩⟩

private lemma covering_ofArrows_nonempty
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {X : C} {I : Type (max u v)} (U : I → C) (f : ∀ i, U i ⟶ X)
    (hf : Sieve.ofArrows U f ∈ J X) :
    Sieve.ofArrows (fun i : {i // ¬ (⊥ : Sieve (U i)) ∈ J (U i)} => U i.val)
      (fun i => f i.val) ∈ J X := by
  let S := Sieve.ofArrows
    (fun i : {i // ¬ (⊥ : Sieve (U i)) ∈ J (U i)} => U i.val) (fun i => f i.val)
  apply J.transitive hf
  intro Y k hk
  rcases hk with ⟨Z, l, _, ⟨i⟩, rfl⟩
  have hi : S.pullback (f i) ∈ J (U i) := by
    by_cases h : (⊥ : Sieve (U i)) ∈ J (U i)
    · exact J.superset_covering bot_le h
    · apply J.superset_covering _ (J.top_mem (U i))
      intro V g _
      exact S.downward_closed (Sieve.ofArrows_mk _ _ ⟨i, h⟩) g
  simpa only [Sieve.pullback_comp] using J.pullback_stable l hi

private lemma constantSheaf_map_injective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    (X : C) (hX : ¬ (⊥ : Sieve X) ∈ J X)
    {A B : ModuleCat.{max u v w} Λ} {f g : A ⟶ B}
    (h : (constantSheaf J (ModuleCat.{max u v w} Λ)).map f =
      (constantSheaf J (ModuleCat.{max u v w} Λ)).map g) : f = g := by
  have hsec : f ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op X) =
      g ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op X) := by
    rw [constantSheaf_unit_naturality J f X, constantSheaf_unit_naturality J g X, h]
  ext x
  obtain ⟨I, U, k, hk, heq⟩ := exists_cover_eq_constant_sections J B X (f x) (g x)
    (congrArg (fun z => z x) hsec)
  by_contra hx
  apply hX
  apply J.superset_covering _ hk
  rintro V k ⟨W, l, _, ⟨i⟩, _⟩
  exact (hx (heq i)).elim

private noncomputable def isoMappingCoconeOfDistinguished
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q)
    (eP : T.obj₂ ≅ DerivedCategory.Q.obj P)
    (eQ : T.obj₃ ≅ DerivedCategory.Q.obj Q)
    (h : T.mor₂ ≫ eQ.hom = eP.hom ≫ DerivedCategory.Q.map f) :
    T.obj₁ ≅ DerivedCategory.Q.obj (CochainComplex.mappingCocone f) := by
  let S := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle f)
  let e := isoTriangleOfIso₁₂ T.rotate S.rotate (rot_of_distTriang _ hT)
    (rot_of_distTriang _ (DerivedCategory.mappingCocone_triangle_distinguished f)) eP eQ h
  exact (shiftFunctor (DerivedCategory A) (1 : ℤ)).preimageIso (Triangle.π₃.mapIso e)

private lemma exists_cover_constant_chainMap_to_single
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (P : CochainComplex (ModuleCat.{max u v w} Λ) ℤ) (b : ℤ)
    (E : ModuleCat.{max u v w} Λ) (hP : ModuleCat.isFG Λ (P.X b))
    (φ : ((constantSheaf J (ModuleCat.{max u v w} Λ)).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((constantSheaf J (ModuleCat.{max u v w} Λ)).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor _ b).obj E)) (X : C) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i,
        ∃ g : P ⟶ (CochainComplex.singleFunctor _ b).obj E,
          ((constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).mapHomologicalComplex
            (.up ℤ)).map g ≫
              (constantComplexOverIso J (U i) ((CochainComplex.singleFunctor _ b).obj E)).hom =
            (constantComplexOverIso J (U i) P).hom ≫
              ((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).mapHomologicalComplex
                (.up ℤ)).map φ := by
  let S := (CochainComplex.singleFunctor (ModuleCat.{max u v w} Λ) b).obj E
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) b E
  let c := constantSheaf J (ModuleCat.{max u v w} Λ)
  let φb : c.obj (P.X b) ⟶ c.obj E := φ.f b ≫ c.map e.hom
  obtain ⟨I, U, f, hf, ht⟩ := exists_cover_fixed_constant_map J (P.X b) E hP φb X
  refine ⟨{i // ¬ (⊥ : Sieve (U i)) ∈ J (U i)}, (fun i => U i.val),
    (fun i => f i.val), covering_ofArrows_nonempty J U f hf, ?_⟩
  rintro ⟨i, hi⟩
  obtain ⟨t, ht⟩ := ht i
  let F := J.overPullback (ModuleCat.{max u v w} Λ) (U i)
  let c' := constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)
  have hi' : ¬ (⊥ : Sieve (Over.mk (𝟙 (U i)))) ∈ (J.over (U i)) (Over.mk (𝟙 (U i))) := by
    intro h
    apply hi
    have hh := (J.mem_over_iff _).mp h
    rwa [map_bot] at hh
  have hdt (j : ℤ) (_ : (ComplexShape.up ℤ).Rel j b) : P.d j b ≫ t = 0 := by
    apply constantSheaf_map_injective (J.over (U i)) (Over.mk (𝟙 (U i))) hi'
    rw [Functor.map_zero, Functor.map_comp]
    apply (cancel_mono (constantSheafOverIso J (U i) E).hom).mp
    rw [zero_comp, Category.assoc, ht,
      ← Category.assoc, constantSheafOverIso_naturality, Category.assoc,
      ← F.map_comp]
    have hz : c.map (P.d j b) ≫ φb = 0 := by
      have hh := φ.comm j b
      change φ.f j ≫ c.map (S.d j b) = c.map (P.d j b) ≫ φ.f b at hh
      dsimp [φb]
      rw [← Category.assoc, ← hh]
      simp [S, CochainComplex.singleFunctor]
    rw [hz, F.map_zero, comp_zero]
  let g : P ⟶ S := HomologicalComplex.mkHomToSingle t hdt
  refine ⟨g, ?_⟩
  ext q : 1
  by_cases hq : q = b
  · subst q
    have hgb : g.f b = t ≫ e.inv := HomologicalComplex.mkHomToSingle_f t hdt
    have hnat : c'.map e.hom ≫ (constantSheafOverIso J (U i) E).hom =
        (constantSheafOverIso J (U i) (S.X b)).hom ≫ F.map (c.map e.hom) :=
      constantSheafOverIso_naturality J (U i) e.hom
    change c'.map (g.f b) ≫ (constantSheafOverIso J (U i) (S.X b)).hom =
      (constantSheafOverIso J (U i) (P.X b)).hom ≫ F.map (φ.f b)
    apply (cancel_mono (F.map (c.map e.hom))).mp
    rw [hgb, c'.map_comp]
    simp only [Category.assoc]
    rw [← hnat, ← Category.assoc (c'.map e.inv), ← c'.map_comp, e.inv_hom_id,
      c'.map_id, Category.id_comp]
    simpa only [Category.assoc, ← F.map_comp] using ht
  · exact (Functor.map_isZero F
      (Functor.map_isZero c (HomologicalComplex.isZero_single_obj_X (.up ℤ) b E q hq))).eq_of_tgt
      _ _

/-- A constant model of a complex restricts to a constant model of its
restriction to a slice site. -/
private lemma hasConstantComplexModel_over
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (a b : ℤ) (U : C)
    (h : HasConstantComplexModel J T a b) :
    HasConstantComplexModel (J.over U)
      (((J.overPullback (ModuleCat.{max u v w} Λ) U).mapHomologicalComplex (.up ℤ)).obj T) a b := by
  obtain ⟨P, hP, hfg, ⟨e⟩⟩ := h
  exact ⟨P, hP, hfg, ⟨mapQObjIso (J.overPullback (ModuleCat.{max u v w} Λ) U) e ≪≫
    DerivedCategory.Q.mapIso (constantComplexOverIso J U P).symm⟩⟩

/-- A constant model is in particular a local constant model, on the trivial
covering of any object. -/
private lemma hasLocalConstantComplexModel_of_global
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (a b : ℤ) (X : C)
    (h : HasConstantComplexModel J T a b) :
    HasLocalConstantComplexModel J T a b X := by
  refine ⟨PUnit, fun _ => X, fun _ => 𝟙 X, ?_,
    fun _ => hasConstantComplexModel_over J T a b X h⟩
  apply J.superset_covering _ (J.top_mem X)
  intro Y f _
  simpa using (Sieve.ofArrows (fun _ : PUnit => X) (fun _ => 𝟙 X)).downward_closed
    (Sieve.ofArrows_mk _ _ PUnit.unit) f

/-- A complex concentrated in a single degree has a local constant model of
amplitude zero: this is the base of the induction on the amplitude. -/
private lemma hasLocalConstantComplexModel_of_single_degree
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (b : ℤ)
    [T.IsStrictlyGE b] [T.IsStrictlyLE b]
    (hT : IsFiniteTypeLocallyConstantModuleSheaf J Λ (T.homology b)) (X : C) :
    HasLocalConstantComplexModel J T b b X :=
  exists_cover_constantComplex_model_of_isGE_of_isLE J Λ X T b hT

/-- The statement proved by induction on the cohomological amplitude `b - a`: on
any site, a complex of module sheaves which is strictly supported in `[a, b]`
and whose cohomology sheaves are locally constant of finite type has, locally on
the site, a model by the constant sheaf complex of a bounded complex of
finite-type modules. -/
private abbrev HasLocalModelUpToAmplitude (m : ℕ) : Prop :=
  ∀ {C : Type (max u v)} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (a b : ℤ),
    a ≤ b → b - a ≤ (m : ℤ) → T.IsStrictlyGE a → T.IsStrictlyLE b →
    (∀ q, IsFiniteTypeLocallyConstantModuleSheaf J Λ (T.homology q)) →
    ∀ X : C, HasLocalConstantComplexModel J T a b X

/-- Restricting a constant sheaf placed in degree `b` to a slice site and shifting by one is the
constant sheaf placed in degree `b - 1`. -/
private noncomputable def singleOverShiftIso
    {C : Type (max u v)} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (U : C) (b : ℤ) (N : ModuleCat.{max u v w} Λ) :
    (DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{max u v w} Λ) U).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor (Sheaf J (ModuleCat.{max u v w} Λ)) b).obj
            ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj N))))⟦(1 : ℤ)⟧ ≅
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Sheaf (J.over U) (ModuleCat.{max u v w} Λ)) (b - 1)).obj
          ((constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).obj N)) :=
  (shiftFunctor (DerivedCategory (Sheaf (J.over U) (ModuleCat.{max u v w} Λ))) (1 : ℤ)).mapIso
      (DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
            (J.overPullback (ModuleCat.{max u v w} Λ) U) (.up ℤ) b).app
            ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj N) ≪≫
          (CochainComplex.singleFunctor _ b).mapIso (constantSheafOverIso J U N).symm)) ≪≫
    ((DerivedCategory.singleFunctors (Sheaf (J.over U) (ModuleCat.{max u v w} Λ))).shiftIso
      1 (b - 1) b (by omega)).app ((constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).obj N)

/-- If the mapping cone of `α` restricted to a slice site is modelled by a constant complex `P`,
then the restriction of the target of `α` is the mapping cocone of a chain map from `P` to a
constant free module in degree `b - 1`. -/
private lemma exists_iso_mappingCocone_of_mappingCone
    {C : Type (max u v)} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (b : ℤ) (n : ℕ)
    (α : (CochainComplex.singleFunctor (Sheaf J (ModuleCat.{max u v w} Λ)) b).obj
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj (freeMod.{v, u, w} Λ n)) ⟶ T)
    (U : C) (P : CochainComplex (ModuleCat.{max u v w} Λ) ℤ) [P.IsStrictlyLE (b - 1)]
    (ePcone : DerivedCategory.Q.obj (CochainComplex.mappingCone
        (((J.overPullback (ModuleCat.{max u v w} Λ) U).mapHomologicalComplex (.up ℤ)).map α)) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).mapHomologicalComplex
          (.up ℤ)).obj P)) :
    ∃ φ : ((constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).mapHomologicalComplex
          (.up ℤ)).obj P ⟶
        ((constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor (ModuleCat.{max u v w} Λ) (b - 1)).obj
            (freeMod.{v, u, w} Λ n)),
      Nonempty (DerivedCategory.Q.obj
          (((J.overPullback (ModuleCat.{max u v w} Λ) U).mapHomologicalComplex (.up ℤ)).obj T) ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCocone φ)) := by
  let G := J.overPullback (ModuleCat.{max u v w} Λ) U
  let cJ := constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)
  let N := freeMod.{v, u, w} Λ n
  let α' := (G.mapHomologicalComplex (.up ℤ)).map α
  have hdist := DerivedCategory.mappingCone_triangle_distinguished α'
  let eQ' := singleOverShiftIso.{v, u, w} J U b N
  let σ : (cJ.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{max u v w} Λ) (b - 1)).obj N) ≅
      (CochainComplex.singleFunctor (Sheaf (J.over U) (ModuleCat.{max u v w} Λ)) (b - 1)).obj
        (cJ.obj N) :=
    (HomologicalComplex.singleMapHomologicalComplex cJ (.up ℤ) (b - 1)).app N
  let γ : DerivedCategory.Q.obj (CochainComplex.mappingCone α') ⟶
      (DerivedCategory.Q.obj
        ((G.mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor (Sheaf J (ModuleCat.{max u v w} Λ)) b).obj
            ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj N))))⟦(1 : ℤ)⟧ :=
    (DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle α')).rotate.mor₂
  obtain ⟨φ', hφ'⟩ := exists_chainMap_to_single_of_derived
    ((cJ.mapHomologicalComplex (.up ℤ)).obj P) (b - 1) (cJ.obj N)
    (ePcone.inv ≫ γ ≫ eQ'.hom)
  let φ := φ' ≫ σ.inv
  have hφ : DerivedCategory.Q.map φ =
      ePcone.inv ≫ γ ≫ eQ'.hom ≫ DerivedCategory.Q.map σ.inv := by
    change DerivedCategory.Q.map (φ' ≫ σ.inv) = _
    rw [DerivedCategory.Q.map_comp, hφ', Category.assoc, Category.assoc]
  exact ⟨φ, ⟨isoMappingCoconeOfDistinguished
    (DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle α')).rotate
    (rot_of_distTriang _ hdist) φ ePcone (eQ' ≪≫ DerivedCategory.Q.mapIso σ.symm)
    (by
      change γ ≫ (eQ' ≪≫ DerivedCategory.Q.mapIso σ.symm).hom =
        ePcone.hom ≫ DerivedCategory.Q.map φ
      rw [hφ]
      simp)⟩⟩

/-- A complex isomorphic in the derived category to the mapping cocone of a chain map from a
constant complex to a constant free module in degree `b - 1` has a local constant model. -/
private lemma hasLocalConstantComplexModel_of_iso_mappingCocone
    {C : Type (max u v)} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (a b : ℤ) (hab : a ≤ b)
    (P : CochainComplex (ModuleCat.{max u v w} Λ) ℤ)
    (hP : ∀ k, k ∉ Set.Icc a (b - 1) → IsZero (P.X k))
    (hPfg : ∀ k, ModuleCat.isFG Λ (P.X k)) (n : ℕ)
    (φ : ((constantSheaf J (ModuleCat.{max u v w} Λ)).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((constantSheaf J (ModuleCat.{max u v w} Λ)).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{max u v w} Λ) (b - 1)).obj
          (freeMod.{v, u, w} Λ n)))
    (Θ : DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj (CochainComplex.mappingCocone φ))
    (X : C) :
    HasLocalConstantComplexModel J T a b X := by
  let N := freeMod.{v, u, w} Λ n
  obtain ⟨I₂, W, k, hcov₂, hgcover⟩ :=
    exists_cover_constant_chainMap_to_single J P (b - 1) N (hPfg (b - 1)) φ X
  refine hasLocalConstantComplexModel_of_cover.{v, max u v, w} J _ a b W k hcov₂ (fun j => ?_)
  obtain ⟨gmod, hgmod⟩ := hgcover j
  refine hasLocalConstantComplexModel_of_global _ _ a b _ ?_
  let G' := J.overPullback (ModuleCat.{max u v w} Λ) (W j)
  let cJ' := constantSheaf (J.over (W j)) (ModuleCat.{max u v w} Λ)
  obtain ⟨hzero, hfg⟩ :=
    mappingCocone_single_finite_bounded a b hab hP hPfg N (isFG_freeMod.{v, u, w} Λ n) gmod
  refine ⟨CochainComplex.mappingCocone gmod, hzero, hfg, ⟨?_⟩⟩
  have hchain : (G'.mapHomologicalComplex (.up ℤ)).map φ ≫
      (constantComplexOverIso J (W j)
        ((CochainComplex.singleFunctor (ModuleCat.{max u v w} Λ) (b - 1)).obj N)).inv =
      (constantComplexOverIso J (W j) P).inv ≫
        (cJ'.mapHomologicalComplex (.up ℤ)).map gmod := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hgmod, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  let eMid := isoMappingCoconeOfDistinguished
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle
      ((G'.mapHomologicalComplex (.up ℤ)).map φ)))
    (DerivedCategory.mappingCocone_triangle_distinguished _)
    ((cJ'.mapHomologicalComplex (.up ℤ)).map gmod)
    (DerivedCategory.Q.mapIso (constantComplexOverIso J (W j) P).symm)
    (DerivedCategory.Q.mapIso (constantComplexOverIso J (W j)
      ((CochainComplex.singleFunctor (ModuleCat.{max u v w} Λ) (b - 1)).obj N)).symm)
    (by
      have hQ := congrArg DerivedCategory.Q.map hchain
      rwa [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp] at hQ)
  exact mapQObjIso G' Θ ≪≫ DerivedCategory.Q.mapIso (mapMappingCoconeIso G' φ) ≪≫ eMid ≪≫
    DerivedCategory.Q.mapIso (mapMappingCoconeIso cJ' gmod).symm

/-- The inductive step of Tag 094G. Given a chain map `α` from a constant
finite free sheaf in degree `b` which is surjective on degree-`b` cohomology,
the mapping cone of `α` has amplitude one less, so the inductive hypothesis
gives it a constant model `P` locally on the site. Over a further covering the
connecting map `P → Λ^n[-b+1]` is induced by a homomorphism of modules `g`, and
the mapping cocone of `g` is the required model of `T`. -/
private lemma hasLocalConstantComplexModel_of_chainMap
    {C : Type (max u v)} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (a b : ℤ) (hab : a < b)
    [T.IsStrictlyGE a] [T.IsStrictlyLE b]
    (hT : ∀ q, IsFiniteTypeLocallyConstantModuleSheaf J Λ (T.homology q))
    (n : ℕ)
    (α : (CochainComplex.singleFunctor (Sheaf J (ModuleCat.{max u v w} Λ)) b).obj
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj (freeMod.{v, u, w} Λ n)) ⟶ T)
    [Epi (HomologicalComplex.homologyMap α b)]
    (m : ℕ) (ih : HasLocalModelUpToAmplitude.{v, u, w} m) (hm : b - 1 - a ≤ (m : ℤ)) (X : C) :
    HasLocalConstantComplexModel J T a b X := by
  have hTQ (q : ℤ) : IsFiniteTypeLocallyConstantModuleSheaf J Λ
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{max u v w} Λ)) q).obj
        (DerivedCategory.Q.obj T)) :=
    finiteTypeLocallyConstant_of_iso J Λ
      ((DerivedCategory.homologyFunctorFactors _ q).app T).symm (hT q)
  obtain ⟨hGEcone, hLEcone, hpropcone⟩ :=
    mappingCone_isGE_isLE_and_prop
      (fun F : Sheaf J (ModuleCat.{max u v w} Λ) => IsFiniteTypeLocallyConstantModuleSheaf J Λ F)
      T a b hab hTQ _ (finiteTypeLocallyConstant_constantSheaf.{v, max u v, w} J _
        (isFG_freeMod.{v, u, w} Λ n)) α
  let := hGEcone
  let := hLEcone
  obtain ⟨T', hT'GE, hT'LE, ⟨eCone⟩⟩ :=
    (DerivedCategory.Q.obj (CochainComplex.mappingCone α)).exists_iso_Q_obj_of_isGE_of_isLE
      a (b - 1)
  let := hT'GE
  let := hT'LE
  have hT' := finiteTypeLocallyConstant_homology_of_iso_Q J Λ eCone hpropcone
  obtain ⟨I, U, f, hcov, hmodel⟩ := ih J T' a (b - 1) (by omega) hm hT'GE hT'LE hT' X
  refine hasLocalConstantComplexModel_of_cover J T a b U f hcov (fun i => ?_)
  obtain ⟨P, hP, hPfg, ⟨eP₀⟩⟩ := hmodel i
  have : P.IsStrictlyLE (b - 1) :=
    (CochainComplex.isStrictlyLE_iff P (b - 1)).mpr
      (fun k hk => hP k (by simp only [Set.mem_Icc]; omega))
  let G := J.overPullback (ModuleCat.{max u v w} Λ) (U i)
  obtain ⟨φ, ⟨Θ⟩⟩ := exists_iso_mappingCocone_of_mappingCone.{v, u, w} J T b n α (U i) P
    (DerivedCategory.Q.mapIso
        (CochainComplex.mappingCone.mapHomologicalComplexIso α G).symm ≪≫
      (G.mapDerivedCategoryFactors.app (CochainComplex.mappingCone α)).symm ≪≫
      G.mapDerivedCategory.mapIso eCone ≪≫ G.mapDerivedCategoryFactors.app T' ≪≫ eP₀)
  exact hasLocalConstantComplexModel_of_iso_mappingCocone.{v, u, w} (J.over (U i)) _ a b hab.le
    P hP hPfg n φ Θ _

private lemma hasLocalModelUpToAmplitude_zero : HasLocalModelUpToAmplitude.{v, u, w} 0 := by
  intro C _ J Λ _ _ _ T a b hab hm hGE hLE hT X
  obtain rfl : a = b := by omega
  let := hGE
  let := hLE
  exact hasLocalConstantComplexModel_of_single_degree J T _ (hT _) X

private lemma hasLocalModelUpToAmplitude_succ (m : ℕ)
    (ih : HasLocalModelUpToAmplitude.{v, u, w} m) :
    HasLocalModelUpToAmplitude.{v, u, w} (m + 1) := by
  intro C _ J Λ _ _ _ T a b hab hm hGE hLE hT X
  let := hGE
  let := hLE
  rcases eq_or_lt_of_le hab with rfl | hab'
  · exact hasLocalConstantComplexModel_of_single_degree J T _ (hT _) X
  obtain ⟨I₀, U₀, f₀, hcov₀, hfree⟩ :=
    exists_cover_constantFree_epi_homology J Λ T b (hT b) X
  refine hasLocalConstantComplexModel_of_cover J T a b U₀ f₀ hcov₀ (fun i₀ => ?_)
  obtain ⟨n, g, hg⟩ := hfree i₀
  let := hg
  obtain ⟨I₁, U₁, f₁, hcov₁, hα⟩ :=
    exists_cover_homology_epi_of_constantFree_epi (J.over (U₀ i₀))
      (((J.overPullback (ModuleCat Λ) (U₀ i₀)).mapHomologicalComplex (.up ℤ)).obj T)
      b n g (Over.mk (𝟙 (U₀ i₀)))
  refine hasLocalConstantComplexModel_of_cover.{v, max u v, w} (J.over (U₀ i₀)) _ a b U₁ f₁
    hcov₁ (fun i₁ => ?_)
  obtain ⟨α, hαepi⟩ := hα i₁
  let := hαepi
  exact hasLocalConstantComplexModel_of_chainMap.{v, u, w} _ _ a b hab'
    (fun q => finiteTypeLocallyConstant_homology_over (J.over (U₀ i₀)) _ q
      (finiteTypeLocallyConstant_homology_over J T q (hT q) (U₀ i₀)) (U₁ i₁))
    n α m ih (by omega) (Over.mk (𝟙 (U₁ i₁)))

private lemma hasLocalModelUpToAmplitude (m : ℕ) : HasLocalModelUpToAmplitude.{v, u, w} m := by
  induction m with
  | zero => exact hasLocalModelUpToAmplitude_zero
  | succ m ih => exact hasLocalModelUpToAmplitude_succ m ih

/-- The induction of `Stacks.ConstantSheaf.hasLocalModelUpToAmplitude` quantifies over sites
whose object type is `Type (max u v)`, which is the shape that is stable under slicing: the
objects of `C/U` live in `Type (max u v)` whatever the object universe of `C`, so an induction
step that passes to a slice site stays inside the statement. This lemma transfers the conclusion
to a site with an arbitrary object universe, by taking the one-element covering `{𝟙 X}` of `X`
and applying the induction on the slice site `C/X`. -/
private lemma hasLocalConstantComplexModel_of_le
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] [IsNoetherianRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (a b : ℤ) (hab : a ≤ b)
    [T.IsStrictlyGE a] [T.IsStrictlyLE b]
    (hT : ∀ q, IsFiniteTypeLocallyConstantModuleSheaf J Λ (T.homology q)) (X : C) :
    HasLocalConstantComplexModel J T a b X := by
  refine hasLocalConstantComplexModel_of_cover J T a b
    (fun _ : PUnit.{max u v + 1} => X) (fun _ => 𝟙 X) ?_ (fun _ => ?_)
  · have h : Sieve.ofArrows (fun _ : PUnit.{max u v + 1} => X) (fun _ => 𝟙 X) = ⊤ :=
      Sieve.id_mem_iff_eq_top.mp (Sieve.ofArrows_mk _ _ PUnit.unit)
    rw [h]
    exact J.top_mem X
  · exact hasLocalModelUpToAmplitude.{v, u, w} (b - a).toNat (J.over X) _ a b hab
      (by omega) inferInstance inferInstance
      (fun q => finiteTypeLocallyConstant_homology_over J T q (hT q) X) (Over.mk (𝟙 X))

/-- An object of the bounded derived category of sheaves of `Λ`-modules whose cohomology sheaves
are locally constant of finite type is, over a covering family of any object of the site,
represented by a bounded complex of *constant* sheaves on finitely generated `Λ`-modules.

This is the same mathematics as
`Stacks.ConstantSheaf.exists_cover_isRepresentedByLocallyConstantComplex_of_isGE_of_isLE`,
packaged for an object of `DerivedCategory.Bounded`: the bounds and the complex representative
are produced rather than given, and the local models are exhibited as constant sheaf complexes,
which is more than the conclusion of Tag 094G asks. The tag sits on the house form rather than
here, so that the covering set of Tag 094G stays minimal. -/
public theorem exists_cover_constantComplex_representation
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] [IsNoetherianRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (X : C)
    (K : DerivedCategory.Bounded (Sheaf J (ModuleCat.{max u v w} Λ)))
    (hK : ∀ n : ℤ, IsFiniteTypeLocallyConstantModuleSheaf J Λ
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{max u v w} Λ)) n).obj K.obj)) :
    ∃ (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ),
      Nonempty (K.obj ≅ DerivedCategory.Q.obj T) ∧
      ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧
        ∀ i, ∃ (P : CochainComplex (ModuleCat.{max u v w} Λ) ℤ)
          (a b : ℤ),
          (∀ n, n ∉ Set.Icc a b → IsZero (P.X n)) ∧
          (∀ n, ModuleCat.isFG Λ (P.X n)) ∧
          Nonempty (DerivedCategory.Q.obj
            (((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj T) ≅
            DerivedCategory.Q.obj
              (((constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property
  let : K.obj.IsGE a := ha
  let : K.obj.IsLE b := hb
  by_cases hba : b ≤ a
  · have : K.obj.IsGE b := DerivedCategory.TStructure.t.isGE_of_ge K.obj b a hba
    obtain ⟨T, e, I, U, f, hcov, h⟩ :=
      exists_cover_constantComplex_representation_of_isGE_of_isLE J Λ X K.obj b (hK b)
    refine ⟨T, ⟨e⟩, I, U, f, hcov, fun i => ?_⟩
    obtain ⟨P, hP, hfg, eP⟩ := h i
    exact ⟨P, b, b, hP, hfg, eP⟩
  obtain ⟨T, hTa, hTb, ⟨e⟩⟩ := K.obj.exists_iso_Q_obj_of_isGE_of_isLE a b
  let := hTa
  let := hTb
  have hT := finiteTypeLocallyConstant_homology_of_iso_Q J Λ e hK
  obtain ⟨I, U, f, hcov, hmodel⟩ :=
    hasLocalConstantComplexModel_of_le J Λ T a b (not_le.mp hba).le hT X
  refine ⟨T, ⟨e⟩, I, U, f, hcov, fun i => ?_⟩
  obtain ⟨P, hP, hfg, eP⟩ := hmodel i
  exact ⟨P, a, b, hP, hfg, eP⟩

/-! ### Tag 094G, the general case -/

/-- **Stacks Tag 094G, the general case.** Let `K` be an object of the derived category of
sheaves of `Λ`-modules over a Noetherian ring whose cohomology is concentrated in the degrees
`[a, b]` and all of whose cohomology sheaves are locally constant of finite type. Then every
object `U` of the site has a covering family `V i ⟶ U` such that the restriction of `K` to each
slice site `C / V i` is represented by a complex of locally constant sheaves of `Λ`-modules of
finite type, concentrated in the degrees `[a, b]`.

This is the statement of the source for an arbitrary number of nonzero cohomology sheaves,
proved by the source's induction on `b - a`;
`Stacks.ConstantSheaf.exists_cover_isRepresentedByLocallyConstantComplex` is the base case
`a = b` of that induction. The complex produced here is in fact degreewise *constant* on each
member of the covering family, which is more than the conclusion records. -/
@[stacks 094G "the general case: the induction on the number of nonzero cohomology sheaves"]
public theorem exists_cover_isRepresentedByLocallyConstantComplex_of_isGE_of_isLE
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] [IsNoetherianRing Λ]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{max u v w} Λ)]
    (a b : ℤ) (hab : a ≤ b) (U : C)
    (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    [K.IsGE a] [K.IsLE b]
    (hK : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj K)) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ i : I,
        IsRepresentedByLocallyConstantComplex.{v, max u v, w} (J.over (V i)) Λ a b
          ((J.overPullback (ModuleCat.{max u v w} Λ) (V i)).mapDerivedCategory.obj K) := by
  obtain ⟨T, hTa, hTb, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isGE_of_isLE a b
  let := hTa
  let := hTb
  have hT := finiteTypeLocallyConstant_homology_of_iso_Q J Λ e hK
  obtain ⟨I, V, f, hcov, hmodel⟩ := hasLocalConstantComplexModel_of_le J Λ T a b hab hT U
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  obtain ⟨P, hP, hPfg, ⟨eP⟩⟩ := hmodel i
  set G := J.overPullback (ModuleCat.{max u v w} Λ) (V i) with hG
  set cJ := constantSheaf (J.over (V i)) (ModuleCat.{max u v w} Λ) with hcJ
  have hzero (k : ℤ) (hk : k ∉ Set.Icc a b) :
      IsZero ((cJ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P |>.X k) :=
    Functor.map_isZero cJ (hP k hk)
  refine ⟨(cJ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, ?_, ?_, ?_, ⟨?_⟩⟩
  · exact (CochainComplex.isStrictlyGE_iff _ a).mpr fun k hk =>
      hzero k (by simp only [Set.mem_Icc]; omega)
  · exact (CochainComplex.isStrictlyLE_iff _ b).mpr fun k hk =>
      hzero k (by simp only [Set.mem_Icc]; omega)
  · exact fun k =>
      finiteTypeLocallyConstant_constantSheaf.{v, max u v, w} (J.over (V i)) _ (hPfg k)
  · exact G.mapDerivedCategory.mapIso e ≪≫ G.mapDerivedCategoryFactors.app T ≪≫ eP

end Stacks.ConstantSheaf

end
