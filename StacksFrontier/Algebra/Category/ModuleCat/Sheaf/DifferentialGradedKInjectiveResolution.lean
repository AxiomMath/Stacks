module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import StacksCore.Algebra.Homology.QuasiIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAcyclicNullHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedGrothendieck
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveLifting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSetOfMonos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.Homology.Injectives.Size.SmallWithRespectToInjections

/-!
# Graded injective K-injective resolutions of differential graded modules

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. Every
right differential graded `A`-module admits a quasi-isomorphism into a module which is graded
injective and K-injective, and the resolution may be chosen functorially in the module. This is
proved here from a *set-indexed* family of acyclic monomorphisms detecting the graded injective
K-injective modules, which is carried as a hypothesis; see the implementation notes.

This is the small-object argument. Let `i r : Ms r ⟶ Ms' r` be a family of monomorphisms of
acyclic right differential graded modules with the property that a module into which every
`Ms r ⟶ I` extends along `i r` is K-injective and graded injective. Attaching all such
extensions in one step is a functor `F` together with a natural monomorphic quasi-isomorphism
`η : 𝟭 ⟶ F`; it is iterated transfinitely, through an ordinal `κ.ord` whose cofinality exceeds
the number of subobjects of each `Ms r`, and the colimit of the tower is the resolution. The
inclusion of the tower is a monomorphism and a quasi-isomorphism because both properties are
stable under transfinite composition, and the target has the extension property because a
morphism out of `Ms r` into the colimit factors through a stage of the tower, where the next
stage was built to extend it.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.GradedInjectiveKInjectiveResolution` packages a
  resolution functor, its natural inclusion, and the properties of the inclusion and of its
  values.

## Main results

* `SheafOfModules.DifferentialGradedModule.exists_gradedInjectiveKInjectiveResolution`
  constructs the functorial resolution from such a detecting family.
* `SheafOfModules.DifferentialGradedModule.exists_quasiIso_gradedInjective_isKInjective` is the
  resulting resolution of a single module: a quasi-isomorphism `M ⟶ I` with `I` graded
  injective and K-injective.

## Implementation notes

**Where the detecting family comes from.** The family `i r : Ms r ⟶ Ms' r` and its detection
property are parameters of both results below, with the index type `Idx` in the module
universe. They are the content of Tag 0FSY, and
`SheafOfModules.DifferentialGradedModule.exists_setIndexed_acyclic_monomorphisms_iff` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedKInjectiveExistence.lean`
produces one, which is how
`SheafOfModules.DifferentialGradedModule.nonempty_gradedInjectiveKInjectiveResolution` there
states Tag 0FT0 with no parameters left.

The index type has to be set-sized for this argument to run. The older
`exists_acyclic_monomorphisms_isKInjective_gradedInjective_iff` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedKInjectiveLifting.lean` is
indexed by a type *one universe above* the module universe, because it uses all nonzero acyclic
modules as test objects, and a family that large cannot drive the construction: the transfinite
tower is indexed by a single ordinal, and the factorization of a morphism out of a test object
through a stage of the tower needs the cofinality of that ordinal to exceed the number of
subobjects of the test object, which for a family indexed by a proper class of modules has no
uniform bound. The set-sized family instead rests on Tag 0FST's uniform size bound,
`SheafOfModules.DifferentialGradedModule.exists_small_acyclic_submodule`.

Only one direction of Tag 0FSY's equivalence is used: that the extension property implies
K-injectivity and graded injectivity.

**The transfinite tower.** The successor step is the attachment functor of Tag 0FSZ, and the
tower is Mathlib's `CategoryTheory.SmallObject.SuccStruct.iteration` of the natural
transformation `η`. Monomorphy of the inclusion of the tower is the stability of monomorphisms
under transfinite composition; the quasi-isomorphism property is the corresponding stability of
quasi-isomorphisms, which holds because the underlying cochain complex of a differential graded
module commutes with colimits — forgetting the differential is a left adjoint and taking a
homogeneous component commutes with colimits, Tag 0FR0 — and because filtered colimits of
sheaves of modules are exact, so that a filtered colimit of quasi-isomorphisms of complexes is
a quasi-isomorphism.

**The ordinal.** The successor of the supremum of the numbers of subobjects of the `Ms r` and
of `ℵ₀` is a regular cardinal `κ`, and the tower is indexed by `κ.ord.ToType`. The
factorization of a morphism out of `Ms r` through a stage is Tag 079F, applied to the tower,
whose transition maps are monomorphisms.

**The base and the universes.** The base is the structure sheaf of a ringed site, as for the
attachment functor of Tag 0FSZ, and the universes of the site and of the algebra pieces are
independent. The module universe is `max u v w`, which is where the category of right
differential graded modules is Grothendieck abelian (Tag 0FS9) and where it has colimits.

## References

* [Stacks Project, Tag 0FT0](https://stacks.math.columbia.edu/tag/0FT0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace SheafOfModules.DifferentialGradedModule

/-! ### Filtered colimits of quasi-isomorphisms of cochain complexes -/

section ComplexColimits

variable (B : Type*) [Category* B] [Abelian B]

/-- A diagram of cochain complexes read as a cochain complex of diagrams. -/
private def diagramComplex {J : Type*} [SmallCategory J]
    (D : J ⥤ CochainComplex B ℤ) : CochainComplex (J ⥤ B) ℤ where
  X n := D ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) n
  d n m :=
    { app := fun j => (D.obj j).d n m
      naturality := by
        intro i j f
        dsimp
        rw [← HomologicalComplex.Hom.comm (D.map f) n m] }
  shape := by
    intro n m h
    ext j
    exact (D.obj j).shape n m h

/-- A morphism of diagrams of cochain complexes read as a morphism of cochain complexes of
diagrams. -/
private def diagramComplexMap {J : Type*} [SmallCategory J]
    {D D' : J ⥤ CochainComplex B ℤ} (α : D ⟶ D') :
    diagramComplex B D ⟶ diagramComplex B D' where
  f n :=
    { app := fun j => (α.app j).f n
      naturality := by
        intro i j f
        exact congrArg (fun g => (HomologicalComplex.eval B (ComplexShape.up ℤ) n).map g)
          (α.naturality f) }
  comm' := by
    intro n m h
    ext j
    exact (α.app j).comm n m

/-- The cocone on a diagram of cochain complexes whose point is the degreewise colimit. -/
private abbrev diagramComplexCocone {J : Type*} [SmallCategory J] [HasColimitsOfShape J B]
    (D : J ⥤ CochainComplex B ℤ) : Cocone D where
  pt := ((colim (J := J) (C := B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (diagramComplex B D)
  ι :=
    { app := fun j =>
        { f := fun n => colimit.ι (D ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) n) j
          comm' := by
            intro n m h
            let δ : (D ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) n) ⟶
                (D ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) m) :=
              { app := fun j => (D.obj j).d n m
                naturality := by
                  intro i j f
                  simp }
            change colimit.ι (D ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) n) j ≫
              (colim (J := J) (C := B)).map δ =
              (D.obj j).d n m ≫
                colimit.ι (D ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) m) j
            simp [δ] }
      naturality := by
        intro i j f
        ext n
        simpa [Functor.comp_map, HomologicalComplex.eval_map, diagramComplex] using
          (colimit.w (D ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) n) f) }

/-- The degreewise colimit cocone on a diagram of cochain complexes is a colimit. -/
private def diagramComplexCoconeIsColimit {J : Type*} [SmallCategory J] [HasColimitsOfShape J B]
    (D : J ⥤ CochainComplex B ℤ) : IsColimit (diagramComplexCocone B D) :=
  HomologicalComplex.isColimitOfEval _ _ fun n =>
    colimit.isColimit (D ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) n)

/-- Being a quasi-isomorphism of the colimits of two diagrams of cochain complexes does not depend
on the chosen colimit cocones: it transfers between two maps induced by the same morphism of
diagrams. -/
private theorem quasiIso_of_isColimit_of_quasiIso {J : Type*} [SmallCategory J]
    {D D' : J ⥤ CochainComplex B ℤ} (α : D ⟶ D') {c d : Cocone D} {c' d' : Cocone D'}
    (hc : IsColimit c) (hd : IsColimit d) (hc' : IsColimit c') (hd' : IsColimit d')
    (φ : c.pt ⟶ c'.pt) (φ' : d.pt ⟶ d'.pt) (hφ : ∀ j, c.ι.app j ≫ φ = α.app j ≫ c'.ι.app j)
    (hφ' : ∀ j, d.ι.app j ≫ φ' = α.app j ≫ d'.ι.app j) [QuasiIso φ] : QuasiIso φ' := by
  have hcomm : (hc.coconePointUniqueUpToIso hd).hom ≫ φ' =
      φ ≫ (hc'.coconePointUniqueUpToIso hd').hom := by
    refine hc.hom_ext fun j => ?_
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc, hφ', reassoc_of% hφ,
      IsColimit.comp_coconePointUniqueUpToIso_hom]
  exact quasiIso_of_arrow_mk_iso _ _ (Arrow.isoMk (hc.coconePointUniqueUpToIso hd)
    (hc'.coconePointUniqueUpToIso hd') hcomm)

/-- Colimits of a shape along which colimits are exact preserve quasi-isomorphisms of diagrams
of cochain complexes. -/
private theorem quasiIso_colimMap {J : Type*} [SmallCategory J] [HasColimitsOfShape J B]
    [HasExactColimitsOfShape J B] (D D' : J ⥤ CochainComplex B ℤ) (α : D ⟶ D')
    (hα : ∀ j, QuasiIso (α.app j)) : QuasiIso (colim.map α) := by
  let G : (J ⥤ B) ⥤ B := colim
  let ψ := diagramComplexMap B α
  have : QuasiIso ψ := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro j
    change QuasiIso (α.app j)
    exact hα j
  have : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) := by
    have : G.Additive := ⟨by
      intro Y Z f g
      apply colimit.hom_ext
      intro j
      change colimit.ι Y j ≫ colim.map (f + g) = colimit.ι Y j ≫ (colim.map f + colim.map g)
      rw [colimit.ι_map, Preadditive.comp_add, colimit.ι_map, colimit.ι_map]
      simp⟩
    have : G.PreservesHomology := by infer_instance
    exact HomologicalComplex.quasiIso_map_of_preservesHomology ψ G
  refine quasiIso_of_isColimit_of_quasiIso B α (diagramComplexCoconeIsColimit B D)
    (colimit.isColimit D) (diagramComplexCoconeIsColimit B D') (colimit.isColimit D')
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) (colim.map α) (fun j => ?_)
    fun j => colimit.ι_map _ _
  ext n
  let αn : (D ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) n) ⟶
      (D' ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) n) :=
    { app := fun j => (α.app j).f n
      naturality := by
        intro i j f
        exact congrArg (fun φ => φ.f n) (α.naturality f) }
  change colimit.ι (D ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) n) j ≫
      colim.map αn = αn.app j ≫
      colimit.ι (D' ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) n) j
  exact colimit.ι_map _ _

/-- A morphism between colimits of diagrams of cochain complexes which is induced by a
degreewise quasi-isomorphism is a quasi-isomorphism, provided colimits of the shape are
exact. -/
private theorem quasiIso_of_isColimit {J : Type*} [SmallCategory J] [HasColimitsOfShape J B]
    [HasExactColimitsOfShape J B] {D D' : J ⥤ CochainComplex B ℤ} (α : D ⟶ D')
    (hα : ∀ j, QuasiIso (α.app j)) {c : Cocone D} {c' : Cocone D'} (hc : IsColimit c)
    (hc' : IsColimit c') (φ : c.pt ⟶ c'.pt)
    (hφ : ∀ j, c.ι.app j ≫ φ = α.app j ≫ c'.ι.app j) : QuasiIso φ := by
  have : QuasiIso (colim.map α) := quasiIso_colimMap B D D' α hα
  exact quasiIso_of_isColimit_of_quasiIso B α (colimit.isColimit D) hc (colimit.isColimit D') hc'
    (colim.map α) φ (fun j => colimit.ι_map _ _) hφ

end ComplexColimits

/-! ### Transfinite iteration of a functorial monomorphic step -/

/-- The inclusion into the transfinite iteration of a natural transformation from the identity,
evaluated at `Y`, is a transfinite composition of morphisms satisfying `P`, provided every
component of the transformation satisfies `P`. -/
private def transfiniteCompositionIterationOfNatTrans {C : Type*} [Category* C] {F : C ⥤ C}
    (η : 𝟭 C ⟶ F) (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    [HasColimitsOfSize.{w, w} C] (P : MorphismProperty C) (Y : C) (hη : ∀ Z, P (η.app Z)) :
    P.TransfiniteCompositionOfShape J
      (((SmallObject.SuccStruct.ofNatTrans η).ιIteration J).app Y) :=
  (((SmallObject.SuccStruct.ofNatTrans η).transfiniteCompositionOfShapeιIteration J).ofLE
    (by
      change MorphismProperty.ofHoms (fun G : C ⥤ C => Functor.whiskerLeft G η) ≤ _
      rw [MorphismProperty.ofHoms_le_iff]
      exact fun G => hη (G.obj Y) : _ ≤ P.inverseImage ((CategoryTheory.evaluation C C).obj Y))).map

section Iteration

variable {E : Type*} [Category* E] [Abelian E] [IsGrothendieckAbelian.{w} E]
  [HasColimitsOfSize.{w, w} E]

/-- The transfinite iteration of an endofunctor along a natural transformation from the
identity, through the ordinal of a cardinal. -/
private def iterationOf (F : E ⥤ E) (η : 𝟭 E ⟶ F) (κ : Cardinal.{w})
    [OrderBot κ.ord.ToType] : E ⥤ E :=
  (SmallObject.SuccStruct.ofNatTrans η).iteration κ.ord.ToType

/-- The canonical natural transformation into the transfinite iteration. -/
private def iterationOfInclusion (F : E ⥤ E) (η : 𝟭 E ⟶ F) (κ : Cardinal.{w})
    [OrderBot κ.ord.ToType] : 𝟭 E ⟶ iterationOf F η κ :=
  (SmallObject.SuccStruct.ofNatTrans η).ιIteration κ.ord.ToType

/-- Each component of the inclusion into the transfinite iteration is a monomorphism, provided
each component of the step is. -/
private theorem iterationOfInclusion_mono (F : E ⥤ E) (η : 𝟭 E ⟶ F) (hη : ∀ Z, Mono (η.app Z))
    (κ : Cardinal.{w}) [OrderBot κ.ord.ToType] (Y : E) :
    Mono ((iterationOfInclusion F η κ).app Y) := by
  have hcomp := transfiniteCompositionIterationOfNatTrans η κ.ord.ToType
    (MorphismProperty.monomorphisms E) Y hη
  simpa [iterationOfInclusion, iterationOf, SmallObject.SuccStruct.ofNatTrans] using
    MorphismProperty.transfiniteCompositionsOfShape_le _ _ _ hcomp.mem

/-- Each transition map of the tower of transfinite iterates is a monomorphism, provided each
component of the step is. -/
private theorem iterationFunctor_map_mono (F : E ⥤ E) (η : 𝟭 E ⟶ F) (hη : ∀ Z, Mono (η.app Z))
    (κ : Cardinal.{w}) [OrderBot κ.ord.ToType] (i j : κ.ord.ToType) (f : i ⟶ j) (Y : E) :
    Mono ((((SmallObject.SuccStruct.ofNatTrans η).iterationFunctor
      κ.ord.ToType).map f).app Y) := by
  exact (transfiniteCompositionIterationOfNatTrans η κ.ord.ToType
    (MorphismProperty.monomorphisms E) Y hη).mem_map f

/-- A morphism out of an object with fewer subobjects than the cofinality of `κ.ord`, into a
value of the transfinite iteration, factors through a stage of the tower. This is Tag 079F
applied to the tower, whose transition maps are monomorphisms. -/
private theorem factor_through_iterationOf (F : E ⥤ E) (η : 𝟭 E ⟶ F) (hη : ∀ Z, Mono (η.app Z))
    (κ : Cardinal.{w}) (hκ : κ.IsRegular) [OrderBot κ.ord.ToType] (Y Z : E)
    (hY : HasCardinalLT (Subobject Y) κ) (f : Y ⟶ (iterationOf F η κ).obj Z) :
    ∃ (i : κ.ord.ToType) (g : Y ⟶ (((SmallObject.SuccStruct.ofNatTrans η).iterationFunctor
      κ.ord.ToType).obj i).obj Z),
      g ≫ (((SmallObject.SuccStruct.ofNatTrans η).iterationCocone
        κ.ord.ToType).ι.app i).app Z = f := by
  let S := SmallObject.SuccStruct.ofNatTrans η
  let ev := (CategoryTheory.evaluation E E).obj Z
  let T := S.iterationFunctor κ.ord.ToType ⋙ ev
  have hmono : ∀ {i j : κ.ord.ToType} (uu : i ⟶ j), Mono (T.map uu) := by
    intro i j uu
    dsimp [T, ev]
    exact iterationFunctor_map_mono F η hη κ i j uu Z
  exact Stacks.Injectives.exists_factorization_of_hasCardinalLT_subobject_cof
    Y κ.ord (by rwa [hκ.cof_ord]) T (fun {_ _} uu => hmono uu)
    (isColimitOfPreserves ev (S.isColimitIterationCocone κ.ord.ToType)) f

/-- Every morphism from an object with fewer than `κ` subobjects into a value of the transfinite
iteration extends along `i`, provided every morphism into a value of the step functor does. -/
private theorem exists_extension_iterationOf (F : E ⥤ E) (η : 𝟭 E ⟶ F)
    (hη : ∀ Z, Mono (η.app Z)) (κ : Cardinal.{w}) (hκ : κ.IsRegular) [OrderBot κ.ord.ToType]
    [NoMaxOrder κ.ord.ToType] {Y Y' : E} (i : Y ⟶ Y') (hY : HasCardinalLT (Subobject Y) κ)
    (hext : ∀ (Z : E) (g : Y ⟶ Z), ∃ h : Y' ⟶ F.obj Z, i ≫ h = g ≫ η.app Z) (M : E)
    (f : Y ⟶ (iterationOf F η κ).obj M) :
    ∃ g : Y' ⟶ (iterationOf F η κ).obj M, i ≫ g = f := by
  let S := SmallObject.SuccStruct.ofNatTrans η
  obtain ⟨j, g₀, hg₀⟩ := factor_through_iterationOf F η hη κ hκ Y M hY f
  obtain ⟨h, hh⟩ := hext (((S.iterationFunctor κ.ord.ToType).obj j).obj M) g₀
  have hjmax : ¬ IsMax j := not_isMax j
  have hmap : ((S.iterationFunctor κ.ord.ToType).map (homOfLE (Order.le_succ j))).app M =
      η.app (((S.iterationFunctor κ.ord.ToType).obj j).obj M) ≫
        (S.iterationFunctorObjSuccIso j hjmax).inv.app M :=
    NatTrans.congr_app (S.iterationFunctor_map_succ j hjmax) M
  have hw := congrArg (fun q : (S.iterationFunctor κ.ord.ToType).obj j ⟶
    (S.iterationCocone κ.ord.ToType).pt => q.app M)
    ((S.iterationCocone κ.ord.ToType).w (homOfLE (Order.le_succ j)))
  simp only [NatTrans.comp_app] at hw
  refine ⟨h ≫ (S.iterationFunctorObjSuccIso j hjmax).inv.app M ≫
    ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app M, ?_⟩
  rw [← Category.assoc i h, hh, ← hg₀, ← hw, hmap]
  exact (Category.assoc _ _ _).trans (congrArg (g₀ ≫ ·) (Category.assoc _ _ _).symm)

end Iteration

/-! ### The resolution -/

section Resolution

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  [HasWeakSheafify X.J (Type max u v w)]
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- Quasi-isomorphisms of right differential graded modules, as a class of morphisms. -/
private abbrev dgQuasiIso
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    MorphismProperty (DifferentialGradedModule.{u, v, max u v w} A) :=
  (HomologicalComplex.quasiIso
    (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ)).inverseImage (toCochainComplex.{u, v, max u v w} A)

/-- Quasi-isomorphisms of right differential graded modules are stable under filtered
colimits. -/
private instance dgQuasiIso_isStableUnderFilteredColimits :
    MorphismProperty.IsStableUnderFilteredColimits.{max u v w, max u v w}
      (dgQuasiIso.{u, v, w} A) where
  isStableUnderColimitsOfShape J _ _ := by
    constructor
    intro D D' c c' hc hc' f hf φ hφ
    let G := toCochainComplex.{u, v, max u v w} A
    have : PreservesColimitsOfShape J G := toCochainComplex_preservesColimitsOfShape.{u, v, w} A J
    have : HasExactColimitsOfShape J
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      AB5OfSize.ofShape _
    change QuasiIso (G.map φ)
    refine quasiIso_of_isColimit
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (Functor.whiskerRight f G) (fun j => hf j) (isColimitOfPreserves G hc)
      (isColimitOfPreserves G hc') (G.map φ) fun j => ?_
    change G.map (c.ι.app j) ≫ G.map φ = G.map (f.app j) ≫ G.map (c'.ι.app j)
    rw [← G.map_comp, ← G.map_comp, hφ j]

omit [HasWeakSheafify X.J (Type max u v w)] in
open MorphismProperty in
/-- Quasi-isomorphisms of right differential graded modules are stable under transfinite
composition of any well-ordered shape. -/
private theorem dgQuasiIso_isStableUnderTransfiniteCompositionOfShape (J : Type max u v w)
    [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    (dgQuasiIso.{u, v, w} A).IsStableUnderTransfiniteCompositionOfShape J := by
  apply IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape
  intro J' _ _ _ _
  have : HasColimitsOfShape J' (DifferentialGradedModule.{u, v, max u v w} A) :=
    HasColimitsOfShape.of_small.{max u v w, max u v w} _ J'
  infer_instance

/-- A functorial graded injective K-injective resolution: an endofunctor on right differential
graded modules together with a natural monomorphic quasi-isomorphism from the identity whose
values are graded injective and K-injective. -/
structure GradedInjectiveKInjectiveResolution
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] where
  /-- The resolution endofunctor. -/
  functor : DifferentialGradedModule.{u, v, max u v w} A ⥤
    DifferentialGradedModule.{u, v, max u v w} A
  /-- The natural morphism from a module to its resolution. -/
  inclusion : 𝟭 (DifferentialGradedModule.{u, v, max u v w} A) ⟶ functor
  /-- Each component of the inclusion is a monomorphism. -/
  mono (M : DifferentialGradedModule.{u, v, max u v w} A) : Mono (inclusion.app M)
  /-- Each component of the inclusion is a quasi-isomorphism. -/
  quasiIso (M : DifferentialGradedModule.{u, v, max u v w} A) :
    QuasiIso (inclusion.app M).toHomologicalComplex
  /-- Each value of the resolution functor is graded injective. -/
  gradedInjective (M : DifferentialGradedModule.{u, v, max u v w} A) :
    GradedInjective (functor.obj M)
  /-- Each value of the resolution functor is K-injective. -/
  kInjective (M : DifferentialGradedModule.{u, v, max u v w} A) :
    IsKInjective (functor.obj M)

/-- A regular cardinal exceeding the number of subobjects of every member of a set-indexed
family of right differential graded modules. -/
private theorem exists_regular_cardinal_bound {Idx : Type max u v w}
    (Ms : Idx → DifferentialGradedModule.{u, v, max u v w} A) :
    ∃ κ : Cardinal.{max u v w}, κ.IsRegular ∧
      ∀ r, HasCardinalLT (Subobject (Ms r)) κ := by
  let sz : Idx → Cardinal.{max u v w} := fun r =>
    Cardinal.mk (Shrink.{max u v w} (Subobject (Ms r)))
  let β := max Cardinal.aleph0 (⨆ r, sz r)
  refine ⟨Order.succ β, Cardinal.isRegular_succ (le_max_left _ _), fun r => ?_⟩
  have hle : sz r ≤ β := le_trans (le_ciSup Cardinal.bddAbove_of_small r) (le_max_right _ _)
  exact (hasCardinalLT_iff_of_equiv (equivShrink.{max u v w} (Subobject (Ms r)))
    (Order.succ β)).2 ((hasCardinalLT_iff_cardinal_mk_lt _ _).2 (hle.trans_lt (Order.lt_succ β)))

/-- **Stacks Tag 0FT0.** Let `X` be a ringed site and let `A` be a sheaf of differential graded
algebras on it. Suppose given a set-indexed family of monomorphisms `i r : Ms r ⟶ Ms' r` of
acyclic right differential graded `A`-modules which *detects* the K-injective graded injective
modules: a module into which every morphism from `Ms r` extends along `i r` is K-injective and
graded injective. Then every right differential graded `A`-module admits a functorial
quasi-isomorphic monomorphism into a graded injective K-injective module.

The detecting family is the conclusion of Tag 0FSY, produced by
`exists_setIndexed_acyclic_monomorphisms_iff`; see the implementation notes. -/
@[stacks 0FT0 "the functorial resolution"]
theorem exists_gradedInjectiveKInjectiveResolution
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {Idx : Type max u v w}
    (Ms Ms' : Idx → DifferentialGradedModule.{u, v, max u v w} A) (i : ∀ r, Ms r ⟶ Ms' r)
    (hi : ∀ r, Mono (i r)) (hMs : ∀ r, (Ms r).complex.Acyclic)
    (hMs' : ∀ r, (Ms' r).complex.Acyclic)
    (hdetect : ∀ I : DifferentialGradedModule.{u, v, max u v w} A,
      (∀ (r : Idx) (f : Ms r ⟶ I), ∃ g : Ms' r ⟶ I, i r ≫ g = f) →
        IsKInjective I ∧ GradedInjective I) :
    Nonempty (GradedInjectiveKInjectiveResolution.{u, v, w} A) := by
  let C := DifferentialGradedModule.{u, v, max u v w} A
  obtain ⟨F, η, hηmono, hηqi, hηext⟩ :=
    functorSetOfMonos.{u, v, w, max u v w} Ms Ms' i hi hMs hMs'
  obtain ⟨κ, hκ, hbound⟩ := exists_regular_cardinal_bound (A := A) Ms
  have : Fact κ.IsRegular := ⟨hκ⟩
  have : Nonempty κ.ord.ToType := by simpa using hκ.ne_zero
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  have : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder hκ.aleph0_le
  have hqi : ∀ M : C, QuasiIso ((iterationOfInclusion F η κ).app M).toHomologicalComplex := by
    intro M
    have := dgQuasiIso_isStableUnderTransfiniteCompositionOfShape (A := A) κ.ord.ToType
    exact MorphismProperty.transfiniteCompositionsOfShape_le (dgQuasiIso.{u, v, w} A)
      κ.ord.ToType _
      (transfiniteCompositionIterationOfNatTrans η κ.ord.ToType (dgQuasiIso.{u, v, w} A) M hηqi).mem
  have hext : ∀ (M : C) (r : Idx) (f : Ms r ⟶ (iterationOf F η κ).obj M),
      ∃ g : Ms' r ⟶ (iterationOf F η κ).obj M, i r ≫ g = f := fun M r =>
    exists_extension_iterationOf F η hηmono κ hκ (i r) (hbound r) (fun Z => hηext Z r) M
  exact ⟨{ functor := iterationOf F η κ
           inclusion := iterationOfInclusion F η κ
           mono := iterationOfInclusion_mono F η hηmono κ
           quasiIso := hqi
           gradedInjective := fun M => (hdetect _ (hext M)).2
           kInjective := fun M => (hdetect _ (hext M)).1 }⟩

/-- **Stacks Tag 0FT0.** Let `X` be a ringed site and let `A` be a sheaf of differential graded
algebras on it. Given a set-indexed family of monomorphisms of acyclic right differential graded
`A`-modules detecting the K-injective graded injective modules, every right differential graded
`A`-module `M` admits a quasi-isomorphism `M ⟶ I` with `I` graded injective and K-injective. -/
@[stacks 0FT0 "the resolution of a single module"]
theorem exists_quasiIso_gradedInjective_isKInjective
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {Idx : Type max u v w}
    (Ms Ms' : Idx → DifferentialGradedModule.{u, v, max u v w} A) (i : ∀ r, Ms r ⟶ Ms' r)
    (hi : ∀ r, Mono (i r)) (hMs : ∀ r, (Ms r).complex.Acyclic)
    (hMs' : ∀ r, (Ms' r).complex.Acyclic)
    (hdetect : ∀ I : DifferentialGradedModule.{u, v, max u v w} A,
      (∀ (r : Idx) (f : Ms r ⟶ I), ∃ g : Ms' r ⟶ I, i r ≫ g = f) →
        IsKInjective I ∧ GradedInjective I)
    (M : DifferentialGradedModule.{u, v, max u v w} A) :
    ∃ (I : DifferentialGradedModule.{u, v, max u v w} A) (f : M ⟶ I),
      QuasiIso f.toHomologicalComplex ∧ GradedInjective I ∧ IsKInjective I := by
  obtain ⟨res⟩ := exists_gradedInjectiveKInjectiveResolution A Ms Ms' i hi hMs hMs' hdetect
  exact ⟨res.functor.obj M, res.inclusion.app M, res.quasiIso M, res.gradedInjective M,
    res.kInjective M⟩

end Resolution

end SheafOfModules.DifferentialGradedModule
