module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.FreeSum
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.FreeMooreFibrewiseVanishing
public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomotopy
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.RepresentableAcyclicity

/-!
# The positive homology of a free presheaf on a fibrewise point resolution vanishes

For `G` the free abelian presheaf on a coproduct of representables `∐_i h_{x_i}` and `V` an object
of the base, `G(A_{•,V})` is the free simplicial abelian group on `∐_i Hom(A_{•,V}, x_i)`. Its
fibres over `∐_i Hom(V, p(x_i))` are the simplicial sets `Mor_{C_V}(A_{•,V}, h^*x_i)`, homotopy
equivalent to a point by hypothesis, so its Moore complex has no positive homology. This is the
case of free presheaves of Stacks 08Q9, applied fibrewise.

## Main results

* `Stacks.ChaoticSite.isZero_homology_freeMooreComplex_of_constFibre_isZero`: the free Moore
  complex of a simplicial set has no positive homology when its fibres over a set have none.
* `FibredCategorySituation.isZero_pointMooreComplex_homology_of_isFreeSum`: for `G` a free abelian
  presheaf on a coproduct of representables, the complex `V ↦ G(A_{•,V})` has no positive homology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

namespace Stacks.ChaoticSite

universe v t

variable {S : SimplicialObject (Type v)} {K : Type v}
  (φ : S ⟶ (Functor.const SimplexCategoryᵒᵖ).obj K)

/-- **The free Moore complex of a simplicial set has no positive homology when its fibres over a
set have none.** -/
theorem isZero_homology_freeMooreComplex_of_constFibre_isZero
    (hφ : ∀ k (n : ℕ), 0 < n → IsZero (((alternatingFaceMapComplex AddCommGrpCat.{max v t}).obj
      (constFibre φ k ⋙ uliftFunctor.{t} ⋙ AddCommGrpCat.free)).homology n))
    (n : ℕ) (hn : 0 < n) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat.{max v t}).obj
      (S ⋙ uliftFunctor.{t} ⋙ AddCommGrpCat.free)).homology n) := by
  have : AB4OfSize.{v} AddCommGrpCat.{max v t} := AB4OfSize_shrink.{v, t} _
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := AddCommGrpCat.{max v t}) (J := Discrete K) (ComplexShape.down ℕ) n
  have hc := isColimitOfPreserves
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max v t} (ComplexShape.down ℕ) n)
    (isColimitFreeMooreConstFibreCofan.{v, t} φ)
  rw [IsZero.iff_id_eq_zero]
  exact hc.hom_ext fun ⟨k⟩ => (hφ k n hn).eq_of_src _ _

/-- Positive-degree vanishing of the free Moore complex is invariant under isomorphism of
simplicial sets. -/
lemma isZero_homology_freeMooreComplex_of_iso {X Y : SimplicialObject (Type v)} (e : X ≅ Y)
    (n : ℕ) (h : IsZero (((alternatingFaceMapComplex AddCommGrpCat.{max v t}).obj
      (Y ⋙ uliftFunctor.{t} ⋙ AddCommGrpCat.free)).homology n)) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat.{max v t}).obj
      (X ⋙ uliftFunctor.{t} ⋙ AddCommGrpCat.free)).homology n) :=
  h.of_iso ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    ((alternatingFaceMapComplex AddCommGrpCat.{max v t}).mapIso
      (Functor.isoWhiskerRight e (uliftFunctor.{t} ⋙ AddCommGrpCat.free))))

end Stacks.ChaoticSite

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

universe uD vD uC vC w

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  {A : s.base.C ⥤ CosimplicialObject s.C}

/-- **Positive homology of the complex of presheaves `V ↦ G(A_{•,V})` vanishes as soon as it does
at every object `V`.** -/
lemma isZero_pointMooreComplex_homology_of_forall
    (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) (n : ℕ)
    (h : ∀ V : s.base.C, IsZero (((alternatingFaceMapComplex AddCommGrpCat.{max w uD vD uC vC}).obj
      ((A.obj V).op ⋙ G)).homology n)) :
    IsZero (((pointMooreComplex s A).obj G).homology n) := by
  refine Functor.isZero _ fun V => ?_
  have e := ShortComplex.mapHomologyIso (((pointMooreComplex s A).obj G).sc n)
    ((evaluation s.base.Cᵒᵖ AddCommGrpCat.{max w uD vD uC vC}).obj V)
  refine IsZero.of_iso ?_ e.symm
  have hmap := Functor.congr_obj (AlgebraicTopology.map_alternatingFaceMapComplex
    ((evaluation s.base.Cᵒᵖ AddCommGrpCat.{max w uD vD uC vC}).obj V))
    ((pointEvaluation s A).obj G)
  have := h V.unop
  show IsZero ((((alternatingFaceMapComplex _ ⋙ ((evaluation s.base.Cᵒᵖ
    AddCommGrpCat.{max w uD vD uC vC}).obj V).mapHomologicalComplex _).obj
      ((pointEvaluation s A).obj G)).sc n).homology)
  rwa [hmap]

variable (hA : A ⋙ (Functor.whiskeringRight SimplexCategory s.C s.base.C).obj s.p =
    Functor.const SimplexCategory)

variable (A) in
/-- The simplicial set `n ↦ Hom(A_{n,V}, x)`, lifted to the universe of the sections. -/
abbrev pointHomSSet (V : s.base.C) (x : s.C) : SimplicialObject (Type (max w uD vD uC vC)) :=
  (A.obj V).op ⋙ uliftYoneda.{max w uD vD uC}.obj x

/-- The map `Hom(A_{n,V}, x) ⟶ Hom(V, p(x))` induced by the projection. -/
def pointHomSSetProj (V : s.base.C) (x : s.C) :
    pointHomSSet s A V x ⟶ (Functor.const SimplexCategoryᵒᵖ).obj
      (ULift.{max w uD vD uC vC} (V ⟶ s.p.obj x)) where
  app n := ↾fun g => ⟨eqToHom (obj_obj_proj s hA V n.unop).symm ≫ s.p.map g.down⟩
  naturality n m f := by
    ext ⟨g⟩
    have := isHomLift_obj_map s hA V f.unop
    have hp := IsHomLift.fac' s.p (𝟙 V) ((A.obj V).map f.unop)
    change (⟨eqToHom _ ≫ s.p.map ((A.obj V).map f.unop ≫ g)⟩ : ULift (V ⟶ s.p.obj x)) =
      ⟨eqToHom _ ≫ s.p.map g⟩
    rw [Functor.map_comp, hp]
    simp

/-- The pullback of `x` along `h : V ⟶ p(x)`, as an object of the fibre over `V`. -/
abbrev pullbackFiber {V : s.base.C} {x : s.C} (h : V ⟶ s.p.obj x) : s.p.Fiber V :=
  ⟨Functor.IsPreFibered.pullbackObj (p := s.p) (rfl : s.p.obj x = s.p.obj x) h,
    Functor.IsPreFibered.pullbackObj_proj (p := s.p) rfl h⟩

/-- The chosen cartesian map from the pullback. -/
def pullbackFiberπ {V : s.base.C} {x : s.C} (h : V ⟶ s.p.obj x) :
    Functor.Fiber.fiberInclusion.obj (pullbackFiber s h) ⟶ x :=
  Functor.IsPreFibered.pullbackMap (p := s.p) (rfl : s.p.obj x = s.p.obj x) h

/-- The chosen map `pullbackFiberπ s h` is cartesian over `h`. -/
instance isCartesian_pullbackFiberπ {V : s.base.C} {x : s.C} (h : V ⟶ s.p.obj x) :
    s.p.IsCartesian h (pullbackFiberπ s h) :=
  Functor.IsPreFibered.pullbackMap.IsCartesian (p := s.p) _ h

include hA in
/-- A morphism `g : A_{n,V} ⟶ x` whose image in `Hom(V, p(x))` is `h` lies over `h`. -/
lemma isHomLift_of_pointHomSSetProj {V : s.base.C} {x : s.C} {h : V ⟶ s.p.obj x}
    {n : SimplexCategory} (g : (A.obj V).obj n ⟶ x)
    (hg : eqToHom (obj_obj_proj s hA V n).symm ≫ s.p.map g = h) : s.p.IsHomLift h g :=
  IsHomLift.of_fac' s.p h g (obj_obj_proj s hA V n) rfl (by rw [← hg]; simp)

/-- The fibre of `Hom(A_{n,V}, x) ⟶ Hom(V, p(x))` over `h` is `Mor_{C_V}(A_{n,V}, h^*x)`. -/
def pointHomFibreEquiv {V : s.base.C} {x : s.C} (h : V ⟶ s.p.obj x) (n : SimplexCategory) :
    {g : ULift.{max w uD vD uC} ((A.obj V).obj n ⟶ x) //
      (⟨eqToHom (obj_obj_proj s hA V n).symm ≫ s.p.map g.down⟩ :
        ULift.{max w uD vD uC vC} (V ⟶ s.p.obj x)) = ⟨h⟩} ≃
      ULift.{max w uD vD uC vC}
        ((Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).obj n ⟶ pullbackFiber s h) where
  toFun g :=
    ⟨⟨@Functor.IsCartesian.map _ _ _ _ s.p _ _ _ _ h (pullbackFiberπ s h) _ _ g.1.down
      (isHomLift_of_pointHomSSetProj s hA (n := n) g.1.down
        (congrArg ULift.down g.2 : eqToHom _ ≫ s.p.map g.1.down = h)),
      @Functor.IsCartesian.map_isHomLift _ _ _ _ s.p _ _ _ _ h (pullbackFiberπ s h) _ _ g.1.down
      (isHomLift_of_pointHomSSetProj s hA (n := n) g.1.down
        (congrArg ULift.down g.2 : eqToHom _ ≫ s.p.map g.1.down = h))⟩⟩
  invFun g := ⟨⟨Functor.Fiber.fiberInclusion.map g.down ≫ pullbackFiberπ s h⟩, by
    have h1 := IsHomLift.fac' s.p (𝟙 V) (Functor.Fiber.fiberInclusion.map g.down)
    have h2 := IsHomLift.fac' s.p h (pullbackFiberπ s h)
    apply ULift.ext
    change eqToHom _ ≫ s.p.map (Functor.Fiber.fiberInclusion.map g.down ≫ pullbackFiberπ s h) = h
    rw [Functor.map_comp, h1, h2]
    have key : ∀ (W W' : s.base.C) (a : V = W) (b : W = V) (c : V = W') (d : W' = V)
        (e : s.p.obj x = s.p.obj x),
        eqToHom a ≫ (eqToHom b ≫ 𝟙 V ≫ eqToHom c) ≫ eqToHom d ≫ h ≫ eqToHom e = h := by
      intro W W' a b c d e
      subst a c
      simp
    exact key _ _ _ _ _ _ _⟩
  left_inv g := by
    have := isHomLift_of_pointHomSSetProj s hA (n := n) g.1.down
      (congrArg ULift.down g.2 : eqToHom _ ≫ s.p.map g.1.down = h)
    exact Subtype.ext (ULift.ext _ _ (Functor.IsCartesian.fac s.p h (pullbackFiberπ s h) g.1.down))
  right_inv g := ULift.ext _ _ (Functor.Fiber.hom_ext (Functor.IsCartesian.map_uniq s.p h
    (pullbackFiberπ s h) _ (Functor.Fiber.fiberInclusion.map g.down) rfl).symm)

/-- The fibre of `Hom(A_{•,V}, x) ⟶ Hom(V, p(x))` over `h` is `Mor_{C_V}(A_{•,V}, h^*x)`. -/
def pointHomFibreIso {V : s.base.C} {x : s.C} (h : V ⟶ s.p.obj x) :
    Stacks.ChaoticSite.constFibre (pointHomSSetProj s hA V x) ⟨h⟩ ≅
      ((Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).op ⋙
        yoneda.obj (pullbackFiber s h)) ⋙ uliftFunctor.{max w uD vD uC vC} :=
  NatIso.ofComponents (fun n => Equiv.toIso (pointHomFibreEquiv s hA h n.unop)) (fun {n m} f => by
    ext g
    apply ULift.ext
    apply Functor.Fiber.hom_ext
    have := isHomLift_obj_map s hA V f.unop
    have hg := isHomLift_of_pointHomSSetProj s hA (n := n.unop) g.1.down
      (congrArg ULift.down g.2 : eqToHom _ ≫ s.p.map g.1.down = h)
    have hg' := isHomLift_of_pointHomSSetProj s hA (n := m.unop)
      ((A.obj V).map f.unop ≫ g.1.down)
      (congrArg ULift.down
        ((Stacks.ChaoticSite.constFibre (pointHomSSetProj s hA V x) ⟨h⟩).map f g).2 :
        eqToHom _ ≫ s.p.map ((A.obj V).map f.unop ≫ g.1.down) = h)
    have hmap := @Functor.IsCartesian.map_isHomLift _ _ _ _ s.p _ _ _ _ h (pullbackFiberπ s h) _ _
      g.1.down hg
    change @Functor.IsCartesian.map _ _ _ _ s.p _ _ _ _ h (pullbackFiberπ s h) _ _
        ((A.obj V).map f.unop ≫ g.1.down) hg' =
      (A.obj V).map f.unop ≫
        @Functor.IsCartesian.map _ _ _ _ s.p _ _ _ _ h (pullbackFiberπ s h) _ _ g.1.down hg
    refine (@Functor.IsCartesian.map_uniq _ _ _ _ s.p _ _ _ _ h (pullbackFiberπ s h) _ _
      ((A.obj V).map f.unop ≫ g.1.down) hg' _ inferInstance ?_).symm
    rw [Category.assoc, @Functor.IsCartesian.fac _ _ _ _ s.p _ _ _ _ h (pullbackFiberπ s h) _ _
      g.1.down hg])

variable (hres : ∀ (V : s.base.C) (W : s.p.Fiber V),
  ∃ f : (Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).op ⋙ yoneda.obj W ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vC + 1},
    SimplicialObject.homotopyEquivalences (Type vC) f)

include hres in
/-- **The free Moore complex of `Hom(A_{•,V}, x)` has no positive homology**: its fibres over
`Hom(V, p(x))` are the simplicial sets `Mor_{C_V}(A_{•,V}, h^*x)`, homotopy equivalent to a
point. -/
lemma isZero_homology_pointHomSSet (V : s.base.C) (x : s.C) (n : ℕ) (hn : 0 < n) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat.{max w uD vD uC vC}).obj
      (pointHomSSet s A V x ⋙ uliftFunctor.{max w uD vD uC vC} ⋙
        AddCommGrpCat.free)).homology n) := by
  refine Stacks.ChaoticSite.isZero_homology_freeMooreComplex_of_constFibre
    (pointHomSSetProj s hA V x) (fun ⟨h⟩ => ?_) n hn
  obtain ⟨f₀, hf₀⟩ := hres V (pullbackFiber s h)
  let e : (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vC + 1} ⋙
      uliftFunctor.{max w uD vD uC vC} ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{max w uD vD uC vC + 1} :=
    Functor.constComp _ _ _ ≪≫
      (Functor.const _).mapIso (Equiv.toIso (Equiv.ulift.trans Equiv.punitEquivPUnit))
  exact ⟨(pointHomFibreIso s hA h).hom ≫ Functor.whiskerRight f₀ uliftFunctor ≫ e.hom,
    CategoryTheory.SimplicialObject.homotopyEquivalences_iso_comp_iso _ _ _
      (CategoryTheory.SimplicialObject.homotopyEquivalences_whiskering_map uliftFunctor hf₀)⟩

variable (A) in
/-- The projection of `n ↦ ∐_i Hom(A_{n,V}, x_i)` to the index set. -/
def sigmaYonedaIndex {ι : Type (max w uD vD uC vC)} (x : ι → s.C) (V : s.base.C) :
    (A.obj V).op ⋙ sigmaYoneda s x ⟶ (Functor.const SimplexCategoryᵒᵖ).obj ι where
  app _ := ↾fun g => g.1
  naturality _ _ _ := rfl

variable (A) in
/-- The fibre of `sigmaYonedaIndex` over `i` is `Hom(A_{•,V}, x_i)`. -/
def sigmaYonedaIndexFibreIso {ι : Type (max w uD vD uC vC)} (x : ι → s.C) (V : s.base.C)
    (i : ι) :
    Stacks.ChaoticSite.constFibre (sigmaYonedaIndex s A x V) i ≅ pointHomSSet s A V (x i) :=
  NatIso.ofComponents (fun n => Equiv.toIso
    { toFun := fun g => cast (congrArg
        (fun j => ULift.{max w uD vD uC} ((A.obj V).obj n.unop ⟶ x j)) g.2) g.1.2
      invFun := fun g => ⟨⟨i, g⟩, rfl⟩
      left_inv := by rintro ⟨⟨j, g⟩, rfl⟩; rfl
      right_inv := fun _ => rfl }) (fun {n m} f => by
    ext ⟨⟨j, g⟩, hj⟩
    subst hj
    rfl)

include hres in
/-- **The free Moore complex of `n ↦ ∐_i Hom(A_{n,V}, x_i)` has no positive homology.** -/
lemma isZero_homology_sigmaYoneda {ι : Type (max w uD vD uC vC)} (x : ι → s.C) (V : s.base.C)
    (n : ℕ) (hn : 0 < n) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat.{max w uD vD uC vC}).obj
      (((A.obj V).op ⋙ sigmaYoneda s x) ⋙ uliftFunctor.{max w uD vD uC vC} ⋙
        AddCommGrpCat.free)).homology n) :=
  Stacks.ChaoticSite.isZero_homology_freeMooreComplex_of_constFibre_isZero
    (sigmaYonedaIndex s A x V) (fun i k hk =>
      Stacks.ChaoticSite.isZero_homology_freeMooreComplex_of_iso
        (sigmaYonedaIndexFibreIso s A x V i) k
        (isZero_homology_pointHomSSet s hA hres V (x i) k hk)) n hn

include hres in
/-- For `G` a free abelian presheaf on a coproduct of representables, the complex of presheaves
`V ↦ G(A_{•,V})` has no positive homology: the case of free presheaves of Stacks 08Q9, applied
fibrewise. -/
theorem isZero_pointMooreComplex_homology_of_isFreeSum
    (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) (hG : IsFreeSum s G) (n : ℕ) :
    IsZero (((pointMooreComplex s A).obj G).homology (n + 1)) := by
  obtain ⟨ι, x, ⟨e⟩⟩ := hG
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso
    ((pointMooreComplex s A).mapIso e)).symm
  refine isZero_pointMooreComplex_homology_of_forall s _ (n + 1) fun V => ?_
  refine IsZero.of_iso (isZero_homology_sigmaYoneda s hA hres x V (n + 1) n.succ_pos) ?_
  exact (HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso
    ((alternatingFaceMapComplex _).mapIso (Functor.isoWhiskerLeft ((A.obj V).op ⋙ sigmaYoneda s x)
      (Functor.isoWhiskerRight uliftFunctorTrivial AddCommGrpCat.free ≪≫
        Functor.leftUnitor _))).symm

end Stacks.Sites.FibredCategory.FibredCategorySituation
