module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Copower
public import StacksFrontier.CategoryTheory.Sites.CoveringPermanence

/-!
# Hom objects out of a product of simplicial sets

Let `C` be a category with finite limits and let `L` be a simplicial object of `C`. For a finite
simplicial set `A` the *Hom object* `Hom(A, L)` is the simplicial object representing
`W ↦ Mor(W ⊗ A, L)`, and its degree-zero term represents `Y ↦ Mor(A, L ⋙ Mor(Y, -))`
(Tag 017L, `representableByAppZero`). The Hom object is determined only up to isomorphism, and
the statements here are about any representing datum `SimplicialObject.IsHomFromSSet A L H`.

First, `Hom(∂Δ[1], L) = L × L`: the boundary of the standard `1`-simplex has exactly two
simplices in each degree, both of them constant, so a morphism out of it into `L` is a pair of
morphisms.

Second, if `H` represents `Hom(A, L)`, then an object representing
`Y ↦ Mor(T, H ⋙ Mor(Y, -))` also represents `Y ↦ Mor(A ⊗ T, L ⋙ Mor(Y, -))`: points of a Hom
object out of `A` with values in `T` are points of a Hom object out of `A ⊗ T`.

## Main definitions

* `boundaryOneVertex`: the constant `m`-simplex of `∂Δ[1]` at a vertex `i : Fin 2`.
* `boundaryHomObjEquiv` and `homPairEquiv`: morphisms out of `∂Δ[1]` into `L` are pairs of
  morphisms, and so are morphisms into `L ⨯ L`.
* `boundaryIntervalHomFromSSet`: the resulting representing datum exhibiting `L ⨯ L` as
  `Hom(∂Δ[1], L)`.
* `homFromSSetHomObjEquiv`: the representing equivalence of a Hom object, read as an
  identification of morphisms into it with `Hom`-objects of natural transformations.
* `copowerHomObjEquiv` and `sSetMapCopowerEquiv`: the universal property of the copower by a
  simplicial set, in the two forms needed below.
* `homFromSSetPointsEquiv` and `representableBy_homFromSSetPoints`: `T`-points of `Hom(A, L)`
  are points of `Hom(A ⊗ T, L)`.
* `pointwisePresheaf`: the presheaf of simplicial sets `Y ↦ L ⋙ Mor(Y, -)` attached to a
  simplicial object.

## Main results

* `boundaryIntervalHomFromSSet_vertex_zero` and `boundaryIntervalHomFromSSet_vertex_one`: the
  two components of the representing datum for `Hom(∂Δ[1], L)` are the two product projections.
* `homFromSSetPointsEquiv_apply`, `homFromSSetPointsEquiv_precomp` and
  `homFromSSetPointsEquiv_restriction`: the identification of points is computed pointwise, and
  is natural in the simplicial set `T` and in the Hom object.
* `representableByStdSimplex_postcomp`, `matchingCoyonedaCounit_postcomp`,
  `matchingSkeletonHomEquiv_postcomp` and `representableByBoundarySucc_postcomp`: the
  representing data of `L_m` and of the matching object `(cosk_n L)_{n + 1}` are natural in `L`.
* `representedRestriction_comp`: restriction morphisms between representing objects compose.
* `intervalEndpointMap_boundary_restriction`: a morphism `H ⟶ L ⨯ L` whose two components are
  the endpoint evaluations of the universal `Δ[1]`-datum is the restriction of that datum along
  the boundary inclusion.

## References

* [Stacks Project, Tag 017L](https://stacks.math.columbia.edu/tag/017L)
* [Stacks Project, Tag 018V](https://stacks.math.columbia.edu/tag/018V)
-/

@[expose] public section

universe z u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject Opposite Simplicial
open scoped MonoidalCategory

namespace Stacks.CategoryTheory.Hypercovering

/-! ### The two vertices of the interval -/

section BoundaryOne

/-- The constant `m`-simplex of `∂Δ[1]` at the vertex `i : Fin 2`. -/
def boundaryOneVertex {m : SimplexCategoryᵒᵖ} (i : Fin 2) :
    ((SSet.boundary.{z} 1).toSSet).obj m :=
  ⟨SSet.stdSimplex.const 1 i m, by
    change ¬ Function.Surjective (SSet.stdSimplex.asOrderHom _)
    fin_cases i
    · intro hs
      obtain ⟨j, hj⟩ := hs 1
      change (0 : Fin 2) = 1 at hj
      exact (by decide : (0 : Fin 2) ≠ 1) hj
    · intro hs
      obtain ⟨j, hj⟩ := hs 0
      change (1 : Fin 2) = 0 at hj
      exact (by decide : (1 : Fin 2) ≠ 0) hj⟩

/-- The simplicial structure maps of `∂Δ[1]` fix the two constant simplices. -/
lemma boundaryOne_map_vertex {m m' : SimplexCategoryᵒᵖ} (f : m ⟶ m') (i : Fin 2) :
    ((SSet.boundary.{z} 1).toSSet.map f) (boundaryOneVertex (m := m) i) =
      boundaryOneVertex (m := m') i := by
  apply Subtype.ext
  change Δ[1].map f
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
        (OrderHom.const (Fin (m.unop.len + 1)) i))) =
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
      (OrderHom.const (Fin (m'.unop.len + 1)) i))
  rw [SSet.stdSimplex.map_objEquiv_symm]
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  ext j
  simp [SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk]

/-- The simplicial structure maps of `Δ[1]` fix the constant simplices. -/
lemma stdSimplex_map_const {m m' : SimplexCategoryᵒᵖ} (f : m ⟶ m') (i : Fin 2) :
    Δ[1].map f (SSet.stdSimplex.const 1 i m) = SSet.stdSimplex.const 1 i m' :=
  congrArg Subtype.val (boundaryOne_map_vertex f i)

/-- Every simplex of `∂Δ[1]` is one of the two constant ones. -/
lemma boundaryOne_eq_vertex {m : SimplexCategoryᵒᵖ}
    (x : ((SSet.boundary.{z} 1).toSSet).obj m) :
    x = boundaryOneVertex (m := m) 0 ∨ x = boundaryOneVertex (m := m) 1 := by
  have hx : ¬ Function.Surjective (SSet.stdSimplex.asOrderHom x.1) := x.2
  have hmiss : ∃ i : Fin 2, ∀ j, (SSet.stdSimplex.asOrderHom x.1) j ≠ i := by
    by_contra h
    push Not at h
    exact hx h
  obtain ⟨i, hi⟩ := hmiss
  fin_cases i
  · right
    apply Subtype.ext
    apply SSet.stdSimplex.ext
    intro j
    exact (by decide : ∀ v : Fin 2, v ≠ 0 → v = 1) _ (hi j)
  · left
    apply Subtype.ext
    apply SSet.stdSimplex.ext
    intro j
    exact (by decide : ∀ v : Fin 2, v ≠ 1 → v = 0) _ (hi j)

/-- The two constant simplices of `∂Δ[1]` are distinct. -/
lemma boundaryOneVertex_ne {m : SimplexCategoryᵒᵖ} :
    boundaryOneVertex.{z} (m := m) 0 ≠ boundaryOneVertex.{z} (m := m) 1 := by
  intro h
  have h0 := congrArg (fun x ↦ (SSet.stdSimplex.asOrderHom x.1) (0 : Fin (m.unop.len + 1))) h
  change (0 : Fin 2) = 1 at h0
  exact (by decide : (0 : Fin 2) ≠ 1) h0

end BoundaryOne

/-! ### `Hom(∂Δ[1], L)` is a product of two copies -/

section BoundaryHom

variable {D : Type u'} [Category.{v'} D]

/-- The `Hom` object of natural transformations out of `∂Δ[1]` attached to a pair of morphisms,
by sending the two constant simplices to the two morphisms. -/
noncomputable def boundaryHomObjOfPair {W : SimplicialObject D} (L : SimplicialObject D)
    (p : (W ⟶ L) × (W ⟶ L)) :
    Functor.HomObj W L ((SSet.boundary.{v'} 1).toSSet) := by
  classical
  refine { app := ?_, naturality := ?_ }
  · intro m s
    letI : Decidable (s = boundaryOneVertex (m := m) 0) := Classical.propDecidable _
    exact if s = boundaryOneVertex (m := m) 0 then p.1.app m else p.2.app m
  · intro m m' f s
    rcases boundaryOne_eq_vertex s with hs | hs
    · subst s
      rw [boundaryOne_map_vertex f 0, ite_eq_left rfl, ite_eq_left rfl]
      exact p.1.naturality f
    · subst s
      rw [boundaryOne_map_vertex f 1]
      have hneq : boundaryOneVertex (m := m') 1 ≠ boundaryOneVertex (m := m') 0 :=
        Ne.symm (boundaryOneVertex_ne.{v'} (m := m'))
      have hneq' : boundaryOneVertex (m := m) 1 ≠ boundaryOneVertex (m := m) 0 :=
        Ne.symm (boundaryOneVertex_ne.{v'} (m := m))
      rw [ite_eq_right hneq, ite_eq_right hneq']
      exact p.2.naturality f

/-- A `Hom` object of natural transformations out of `∂Δ[1]` is a pair of morphisms: the values
at the two constant simplices. -/
noncomputable def boundaryHomObjEquiv (W L : SimplicialObject D) :
    Functor.HomObj W L ((SSet.boundary.{v'} 1).toSSet) ≃ (W ⟶ L) × (W ⟶ L) where
  toFun y :=
    ({ app m := y.app m (boundaryOneVertex (m := m) 0)
       naturality := by
         intro m m' f
         have h := y.naturality f (boundaryOneVertex (m := m) 0)
         rw [boundaryOne_map_vertex f 0] at h
         exact h },
     { app m := y.app m (boundaryOneVertex (m := m) 1)
       naturality := by
         intro m m' f
         have h := y.naturality f (boundaryOneVertex (m := m) 1)
         rw [boundaryOne_map_vertex f 1] at h
         exact h })
  invFun := boundaryHomObjOfPair L
  left_inv y := by
    classical
    ext m s
    rcases boundaryOne_eq_vertex s with hs | hs
    · subst s
      simp [boundaryHomObjOfPair]
    · subst s
      simp [boundaryHomObjOfPair, Ne.symm (boundaryOneVertex_ne.{v'} (m := m))]
  right_inv p := by
    rcases p with ⟨f, g⟩
    apply Prod.ext
    · ext m
      simp [boundaryHomObjOfPair]
    · ext m
      simp [boundaryHomObjOfPair, Ne.symm (boundaryOneVertex_ne.{v'} (m := m))]

/-- A morphism into a product of two copies of a simplicial object is a pair of morphisms. -/
noncomputable def homPairEquiv [HasBinaryProducts D] (W L : SimplicialObject D) :
    (W ⟶ L ⨯ L) ≃ (W ⟶ L) × (W ⟶ L) where
  toFun f := (f ≫ prod.fst, f ≫ prod.snd)
  invFun p := prod.lift p.1 p.2
  left_inv f := by apply prod.hom_ext <;> simp
  right_inv p := by apply Prod.ext <;> simp

/-- The identification of `Hom` objects out of `∂Δ[1]` with pairs is natural. -/
lemma boundaryHomObjEquiv_comp {W W' : SimplicialObject D} (L : SimplicialObject D)
    (g : W ⟶ W') (y : Functor.HomObj W' L ((SSet.boundary.{v'} 1).toSSet)) :
    boundaryHomObjEquiv W L ((Functor.HomObj.ofNatTrans g).comp y) =
      (g ≫ (boundaryHomObjEquiv W' L y).1, g ≫ (boundaryHomObjEquiv W' L y).2) := by
  apply Prod.ext <;> ext m <;> rfl

/-- Composing a `Hom` object of natural transformations with a morphism of simplicial objects
corresponds, under the identification with morphisms into the simplicial Hom, to whiskering. -/
lemma functorHomEquiv_eHomWhiskerRight (V : SimplicialObject D) (A : SSet.{v'})
    {W W' : SimplicialObject D} (g : W ⟶ W') (y : A ⟶ SimplicialCategory.sHom W' V) :
    Functor.functorHomEquiv W V A (y ≫ eHomWhiskerRight SSet.{v'} g V) =
      (Functor.HomObj.ofNatTrans g).comp (Functor.functorHomEquiv W' V A y) := by
  apply Functor.HomObj.ext
  funext n a
  rfl

/-- The representing equivalence of a `Hom` object, read through `Functor.functorHomEquiv`, is
natural in the source simplicial object. -/
lemma functorHomEquiv_sHomFunctorMap (A : SSet.{v'}) (V H : SimplicialObject D)
    (hH : SimplicialObject.IsHomFromSSet A V H) {W W' : SimplicialObject D} (g : W ⟶ W')
    (f : W' ⟶ H) :
    Functor.functorHomEquiv W V A
        (((SimplicialCategory.sHomFunctor (SimplicialObject D)).flip.obj V ⋙
          coyoneda.obj (op A)).map g.op (hH.homEquiv f)) =
      (Functor.HomObj.ofNatTrans g).comp
        (Functor.functorHomEquiv W' V A (hH.homEquiv f)) := by
  apply Functor.HomObj.ext
  funext n a
  rfl

variable [HasFiniteLimits D]

/-- **`Hom(∂Δ[1], L) = L × L`.** Restriction to the two vertices of the standard `1`-simplex is
represented by the product of two copies of `L`. -/
noncomputable def boundaryIntervalHomFromSSet (L : SimplicialObject D) :
    SimplicialObject.IsHomFromSSet (SSet.boundary.{v'} 1) L (L ⨯ L) := by
  let S : SSet.{v'} := (SSet.boundary.{v'} 1).toSSet
  let e' : {W : SimplicialObject D} → (W ⟶ L ⨯ L) ≃ Functor.HomObj W L S := fun {W} ↦
    (homPairEquiv W L).trans (boundaryHomObjEquiv W L).symm
  let e : {W : SimplicialObject D} → (W ⟶ L ⨯ L) ≃ (S ⟶ SimplicialCategory.sHom W L) :=
    fun {W} ↦ (e' (W := W)).trans (Functor.functorHomEquiv W L S).symm
  refine { homEquiv := e, homEquiv_comp := ?_ }
  intro W W' g f
  apply (Functor.functorHomEquiv W L S).injective
  change Functor.functorHomEquiv W L S (e (W := W) (g ≫ f)) =
    Functor.functorHomEquiv W L S (e (W := W') f ≫ eHomWhiskerRight SSet.{v'} g L)
  rw [functorHomEquiv_eHomWhiskerRight]
  have he : e' (W := W) (g ≫ f) = (Functor.HomObj.ofNatTrans g).comp (e' (W := W') f) := by
    dsimp [e']
    apply (boundaryHomObjEquiv W L).injective
    rw [boundaryHomObjEquiv_comp]
    have hB := Equiv.apply_symm_apply (boundaryHomObjEquiv W L) ((homPairEquiv W L) (g ≫ f))
    have hB' := Equiv.apply_symm_apply (boundaryHomObjEquiv W' L) ((homPairEquiv W' L) f)
    rw [hB, hB']
    dsimp [homPairEquiv]
    apply Prod.ext <;> ext m <;> simp [Category.assoc]
  dsimp [e]
  calc
    _ = e' (W := W) (g ≫ f) := Equiv.apply_symm_apply _ _
    _ = (Functor.HomObj.ofNatTrans g).comp (e' (W := W') f) := he
    _ = (Functor.HomObj.ofNatTrans g).comp
        (Functor.functorHomEquiv W' L S
          ((Functor.functorHomEquiv W' L S).symm (e' (W := W') f))) := by
      rw [Equiv.apply_symm_apply]

/-- The first component of the representing datum for `Hom(∂Δ[1], L)` is the first product
projection. -/
lemma boundaryIntervalHomFromSSet_vertex_zero (L : SimplicialObject D)
    {W : SimplicialObject D} (f : W ⟶ L ⨯ L) (m : SimplexCategoryᵒᵖ) :
    (Functor.functorHomEquiv W L ((SSet.boundary.{v'} 1).toSSet)
      ((boundaryIntervalHomFromSSet L).homEquiv f)).app m
      (boundaryOneVertex (m := m) 0) = (f ≫ prod.fst).app m := by
  change ((boundaryHomObjEquiv W L).symm ((homPairEquiv W L) f)).app m
    (boundaryOneVertex (m := m) 0) = (f ≫ prod.fst).app m
  simp [boundaryHomObjEquiv, boundaryHomObjOfPair, homPairEquiv]

/-- The second component of the representing datum for `Hom(∂Δ[1], L)` is the second product
projection. -/
lemma boundaryIntervalHomFromSSet_vertex_one (L : SimplicialObject D)
    {W : SimplicialObject D} (f : W ⟶ L ⨯ L) (m : SimplexCategoryᵒᵖ) :
    (Functor.functorHomEquiv W L ((SSet.boundary.{v'} 1).toSSet)
      ((boundaryIntervalHomFromSSet L).homEquiv f)).app m
      (boundaryOneVertex (m := m) 1) = (f ≫ prod.snd).app m := by
  change ((boundaryHomObjEquiv W L).symm ((homPairEquiv W L) f)).app m
    (boundaryOneVertex (m := m) 1) = (f ≫ prod.snd).app m
  have hneq : boundaryOneVertex (m := m) 1 ≠ boundaryOneVertex (m := m) 0 :=
    Ne.symm (boundaryOneVertex_ne.{v'} (m := m))
  simp [boundaryHomObjEquiv, boundaryHomObjOfPair, homPairEquiv, hneq]

/-- A morphism `H ⟶ L ⨯ L` whose two components are the evaluations of the universal
`Δ[1]`-datum at the two vertices is the restriction of that datum along the boundary
inclusion. -/
lemma intervalEndpointMap_boundary_restriction (L H : SimplicialObject D)
    (hH : SimplicialObject.IsHomFromSSet Δ[1] L H) (e : H ⟶ L ⨯ L)
    (he₀ : ∀ m : SimplexCategoryᵒᵖ, (e ≫ prod.fst).app m =
      (Functor.functorHomEquiv H L Δ[1] (hH.homEquiv (𝟙 H))).app m
        (SSet.stdSimplex.const 1 0 m))
    (he₁ : ∀ m : SimplexCategoryᵒᵖ, (e ≫ prod.snd).app m =
      (Functor.functorHomEquiv H L Δ[1] (hH.homEquiv (𝟙 H))).app m
        (SSet.stdSimplex.const 1 1 m)) :
    (boundaryIntervalHomFromSSet L).homEquiv e =
      (SSet.boundary.{v'} 1).ι ≫ hH.homEquiv (𝟙 H) := by
  apply (Functor.functorHomEquiv H L ((SSet.boundary.{v'} 1).toSSet)).injective
  apply Functor.HomObj.ext
  funext m s
  rcases boundaryOne_eq_vertex s with rfl | rfl
  · exact (boundaryIntervalHomFromSSet_vertex_zero L e m).trans (he₀ m)
  · exact (boundaryIntervalHomFromSSet_vertex_one L e m).trans (he₁ m)

end BoundaryHom

/-! ### Points of a Hom object -/

section Points

variable {D : Type u'} [Category.{v'} D]

/-- Morphisms into a `Hom` object, as `Hom` objects of natural transformations. -/
noncomputable def homFromSSetHomObjEquiv (A : SSet.{v'}) (L H : SimplicialObject D)
    (hH : SimplicialObject.IsHomFromSSet A L H) (W : SimplicialObject D) :
    (W ⟶ H) ≃ Functor.HomObj W L A where
  toFun f := Functor.functorHomEquiv W L A (hH.homEquiv f)
  invFun y := hH.homEquiv.symm ((Functor.functorHomEquiv W L A).symm y)
  left_inv f := by
    calc
      hH.homEquiv.symm
          ((Functor.functorHomEquiv W L A).symm
            (Functor.functorHomEquiv W L A (hH.homEquiv f))) =
          hH.homEquiv.symm (hH.homEquiv f) :=
        congrArg hH.homEquiv.symm ((Functor.functorHomEquiv W L A).symm_apply_apply _)
      _ = f := hH.homEquiv.symm_apply_apply f
  right_inv y := by
    calc
      Functor.functorHomEquiv W L A
          (hH.homEquiv (hH.homEquiv.symm ((Functor.functorHomEquiv W L A).symm y))) =
          Functor.functorHomEquiv W L A ((Functor.functorHomEquiv W L A).symm y) :=
        congrArg (Functor.functorHomEquiv W L A)
          (hH.homEquiv.apply_symm_apply ((Functor.functorHomEquiv W L A).symm y))
      _ = y := (Functor.functorHomEquiv W L A).apply_symm_apply y

/-- The identification of morphisms into a `Hom` object with `Hom` objects of natural
transformations is natural in the source. -/
lemma homFromSSetHomObjEquiv_comp (A : SSet.{v'}) (L H : SimplicialObject D)
    (hH : SimplicialObject.IsHomFromSSet A L H) {W W' : SimplicialObject D} (g : W ⟶ W')
    (f : W' ⟶ H) :
    homFromSSetHomObjEquiv A L H hH W (g ≫ f) =
      (Functor.HomObj.ofNatTrans g).comp (homFromSSetHomObjEquiv A L H hH W' f) := by
  change Functor.functorHomEquiv W L A (hH.homEquiv (g ≫ f)) =
    (Functor.HomObj.ofNatTrans g).comp (Functor.functorHomEquiv W' L A (hH.homEquiv f))
  calc
    _ = Functor.functorHomEquiv W L A
        (((SimplicialCategory.sHomFunctor (SimplicialObject D)).flip.obj L ⋙
          coyoneda.obj (op A)).map g.op (hH.homEquiv f)) := by rw [hH.homEquiv_comp]
    _ = _ := functorHomEquiv_sHomFunctorMap A L H hH g f

/-- A morphism into a `Hom` object is the universal one precomposed with it. -/
private lemma homFromSSetHomObjEquiv_eq_comp_id (A : SSet.{v'}) (L H : SimplicialObject D)
    (hH : SimplicialObject.IsHomFromSSet A L H) {W : SimplicialObject D} (f : W ⟶ H) :
    homFromSSetHomObjEquiv A L H hH W f =
      (Functor.HomObj.ofNatTrans f).comp (homFromSSetHomObjEquiv A L H hH H (𝟙 H)) := by
  simpa using homFromSSetHomObjEquiv_comp A L H hH f (𝟙 H)

/-- A `Hom` object of natural transformations out of a copower by `T` is a `Hom` object out of
the tensor product by `T`. -/
noncomputable def copowerHomObjEquiv (X : D) (T A : SSet.{v'}) (L : SimplicialObject D)
    [∀ m, HasCoproduct (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m)] :
    Functor.HomObj (((SimplicialObject.const D).obj X).copower T) L A ≃
      Functor.HomObj ((SimplicialObject.const D).obj X) L (T ⊗ A) where
  toFun y :=
    { app := fun m ta ↦ Sigma.ι
        (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) ta.1 ≫ y.app m ta.2
      naturality := by
        intro m m' f ⟨t, a⟩
        change ((SimplicialObject.const D).obj X).map f ≫
            Sigma.ι (fun _ : T.obj m' => ((SimplicialObject.const D).obj X).obj m')
              (T.map f t) ≫ y.app m' (A.map f a) =
            (Sigma.ι (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) t ≫
              y.app m a) ≫ L.map f
        calc
          _ = Sigma.ι (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) t ≫
              (((SimplicialObject.const D).obj X).copower T).map f ≫ y.app m' (A.map f a) := by
                simp
          _ = Sigma.ι (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) t ≫
                y.app m a ≫ L.map f := by
            rw [← y.naturality f a]
          _ = (Sigma.ι (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) t ≫
                y.app m a) ≫ L.map f := by simp }
  invFun y :=
    { app := fun m a ↦ Sigma.desc (fun t ↦ y.app m (t, a))
      naturality := by
        intro m m' f a
        change (((SimplicialObject.const D).obj X).copower T).map f ≫
            Sigma.desc (fun t ↦ y.app m' (t, A.map f a)) =
          Sigma.desc (fun t ↦ y.app m (t, a)) ≫ L.map f
        apply Sigma.hom_ext
        intro t
        have hmap : (T ⊗ A).map f (t, a) = (T.map f t, A.map f a) := rfl
        calc
          Sigma.ι (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) t ≫
              (((SimplicialObject.const D).obj X).copower T).map f ≫
              Sigma.desc (fun t ↦ y.app m' (t, A.map f a)) =
            ((SimplicialObject.const D).obj X).map f ≫
              Sigma.ι (fun _ : T.obj m' => ((SimplicialObject.const D).obj X).obj m')
                (T.map f t) ≫ Sigma.desc (fun t ↦ y.app m' (t, A.map f a)) := by
              simp
          _ = y.app m' (T.map f t, A.map f a) := by simp
          _ = y.app m (t, a) ≫ L.map f := by
            rw [← hmap]
            simpa using y.naturality f (t, a)
          _ = Sigma.ι (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) t ≫
                Sigma.desc (fun t ↦ y.app m (t, a)) ≫ L.map f := by simp }
  left_inv y := by
    apply Functor.HomObj.ext
    funext m a
    apply Sigma.hom_ext
    intro t
    simp
  right_inv y := by
    apply Functor.HomObj.ext
    funext m
    funext ta
    rcases ta with ⟨t, a⟩
    simp

/-- The universal property of the copower by a simplicial set: morphisms out of
`X ⊗ T` into `K` are morphisms of simplicial sets `T ⟶ K ⋙ Mor(X, -)`. -/
noncomputable def sSetMapCopowerEquiv (X : D) (T : SSet.{v'}) (K : SimplicialObject D)
    [∀ m, HasCoproduct (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m)] :
    (T ⟶ K ⋙ coyoneda.obj (op X)) ≃
      (((SimplicialObject.const D).obj X).copower T ⟶ K) where
  toFun y :=
    { app := fun m ↦ Sigma.desc (fun t ↦ y.app m t)
      naturality := by
        intro m m' f
        apply Sigma.hom_ext
        intro t
        calc
          Sigma.ι (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) t ≫
              (((SimplicialObject.const D).obj X).copower T).map f ≫
              Sigma.desc (fun t ↦ y.app m' t) = y.app m' (T.map f t) := by
            simp
          _ = y.app m t ≫ K.map f := by
            simp
          _ = Sigma.ι (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) t ≫
                Sigma.desc (fun t ↦ y.app m t) ≫ K.map f := by simp }
  invFun g :=
    { app := fun m ↦ ↾fun t ↦ Sigma.ι
        (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) t ≫ g.app m
      naturality := by
        intro m m' f
        ext t
        have h := congrArg (fun q ↦ Sigma.ι
          (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) t ≫ q)
          (g.naturality f)
        simpa [Category.assoc] using h }
  left_inv y := by
    ext m t
    simp
  right_inv g := by
    ext m
    apply Sigma.hom_ext
    intro t
    simp

/-- `T`-points of `Hom(A, L)` are points of `Hom(A ⊗ T, L)`. -/
noncomputable def homFromSSetPointsEquiv (A T : SSet.{v'}) (L H : SimplicialObject D)
    (hH : SimplicialObject.IsHomFromSSet A L H) (X : D)
    [∀ m, HasCoproduct (fun _ : T.obj m => X)] :
    (T ⟶ H ⋙ coyoneda.obj (op X)) ≃ (A ⊗ T ⟶ L ⋙ coyoneda.obj (op X)) := by
  letI : ∀ m, HasCoproduct
      (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) := fun m ↦ by
    simpa using (inferInstance : HasCoproduct (fun _ : T.obj m => X))
  let W := ((SimplicialObject.const D).obj X).copower T
  let e₆ : (T ⊗ A ⟶ L ⋙ coyoneda.obj (op X)) ≃ (A ⊗ T ⟶ L ⋙ coyoneda.obj (op X)) :=
    { toFun := fun f ↦ (β_ A T).hom ≫ f
      invFun := fun f ↦ (β_ A T).inv ≫ f
      left_inv := by intro f; simp
      right_inv := by intro f; simp }
  exact (sSetMapCopowerEquiv X T H).trans
    ((homFromSSetHomObjEquiv A L H hH W).trans
      ((copowerHomObjEquiv X T A L).trans ((constHomObjEquiv (T ⊗ A) L X).trans e₆)))

/-- The coproducts over the simplices of `T` of the constant simplicial object at `X` exist as
soon as the coproducts of copies of `X` do. -/
private lemma hasCoproduct_const_obj {D : Type u'} [Category.{v'} D] (T : SSet.{v'}) (X : D)
    [∀ m, HasCoproduct (fun _ : T.obj m => X)] :
    ∀ m, HasCoproduct (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m) :=
  fun m ↦ by simpa using (inferInstance : HasCoproduct (fun _ : T.obj m => X))

/-- The identification of points is computed by the copower inclusions. -/
lemma homFromSSetPointsEquiv_app {A T : SSet.{v'}} (L H : SimplicialObject D)
    (hH : SimplicialObject.IsHomFromSSet A L H) (X : D)
    [∀ m, HasCoproduct (fun _ : T.obj m => X)]
    [∀ m, HasCoproduct (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m)]
    (g : T ⟶ H ⋙ coyoneda.obj (op X)) {k : SimplexCategoryᵒᵖ} (a : A.obj k) (t : T.obj k) :
    (homFromSSetPointsEquiv A T L H hH X g).app k (a, t) =
      Sigma.ι (fun _ : T.obj k => ((SimplicialObject.const D).obj X).obj k) t ≫
        (Functor.functorHomEquiv (((SimplicialObject.const D).obj X).copower T) L A
          (hH.homEquiv (sSetMapCopowerEquiv X T H g))).app k a := by
  simp [homFromSSetPointsEquiv, sSetMapCopowerEquiv, homFromSSetHomObjEquiv,
    copowerHomObjEquiv, constHomObjEquiv]
  rfl

/-- The copower-to-tensor identification of `Hom` objects is natural in the object. -/
lemma copowerHomObjEquiv_comp (X Y : D) (f : X ⟶ Y) (T A : SSet.{v'}) (L : SimplicialObject D)
    [∀ m, HasCoproduct (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m)]
    [∀ m, HasCoproduct (fun _ : T.obj m => ((SimplicialObject.const D).obj Y).obj m)]
    (y : Functor.HomObj (((SimplicialObject.const D).obj Y).copower T) L A) :
    copowerHomObjEquiv X T A L
        ((Functor.HomObj.ofNatTrans
          (Functor.copowerMap ((SimplicialObject.const D).map f) (𝟙 T))).comp y) =
      (Functor.HomObj.ofNatTrans ((SimplicialObject.const D).map f)).comp
        (copowerHomObjEquiv Y T A L y) := by
  ext m ⟨t, a⟩
  simp [copowerHomObjEquiv, Functor.HomObj.ofNatTrans, Functor.HomObj.comp,
    Functor.copowerMap]

/-- The universal property of the copower is natural in the object. -/
lemma sSetMapCopowerEquiv_comp (X Y : D) (f : X ⟶ Y) (T : SSet.{v'}) (K : SimplicialObject D)
    [∀ m, HasCoproduct (fun _ : T.obj m => ((SimplicialObject.const D).obj X).obj m)]
    [∀ m, HasCoproduct (fun _ : T.obj m => ((SimplicialObject.const D).obj Y).obj m)]
    (g : T ⟶ K ⋙ coyoneda.obj (op Y)) :
    sSetMapCopowerEquiv X T K (g ≫ Functor.whiskerLeft K (coyoneda.map f.op)) =
      Functor.copowerMap ((SimplicialObject.const D).map f) (𝟙 T) ≫
        sSetMapCopowerEquiv Y T K g := by
  ext m
  apply Sigma.hom_ext
  intro t
  simp [sSetMapCopowerEquiv, Functor.copowerMap]

/-- The degree-zero identification of `Hom` objects of natural transformations out of a
constant simplicial object is natural in the object. -/
lemma constHomObjEquiv_comp (B : SSet.{v'}) (L : SimplicialObject D) {X Y : D} (f : X ⟶ Y)
    (y : Functor.HomObj ((SimplicialObject.const D).obj Y) L B) :
    constHomObjEquiv B L X
        ((Functor.HomObj.ofNatTrans ((SimplicialObject.const D).map f)).comp y) =
      constHomObjEquiv B L Y y ≫ Functor.whiskerLeft L (coyoneda.map f.op) := by
  ext m b
  rfl

/-- The identification of points is natural in the object of `D`. -/
lemma homFromSSetPointsEquiv_comp (A T : SSet.{v'}) (L H : SimplicialObject D)
    (hH : SimplicialObject.IsHomFromSSet A L H) {X Y : D} (f : X ⟶ Y)
    [∀ m, HasCoproduct (fun _ : T.obj m => X)] [∀ m, HasCoproduct (fun _ : T.obj m => Y)]
    (g : T ⟶ H ⋙ coyoneda.obj (op Y)) :
    homFromSSetPointsEquiv A T L H hH X (g ≫ Functor.whiskerLeft H (coyoneda.map f.op)) =
      homFromSSetPointsEquiv A T L H hH Y g ≫ Functor.whiskerLeft L (coyoneda.map f.op) := by
  have := hasCoproduct_const_obj T X
  have := hasCoproduct_const_obj T Y
  unfold homFromSSetPointsEquiv
  simp only [Equiv.trans_apply]
  rw [sSetMapCopowerEquiv_comp, homFromSSetHomObjEquiv_comp, copowerHomObjEquiv_comp,
    constHomObjEquiv_comp]
  ext m ⟨a, t⟩
  simp [Category.assoc]

/-- The identification of points, computed on a single point. -/
lemma homFromSSetPointsEquiv_apply {A T : SSet.{v'}} {L H : SimplicialObject D}
    (hH : SimplicialObject.IsHomFromSSet A L H) (X : D)
    [∀ m, HasCoproduct (fun _ : T.obj m => X)] (g : T ⟶ H ⋙ coyoneda.obj (op X))
    (k : SimplexCategoryᵒᵖ) (a : A.obj k) (t : T.obj k) :
    (homFromSSetPointsEquiv A T L H hH X g).app k (a, t) =
      g.app k t ≫ (homFromSSetHomObjEquiv A L H hH H (𝟙 H)).app k a := by
  have := hasCoproduct_const_obj T X
  rw [homFromSSetPointsEquiv_app]
  change _ ≫ (homFromSSetHomObjEquiv A L H hH _ (sSetMapCopowerEquiv X T H g)).app k a = _
  rw [homFromSSetHomObjEquiv_eq_comp_id]
  change _ ≫ ((sSetMapCopowerEquiv X T H g).app k ≫ _) = _
  simp [sSetMapCopowerEquiv, ← Category.assoc]

/-- The identification of points is natural in the simplicial set `T`. -/
lemma homFromSSetPointsEquiv_precomp {A T T' : SSet.{v'}} {L H : SimplicialObject D}
    (hH : SimplicialObject.IsHomFromSSet A L H) (X : D)
    [∀ m, HasCoproduct (fun _ : T.obj m => X)] [∀ m, HasCoproduct (fun _ : T'.obj m => X)]
    (f : T' ⟶ T) (g : T ⟶ H ⋙ coyoneda.obj (op X)) :
    homFromSSetPointsEquiv A T' L H hH X (f ≫ g) =
      (A ◁ f) ≫ homFromSSetPointsEquiv A T L H hH X g := by
  ext k ⟨a, t⟩
  change (homFromSSetPointsEquiv A T' L H hH X (f ≫ g)).app k (a, t) =
    (homFromSSetPointsEquiv A T L H hH X g).app k (a, f.app k t)
  simp only [homFromSSetPointsEquiv_apply, NatTrans.comp_app, comp_apply]

/-- The identification of points is natural in the `Hom` object: restricting the representing
datum along `i : B ⟶ A` corresponds to restricting along `i ▷ T`. -/
lemma homFromSSetPointsEquiv_restriction {A B T : SSet.{v'}} {L H K : SimplicialObject D}
    (hH : SimplicialObject.IsHomFromSSet A L H) (hK : SimplicialObject.IsHomFromSSet B L K)
    (i : B ⟶ A) (e : H ⟶ K) (he : hK.homEquiv e = i ≫ hH.homEquiv (𝟙 H)) (X : D)
    [∀ m, HasCoproduct (fun _ : T.obj m => X)] (g : T ⟶ H ⋙ coyoneda.obj (op X)) :
    homFromSSetPointsEquiv B T L K hK X
        (g ≫ Functor.whiskerRight e (coyoneda.obj (op X))) =
      (i ▷ T) ≫ homFromSSetPointsEquiv A T L H hH X g := by
  have hh := homFromSSetHomObjEquiv_eq_comp_id B L K hK e
  have hh' : homFromSSetHomObjEquiv B L K hK H e =
      Functor.functorHomEquiv H L B (i ≫ hH.homEquiv (𝟙 H)) :=
    congrArg (Functor.functorHomEquiv H L B) he
  ext k ⟨b, t⟩
  change (homFromSSetPointsEquiv B T L K hK X
    (g ≫ Functor.whiskerRight e (coyoneda.obj (op X)))).app k (b, t) =
      (homFromSSetPointsEquiv A T L H hH X g).app k (i.app k b, t)
  rw [homFromSSetPointsEquiv_apply, homFromSSetPointsEquiv_apply]
  have hcomp := congrArg (fun y ↦ y.app k b) (hh.symm.trans hh')
  change e.app k ≫ (homFromSSetHomObjEquiv B L K hK K (𝟙 K)).app k b =
    (homFromSSetHomObjEquiv A L H hH H (𝟙 H)).app k (i.app k b) at hcomp
  change (g.app k t ≫ e.app k) ≫ _ = _
  rw [Category.assoc, hcomp]

/-- The presheaf of simplicial sets attached to a simplicial object: `Y ↦ L ⋙ Mor(Y, -)`. -/
abbrev pointwisePresheaf (V : SimplicialObject D) : Dᵒᵖ ⥤ SSet.{v'} :=
  coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ D (Type v')).obj V

/-- An object representing the `T`-points of `Hom(A, L)` represents the points of
`Hom(A ⊗ T, L)`. -/
noncomputable def representableBy_homFromSSetPoints {A T : SSet.{v'}}
    {L H : SimplicialObject D} (hH : SimplicialObject.IsHomFromSSet A L H)
    [∀ X : D, ∀ m, HasCoproduct (fun _ : T.obj m => X)] {R : D}
    (hBase : (pointwisePresheaf H ⋙ coyoneda.obj (op T)).RepresentableBy R) :
    (pointwisePresheaf L ⋙ coyoneda.obj (op (A ⊗ T))).RepresentableBy R where
  homEquiv {X} := hBase.homEquiv.trans (homFromSSetPointsEquiv A T L H hH X)
  homEquiv_comp {X Y} f g := by
    simp only [Equiv.trans_apply]
    rw [hBase.homEquiv_comp]
    exact homFromSSetPointsEquiv_comp A T L H hH f (hBase.homEquiv g)

end Points

/-! ### Naturality of the representing data in the simplicial object -/

section Naturality

variable {D : Type u'} [Category.{v'} D]

/-- The representing datum `L_m` for `Hom(Δ[m], L)` is natural in `L`. -/
lemma representableByStdSimplex_postcomp (m : ℕ) {H K : SimplicialObject D} (e : H ⟶ K) (X : D)
    (g : X ⟶ H _⦋m⦌) :
    (representableByStdSimplex K m).homEquiv (g ≫ e.app (op ⦋m⦌)) =
      (representableByStdSimplex H m).homEquiv g ≫
        Functor.whiskerRight e (coyoneda.obj (op X)) :=
  (SSet.yonedaEquiv_symm_comp g (Functor.whiskerRight e (coyoneda.obj (op X)))).symm

variable (n : ℕ)
  [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ D,
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]

/-- The interchange law between the coskeleton counit and a morphism of simplicial objects. -/
lemma matchingCoyonedaCounit_postcomp {H K : SimplicialObject D} (e : H ⟶ K) (X : D) :
    Functor.whiskerLeft (SimplexCategory.Truncated.inclusion n).op
        (Functor.whiskerRight ((SimplicialObject.cosk n).map e) (coyoneda.obj (op X))) ≫
      matchingCoyonedaCounit K n X =
    matchingCoyonedaCounit H n X ≫
      Functor.whiskerRight ((SimplicialObject.truncation n).map e) (coyoneda.obj (op X)) := by
  ext m f
  have h := NatTrans.congr_app
    ((SimplicialObject.coskAdj n).counit.naturality ((SimplicialObject.truncation n).map e)) m
  change (f ≫ ((SimplicialObject.cosk n).map e).app
      ((SimplexCategory.Truncated.inclusion n).op.obj m)) ≫
      ((SimplicialObject.coskAdj n).counit.app
        ((SimplicialObject.truncation n).obj K)).app m =
    (f ≫ ((SimplicialObject.coskAdj n).counit.app
      ((SimplicialObject.truncation n).obj H)).app m) ≫
      ((SimplicialObject.truncation n).map e).app m
  change ((SimplicialObject.cosk n).map e).app
      ((SimplexCategory.Truncated.inclusion n).op.obj m) ≫
      ((SimplicialObject.coskAdj n).counit.app
        ((SimplicialObject.truncation n).obj K)).app m =
    ((SimplicialObject.coskAdj n).counit.app
      ((SimplicialObject.truncation n).obj H)).app m ≫
      ((SimplicialObject.truncation n).map e).app m at h
  exact (Category.assoc _ _ _).trans
    ((congrArg (f ≫ ·) h).trans (Category.assoc _ _ _).symm)

/-- The bijection of `matchingSkeletonHomEquiv` is natural in the simplicial object. -/
lemma matchingSkeletonHomEquiv_postcomp {H K : SimplicialObject D} (e : H ⟶ K) (X : D)
    (g : X ⟶ ((SimplicialObject.cosk n).obj H) _⦋n + 1⦌) :
    matchingSkeletonHomEquiv K n X (g ≫ ((SimplicialObject.cosk n).map e).app (op ⦋n + 1⦌)) =
      matchingSkeletonHomEquiv H n X g ≫ Functor.whiskerRight e (coyoneda.obj (op X)) := by
  have hy : SSet.yonedaEquiv.symm
      (g ≫ ((SimplicialObject.cosk n).map e).app (op ⦋n + 1⦌)) =
      SSet.yonedaEquiv.symm g ≫
        Functor.whiskerRight ((SimplicialObject.cosk n).map e) (coyoneda.obj (op X)) := by
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  refine Eq.trans (congrArg ((SSet.skAdj n).homEquiv
    ((SSet.truncation n).obj (Δ[n + 1] : SSet.{v'}))
    (K ⋙ coyoneda.obj (op X))).symm ?_)
    ((SSet.skAdj n).homEquiv_naturality_right_symm _ _)
  rw [hy]
  exact rightKanHomEquiv_naturality_right (matchingCoyonedaCounit_postcomp n e X) _ _

/-- The representing datum of the matching object `(cosk_n L)_{n + 1}` for
`Hom(∂Δ[n + 1], L)` is natural in `L`. -/
lemma representableByBoundarySucc_postcomp {H K : SimplicialObject D} (e : H ⟶ K) (X : D)
    (g : X ⟶ ((SimplicialObject.cosk n).obj H) _⦋n + 1⦌) :
    (representableByBoundarySucc K n).homEquiv
        (g ≫ ((SimplicialObject.cosk n).map e).app (op ⦋n + 1⦌)) =
      (representableByBoundarySucc H n).homEquiv g ≫
        Functor.whiskerRight e (coyoneda.obj (op X)) := by
  change (SSet.skObjStdSimplexIsoBoundary n).inv ≫ matchingSkeletonHomEquiv K n X _ = _
  rw [matchingSkeletonHomEquiv_postcomp]
  rfl

end Naturality

/-- Restriction morphisms between representing objects compose. -/
lemma representedRestriction_comp {D : Type u'} [Category.{v'} D] (F : Dᵒᵖ ⥤ SSet.{v'})
    {A B E : SSet.{v'}} {R₁ R₂ R₃ : D}
    (h₁ : (F ⋙ coyoneda.obj (op A)).RepresentableBy R₁)
    (h₂ : (F ⋙ coyoneda.obj (op B)).RepresentableBy R₂)
    (h₃ : (F ⋙ coyoneda.obj (op E)).RepresentableBy R₃) (i : B ⟶ A) (j : E ⟶ B) :
    h₂.homEquiv.symm (i ≫ h₁.homEquiv (𝟙 R₁)) ≫
        h₃.homEquiv.symm (j ≫ h₂.homEquiv (𝟙 R₂)) =
      h₃.homEquiv.symm ((j ≫ i) ≫ h₁.homEquiv (𝟙 R₁)) := by
  apply h₃.homEquiv.injective
  rw [h₃.homEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change (j ≫ h₂.homEquiv (𝟙 R₂)) ≫ F.map _ = _
  rw [Category.assoc]
  have h := h₂.homEquiv_eq (h₂.homEquiv.symm (i ≫ h₁.homEquiv (𝟙 R₁)))
  change _ = h₂.homEquiv (𝟙 R₂) ≫ F.map _ at h
  rw [← h, Equiv.apply_symm_apply, Category.assoc]

end Stacks.CategoryTheory.Hypercovering

end
