module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex

/-!
# The canonical map `G ⊗ f_*N ⟶ f_*(f^*G ⊗ N)` as a natural transformation of bifunctors

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi. The canonical map
`G ⊗_{𝒪'} f_*N ⟶ f_*(f^*G ⊗_𝒪 N)` of Stacks 04G0 and 0DK4,
`Stacks.SheafOfModules.pushforwardTensorMap`, is natural in both variables. This file records its
naturality at the curried tensor bifunctor of Tag 06YM,
`Stacks.SheafOfModules.Tensor.sheafTensor`, through which total tensor complexes are formed, and
assembles it into a natural transformation of bifunctors, the form in which it is applied
termwise to complexes.

## Main definitions

* `Stacks.SheafOfModules.pushforwardTensorBifunctorNatTrans`: the natural transformation
  `(G, N) ↦ G ⊗ f_*N ⟶ (G, N) ↦ f_*(f^*G ⊗ N)`, natural in both variables. For a fixed
  second module `N`, the transformation natural in the first variable alone is
  `Stacks.SheafOfModules.pushforwardTensorNatTrans` (in `PushforwardTensorRowComplex`).

## Main results

* `Stacks.SheafOfModules.pushforwardTensorMap_naturality_right`,
  `Stacks.SheafOfModules.pushforwardTensorMap_naturality_left`: naturality in each variable at
  the curried tensor bifunctor.

## References

* [Stacks Project, Tag 0DK4](https://stacks.math.columbia.edu/tag/0DK4)
* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' v u v' u'

namespace Stacks.SheafOfModules

open Stacks.Sheaves.RingedToposModules

section Curried

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

/-- The canonical map `G ⊗ f_*N ⟶ f_*(f^*G ⊗ N)` is natural in the second module, at the
curried tensor bifunctor of Tag 06YM. -/
@[reassoc]
lemma pushforwardTensorMap_naturality_right
    (G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {N N' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : N ⟶ N') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj G).map ((pushforwardModules f).map g) ≫
        pushforwardTensorMap f G N' =
      pushforwardTensorMap f G N ≫ (pushforwardModules f).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          ((f.pullbackModules).obj G)).map g) := by
  refine Eq.trans ?_ ((pushforwardTensorMap_natural f (𝟙 G) g).trans ?_)
  · exact congrArg (· ≫ _) (tensorSheafBifunctor_map_id_fst Y.O G _).symm
  · refine congrArg (fun t => _ ≫ (pushforwardModules f).map t)
      (Eq.trans ?_ (tensorSheafBifunctor_map_id_fst X.O _ g))
    exact congrArg (fun k =>
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).map
        ((k, g) : (((f.pullbackModules).obj G, N) : _ × _) ⟶ ((f.pullbackModules).obj G, N')))
      ((f.pullbackModules).map_id G)

/-- The canonical map `G ⊗ f_*N ⟶ f_*(f^*G ⊗ N)` is natural in the first module, at the
curried tensor bifunctor of Tag 06YM. -/
@[reassoc]
lemma pushforwardTensorMap_naturality_left
    {G G' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (k : G ⟶ G') (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map k).app ((pushforwardModules f).obj N) ≫
        pushforwardTensorMap f G' N =
      pushforwardTensorMap f G N ≫ (pushforwardModules f).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
          ((f.pullbackModules).map k)).app N) := by
  refine Eq.trans ?_ ((pushforwardTensorMap_natural f k (𝟙 N)).trans ?_)
  · refine congrArg (· ≫ _) ((tensorSheafBifunctor_map_id_snd Y.O k _).symm.trans ?_)
    exact congrArg (fun t =>
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)).map
        ((k, t) : ((G, (pushforwardModules f).obj N) : _ × _) ⟶
          (G', (pushforwardModules f).obj N))) ((pushforwardModules f).map_id N).symm
  · refine congrArg (fun t => _ ≫ (pushforwardModules f).map t)
      (tensorSheafBifunctor_map_id_snd X.O _ N)

/-- The canonical map `G ⊗ f_*N ⟶ f_*(f^*G ⊗ N)` of Stacks 04G0 and 0DK4 as a natural
transformation of bifunctors `(G, N) ↦ G ⊗ f_*N ⟶ (G, N) ↦ f_*(f^*G ⊗ N)`, at the curried
tensor bifunctor of Tag 06YM. -/
def pushforwardTensorBifunctorNatTrans :
    Stacks.SheafOfModules.Tensor.sheafTensor Y.O ⋙
        (Functor.whiskeringLeft _ _ _).obj (pushforwardModules f) ⟶
      f.pullbackModules ⋙ Stacks.SheafOfModules.Tensor.sheafTensor X.O ⋙
        (Functor.whiskeringRight _ _ _).obj (pushforwardModules f) where
  app G :=
    { app N := pushforwardTensorMap f G N
      naturality _ _ g := pushforwardTensorMap_naturality_right f G g }
  naturality _ _ k := NatTrans.ext (funext fun N => pushforwardTensorMap_naturality_left f k N)

/-- The component of `pushforwardTensorBifunctorNatTrans f` at `(G, N)` is
`pushforwardTensorMap f G N`. -/
@[simp]
lemma pushforwardTensorBifunctorNatTrans_app_app
    (G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((pushforwardTensorBifunctorNatTrans f).app G).app N = pushforwardTensorMap f G N :=
  rfl

end Curried

end Stacks.SheafOfModules

end
