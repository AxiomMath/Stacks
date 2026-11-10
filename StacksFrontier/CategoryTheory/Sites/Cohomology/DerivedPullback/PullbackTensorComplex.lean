module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.ExactnessOfPullback
public import StacksCore.Tactic.StacksAttribute

/-! # Pullback commutes with the total tensor complex

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi and let `K`, `L` be cochain
complexes of `O'`-modules. The total complex of the tensor double complex of `K` and `L` has a
canonical comparison with the one formed from the pullbacks,

`f^*Tot(K ⊗_{O'} L) ≅ Tot(f^*K ⊗_O f^*L)`,

whose component on the summand of bidegree `(p, q)` is the comparison
`f^*(K^p ⊗_{O'} L^q) ≅ f^*K^p ⊗_O f^*L^q` of **Stacks 03EL**. No boundedness or finiteness
hypothesis is made on `K` or `L`.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.pullbackTensorBicomplexIso`: the comparison of the two
  bicomplexes `(p, q) ↦ f^*(K^p ⊗ L^q)` and `(p, q) ↦ f^*K^p ⊗ f^*L^q`, given by Stacks 03EL in
  each bidegree.
* `Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso`: the comparison
  `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)` of total complexes.

## Main results

* `Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_fst`,
  `Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_snd` and
  `Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_map`: the naturality of Stacks 03EL,
  stated with the curried tensor bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`.
* `Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_hom`: the comparison of total
  complexes acts on the summand of bidegree `(p, q)` by the comparison of Stacks 03EL.
* `Stacks.Sheaves.DerivedPullback.pullbackTensorBicomplexIso_naturality`: the bicomplex
  comparison is natural in the pair of complexes.
* `Stacks.Sheaves.DerivedPullback.hom_ext_pullbackTotal`: two morphisms out of
  `f^*Tot(K ⊗ L)` in one degree agree as soon as they agree on each `f^*`-image of a summand.

## Implementation notes

Stacks 03EL is stated with the uncurried tensor bifunctor, which spells the action on morphisms
`𝟙 A ⊗ₘ b`, while `HomologicalComplex.mapBifunctor` uses the curried
`Stacks.SheafOfModules.Tensor.sheafTensor`, which spells it `A ◁ b`. Identifying the two by `rfl`
unfolds the monoidal structure on presheaves of modules and exhausts the heartbeat budget; the
lemmas `Stacks.SheafOfModules.tensorSheafBifunctor_map_id_fst`,
`Stacks.SheafOfModules.tensorSheafBifunctor_map_id_snd` and
`Stacks.SheafOfModules.tensorSheafBifunctor_map_eq` are to be used instead.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

namespace Stacks.SheafOfModules

/-! ## The curried and the uncurried tensor bifunctor -/

section Bridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

/-- Tensoring on the right by a morphism, read off the uncurried tensor bifunctor, is the
action of the curried tensor bifunctor of Tag 06YM on that morphism. -/
lemma tensorSheafBifunctor_map_id_fst
    (A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} O))
    {B B' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} O)} (b : B ⟶ B') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O)).map
        ((𝟙 A, b) : ((A, B) : _ × _) ⟶ (A, B')) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj A).map b :=
  Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map O (𝟙 A) b

/-- Tensoring on the left by a morphism, read off the uncurried tensor bifunctor, is the action
of the curried tensor bifunctor of Tag 06YM on that morphism. -/
lemma tensorSheafBifunctor_map_id_snd
    {A A' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} O)} (a : A ⟶ A')
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} O)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O)).map
        ((a, 𝟙 B) : ((A, B) : _ × _) ⟶ (A', B)) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map a).app B :=
  Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map O a (𝟙 B)

/-- The action of the uncurried tensor bifunctor on a pair of morphisms, read off the curried
tensor bifunctor of Tag 06YM: tensor on the left, then on the right. -/
lemma tensorSheafBifunctor_map_eq
    {A A' B B' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} O)}
    (a : A ⟶ A') (b : B ⟶ B') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O)).map
        ((a, b) : ((A, B) : _ × _) ⟶ (A', B')) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map a).app B ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj A').map b := by
  rfl

end Bridge

/-! ## Stacks 03EL at the curried tensor bifunctor -/

section Curried

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

/-- The comparison `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` of Stacks 03EL commutes with tensoring by a
morphism of second factors, for the curried tensor bifunctor of Tag 06YM. -/
lemma pullbackTensorIso_hom_naturality_snd
    (A : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {B B' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (b : B ⟶ B') :
    (f.pullbackModules).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj A).map b) ≫
        (pullbackTensorIso f).hom.app (A, B') =
      (pullbackTensorIso f).hom.app (A, B) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
            ((f.pullbackModules).obj A)).map
          ((f.pullbackModules).map b) := by
  have h :=
    (pullbackTensorIso f).hom.naturality ((𝟙 A, b) : ((A, B) : _ × _) ⟶ (A, B'))
  simp only [Functor.comp_map, Functor.prod_map] at h
  rw [(f.pullbackModules).map_id, tensorSheafBifunctor_map_id_fst,
    tensorSheafBifunctor_map_id_fst] at h
  exact h

/-- The comparison `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` of Stacks 03EL commutes with tensoring by a
morphism of first factors, for the curried tensor bifunctor of Tag 06YM. -/
lemma pullbackTensorIso_hom_naturality_fst
    {A A' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (a : A ⟶ A')
    (B : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (f.pullbackModules).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).map a).app B) ≫
        (pullbackTensorIso f).hom.app (A', B) =
      (pullbackTensorIso f).hom.app (A, B) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map
            ((f.pullbackModules).map a)).app
          ((f.pullbackModules).obj B) := by
  have h :=
    (pullbackTensorIso f).hom.naturality ((a, 𝟙 B) : ((A, B) : _ × _) ⟶ (A', B))
  simp only [Functor.comp_map, Functor.prod_map] at h
  rw [(f.pullbackModules).map_id, tensorSheafBifunctor_map_id_snd,
    tensorSheafBifunctor_map_id_snd] at h
  exact h

/-- The comparison `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` of Stacks 03EL commutes with the tensor product
of a pair of morphisms, for the curried tensor bifunctor of Tag 06YM. -/
lemma pullbackTensorIso_hom_naturality_map
    {A A' B B' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (a : A ⟶ A') (b : B ⟶ B') :
    (f.pullbackModules).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).map a).app B ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj A').map b) ≫
        (pullbackTensorIso f).hom.app (A', B') =
      (pullbackTensorIso f).hom.app (A, B) ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map
                ((f.pullbackModules).map a)).app
            ((f.pullbackModules).obj B) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
              ((f.pullbackModules).obj A')).map
            ((f.pullbackModules).map b)) :=
  (pullbackTensorIso f).hom.naturality ((a, b) : ((A, B) : _ × _) ⟶ (A', B'))

end Curried

end Stacks.SheafOfModules

namespace Stacks.Sheaves.DerivedPullback

open HomologicalComplex₂.TotalMap Stacks.SheafOfModules

/-! ## The comparison of total tensor complexes -/

section Complexes

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M :
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
        SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).Additive]
  [∀ M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj M :
      SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
        SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).Additive]

/-- Degreewise pullback of cochain complexes of sheaves of modules along a morphism of ringed
topoi. -/
abbrev pullbackComplexFunctor :
    CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (f.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)

variable (K L : CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)

/-- The bicomplex `(p, q) ↦ f^*(K^p ⊗_{O'} L^q)`, i.e. the pullback of the tensor double
complex of `K` and `L`. -/
abbrev tensorBicomplexPullback : HomologicalComplex₂
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) :=
  mapBicomplex (f.pullbackModules)
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
        Y.O).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L)

/-- The bicomplex `(p, q) ↦ f^*K^p ⊗_O f^*L^q`, i.e. the tensor double complex of the
pullbacks. -/
abbrev tensorBicomplexOfPullbacks : HomologicalComplex₂
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
      ((pullbackComplexFunctor f).obj K)).obj ((pullbackComplexFunctor f).obj L)

/-- The pullback of the tensor double complex of `K` and `L` is the tensor double complex of
their pullbacks: in bidegree `(p, q)` this is the comparison
`f^*(K^p ⊗_{O'} L^q) ≅ f^*K^p ⊗_O f^*L^q` of Stacks 03EL. -/
def pullbackTensorBicomplexIso :
    tensorBicomplexPullback f K L ≅ tensorBicomplexOfPullbacks f K L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => (pullbackTensorIso f).app (K.X p, L.X q))
      (fun q q' _ => (pullbackTensorIso_hom_naturality_snd f (K.X p) (L.d q q')).symm))
    (fun p p' _ => by
      ext q : 1
      exact (pullbackTensorIso_hom_naturality_fst f (K.d p p') (L.X q)).symm)

variable {K L}

/-- The comparison of bicomplexes is natural in the pair of complexes. -/
lemma pullbackTensorBicomplexIso_naturality
    {K K' L L' :
      CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    (((f.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
            Y.O).mapBifunctorHomologicalComplex
              (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map a).app L ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
              Y.O).mapBifunctorHomologicalComplex
              (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K').map b) ≫
        (pullbackTensorBicomplexIso f K' L').hom =
      (pullbackTensorBicomplexIso f K L).hom ≫
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            X.O).mapBifunctorHomologicalComplex
              (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
            ((pullbackComplexFunctor f).map a)).app ((pullbackComplexFunctor f).obj L) ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              X.O).mapBifunctorHomologicalComplex
              (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
            ((pullbackComplexFunctor f).obj K')).map ((pullbackComplexFunctor f).map b)) := by
  refine HomologicalComplex.hom_ext _ _ (fun p => ?_)
  refine HomologicalComplex.hom_ext _ _ (fun q => ?_)
  exact pullbackTensorIso_hom_naturality_map f (a.f p) (b.f q)

variable (K L)
variable [∀ (A B :
      CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ)]

/-- The pullback of the tensor double complex has a total complex. -/
instance hasTotal_tensorBicomplexPullback :
    (tensorBicomplexPullback f K L).HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_iso (pullbackTensorBicomplexIso f K L).symm _

variable [∀ (A B :
      CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O) (ComplexShape.up ℤ)]

/-- The comparison `f^*Tot(K ⊗_{O'} L) ≅ Tot(f^*K ⊗_O f^*L)`, for a morphism of ringed topoi
`f` and unbounded cochain complexes `K`, `L` of `O'`-modules: the inverse of the comparison of
pullback with the total complex, `HomologicalComplex₂.TotalMap.totalIso`, followed by the total
complex of `Stacks.Sheaves.DerivedPullback.pullbackTensorBicomplexIso`. -/
def pullbackTensorTotalIso :
    (pullbackComplexFunctor f).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O) (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor ((pullbackComplexFunctor f).obj K)
        ((pullbackComplexFunctor f).obj L)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ) :=
  (totalIso (f.pullbackModules) _).symm ≪≫
    HomologicalComplex₂.total.mapIso (pullbackTensorBicomplexIso f K L) (ComplexShape.up ℤ)

/-- On the summand of bidegree `(p, q)` of total degree `n`, the comparison of total tensor
complexes is the comparison `f^*(K^p ⊗_{O'} L^q) ≅ f^*K^p ⊗_O f^*L^q` of Stacks 03EL. -/
lemma ι_pullbackTensorTotalIso_hom (p q n : ℤ) (hpq : p + q = n) :
    (f.pullbackModules).map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O) (ComplexShape.up ℤ)
          p q n hpq) ≫
        (pullbackTensorTotalIso f K L).hom.f n =
      (pullbackTensorIso f).hom.app (K.X p, L.X q) ≫
        HomologicalComplex.ιMapBifunctor ((pullbackComplexFunctor f).obj K)
          ((pullbackComplexFunctor f).obj L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O)
          (ComplexShape.up ℤ) p q n hpq := by
  have hι := ι_totalMapf (c₁₂ := ComplexShape.up ℤ) (f.pullbackModules)
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
        Y.O).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L) n p q hpq
  have h1 : (f.pullbackModules).map
        ((((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
            Y.O).mapBifunctorHomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L)).ιTotal
            (ComplexShape.up ℤ) p q n hpq) ≫
      (totalIso (f.pullbackModules)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
            Y.O).mapBifunctorHomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L)).inv.f n =
        (tensorBicomplexPullback f K L).ιTotal (ComplexShape.up ℤ) p q n hpq := by
    rw [← hι, Category.assoc,
      show totalMapf (c₁₂ := ComplexShape.up ℤ) (f.pullbackModules)
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
                Y.O).mapBifunctorHomologicalComplex
              (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L) n ≫
          (totalIso (f.pullbackModules)
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
                Y.O).mapBifunctorHomologicalComplex
              (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L)).inv.f n = 𝟙 _ from
        congrArg (fun φ => HomologicalComplex.Hom.f φ n)
          (totalIso (c₁₂ := ComplexShape.up ℤ) (f.pullbackModules)
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
                Y.O).mapBifunctorHomologicalComplex
              (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L)).hom_inv_id,
      Category.comp_id]
  have h2 := HomologicalComplex₂.ιTotal_map (tensorBicomplexPullback f K L)
    (tensorBicomplexOfPullbacks f K L) (pullbackTensorBicomplexIso f K L).hom
    (ComplexShape.up ℤ) p q n hpq
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ (HomologicalComplex₂.total.mapIso
      (pullbackTensorBicomplexIso f K L) (ComplexShape.up ℤ)).hom.f n) h1)).trans h2

/-- Two morphisms out of `f^*Tot(K ⊗_{O'} L)` in a given total degree agree as soon as they
agree after the `f^*`-image of each summand inclusion. -/
lemma hom_ext_pullbackTotal (n : ℤ)
    {A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {u v : ((pullbackComplexFunctor f).obj (HomologicalComplex.mapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O)
      (ComplexShape.up ℤ))).X n ⟶ A}
    (h : ∀ (p q : ℤ) (hpq : p + q = n),
      (f.pullbackModules).map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O) (ComplexShape.up ℤ)
          p q n hpq) ≫ u =
        (f.pullbackModules).map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O) (ComplexShape.up ℤ)
          p q n hpq) ≫ v) :
    u = v := by
  have : IsIso (totalMapf (c₁₂ := ComplexShape.up ℤ) (f.pullbackModules)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
          Y.O).mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L) n) :=
    isIso_totalMapf _ _ _
  rw [← cancel_epi (totalMapf (c₁₂ := ComplexShape.up ℤ) (f.pullbackModules)
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
        Y.O).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L) n)]
  refine HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (fun p q hpq => ?_)
  rw [← Category.assoc, ← Category.assoc, ι_totalMapf]
  exact h p q hpq

end Complexes

end Stacks.Sheaves.DerivedPullback

end
