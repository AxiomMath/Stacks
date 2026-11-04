module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.BaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.DescentIso

/-!
# Pullback of descent data along a factorisation

If the upper horizontal arrow of a commutative square factors as `j ≫ p`, then the pullback
functor on descent data it induces is isomorphic to the composite of the pullback functors
along `p` and along `j`.

## Main definitions

* `AlgebraicGeometry.DescentData.pullbackCompIso` compares the iterated base change with the
  base change along the composite.
* `AlgebraicGeometry.DescentData.pullbackFactorizationIso` is the resulting isomorphism of
  pullback functors on descent data. Its three bases and three base maps vary independently, so
  it is equivalently the composition law for the pullback functors of two stacked squares.
* `AlgebraicGeometry.DescentData.identityPullbackFunctor` is the pullback functor of the
  identity square, whose functor is the identity.

## References

* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

section CompIso

variable {X X' Y : Scheme.{u}} (p : Y ⟶ X') (j : X ⟶ Y) (V : Over X')

/-- The iterated base change `j^* p^* V` compared with the base change `(j ≫ p)^* V`. -/
def pullbackCompIso :
    (Over.pullback j).obj ((Over.pullback p).obj V) ≅ (Over.pullback (j ≫ p)).obj V :=
  Over.isoMk (pullbackLeftPullbackSndIso V.hom p j) (by simp)

/-- The comparison `pullbackCompIso` followed by the first projection of `(j ≫ p)^* V` is the
composite of the first projections of the iterated base change. -/
@[reassoc]
lemma pullbackCompIso_hom_left_fst :
    (pullbackCompIso p j V).hom.left ≫ pullback.fst V.hom (j ≫ p) =
      pullback.fst (pullback.snd V.hom p) j ≫ pullback.fst V.hom p :=
  pullbackLeftPullbackSndIso_hom_fst V.hom p j

/-- The comparison `pullbackCompIso` followed by the second projection of `(j ≫ p)^* V` is the
second projection of the iterated base change. -/
@[reassoc]
lemma pullbackCompIso_hom_left_snd :
    (pullbackCompIso p j V).hom.left ≫ pullback.snd V.hom (j ≫ p) =
      pullback.snd (pullback.snd V.hom p) j := by
  simpa using Over.w (pullbackCompIso p j V).hom

/-- The comparison `pullbackCompIso` is natural in `V`. -/
lemma pullbackCompIso_naturality {V W : Over X'} (v : V ⟶ W) :
    (Over.pullback j).map ((Over.pullback p).map v) ≫ (pullbackCompIso p j W).hom =
      (pullbackCompIso p j V).hom ≫ (Over.pullback (j ≫ p)).map v := by
  have h1 : ((Over.pullback j).map ((Over.pullback p).map v)).left ≫
      pullback.fst (pullback.snd W.hom p) j =
      pullback.fst (pullback.snd V.hom p) j ≫ ((Over.pullback p).map v).left :=
    pullbackMap_left_fst j ((Over.pullback p).map v)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, pullbackCompIso_hom_left_fst,
      pullbackMap_left_fst, pullbackCompIso_hom_left_fst_assoc]
    rw [← Category.assoc, h1, Category.assoc, pullbackMap_left_fst]
  · simp only [Over.comp_left, Category.assoc, pullbackCompIso_hom_left_snd,
      pullbackMap_left_snd]
    exact pullbackMap_left_snd j ((Over.pullback p).map v)

end CompIso

section Factorization

variable {S S₁ S₂ X X' Y : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S₂} {b : Y ⟶ S₁}
  {p : Y ⟶ X'} {j : X ⟶ Y} {h : S ⟶ S₂} {h₁ : S₁ ⟶ S₂} {h₀ : S ⟶ S₁}
  {comm₀ : (j ≫ p) ≫ a' = a ≫ h} {comm₂ : p ≫ a' = b ≫ h₁} {commⱼ : j ≫ b = a ≫ h₀}
  (P₀ : PullbackFunctor a' a h (j ≫ p) comm₀)
  (P₂ : PullbackFunctor a' b h₁ p comm₂) (Pⱼ : PullbackFunctor b a h₀ j commⱼ)
  (D : DescentData (fun _ : Unit ↦ a'))

/-- The comparison of the iterated pullback with the direct one, on underlying objects. -/
def factorizationObjIso :
    (Pⱼ.functor.obj (P₂.functor.obj D)).obj () ≅ (P₀.functor.obj D).obj () :=
  Pⱼ.objIso (P₂.functor.obj D) ≪≫ (Over.pullback j).mapIso (P₂.objIso D) ≪≫
    pullbackCompIso p j (D.obj ()) ≪≫ (P₀.objIso D).symm

/-- The comparison `factorizationObjIso` followed by the identification of the direct pullback
with a base change is the composite of the identifications of the iterated pullback with an
iterated base change and of `pullbackCompIso`. -/
lemma factorizationObjIso_hom_objIso :
    (factorizationObjIso P₀ P₂ Pⱼ D).hom ≫ (P₀.objIso D).hom =
      (Pⱼ.objIso (P₂.functor.obj D)).hom ≫ (Over.pullback j).map (P₂.objIso D).hom ≫
        (pullbackCompIso p j (D.obj ())).hom := by
  simp [factorizationObjIso, Category.assoc]

/-- The first projection of the comparison `factorizationObjIso`, read on underlying schemes. -/
@[reassoc]
lemma factorizationObjIso_hom_left_fst :
    (factorizationObjIso P₀ P₂ Pⱼ D).hom.left ≫ (P₀.objIso D).hom.left ≫
        pullback.fst (D.obj ()).hom (j ≫ p) =
      (Pⱼ.objIso (P₂.functor.obj D)).hom.left ≫
        pullback.fst (((P₂.functor.obj D).obj ()).hom) j ≫
          (P₂.objIso D).hom.left ≫ pullback.fst (D.obj ()).hom p := by
  have hiso := congrArg Over.Hom.left (factorizationObjIso_hom_objIso P₀ P₂ Pⱼ D)
  simp only [Over.comp_left] at hiso
  have hmap : ((Over.pullback j).map (P₂.objIso D).hom).left ≫
      pullback.fst (pullback.snd (D.obj ()).hom p) j =
      pullback.fst (((P₂.functor.obj D).obj ()).hom) j ≫ (P₂.objIso D).hom.left :=
    pullbackMap_left_fst j (P₂.objIso D).hom
  rw [← Category.assoc, hiso]
  simp only [Category.assoc]
  rw [pullbackCompIso_hom_left_fst, ← Category.assoc
    (((Over.pullback j).map (P₂.objIso D).hom).left), hmap]
  simp only [Category.assoc]

/-- The comparison `factorizationObjIso` is compatible with the source maps of the direct and the
iterated pullback. -/
lemma actOnMap_sourceMap_eq :
    actOnMap (factorizationObjIso P₀ P₂ Pⱼ D).hom ≫ P₀.sourceMap D =
      Pⱼ.sourceMap (P₂.functor.obj D) ≫ P₂.sourceMap D := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, P₀.sourceMap_fst, P₂.sourceMap_fst, P₀.sourceMap_snd,
      P₂.sourceMap_snd, actOnMap_fst_assoc, actOnMap_snd_assoc,
      reassoc_of% (Pⱼ.sourceMap_fst (P₂.functor.obj D)),
      reassoc_of% (Pⱼ.sourceMap_snd (P₂.functor.obj D)), factorizationObjIso_hom_left_fst]

/-- The comparison `factorizationObjIso` is compatible with the descent actions of the iterated
and the direct pullback. -/
lemma factorizationObjIso_actOn :
    (Pⱼ.functor.obj (P₂.functor.obj D)).actOn ≫
        (factorizationObjIso P₀ P₂ Pⱼ D).hom.left =
      actOnMap (factorizationObjIso P₀ P₂ Pⱼ D).hom ≫ (P₀.functor.obj D).actOn := by
  apply (cancel_mono ((Over.forget X).map (P₀.objIso D).hom)).mp
  simp only [Over.forget_map]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [factorizationObjIso_hom_left_fst, Pⱼ.actOn_objIso_fst_assoc,
      P₂.actOn_objIso_fst, P₀.actOn_objIso_fst,
      ← Category.assoc (actOnMap (factorizationObjIso P₀ P₂ Pⱼ D).hom),
      actOnMap_sourceMap_eq P₀ P₂ Pⱼ D]
    simp only [Category.assoc]
  · simp only [Category.assoc, P₀.objIso_hom_left_snd]
    rw [Over.w (factorizationObjIso P₀ P₂ Pⱼ D).hom, DescentData.actOn_hom,
      DescentData.actOn_hom, actOnMap_snd]

/-- The comparison of the iterated pullback with the direct one, as descent data. -/
def factorizationDatumIso :
    Pⱼ.functor.obj (P₂.functor.obj D) ≅ P₀.functor.obj D :=
  isoOfActOn (factorizationObjIso P₀ P₂ Pⱼ D) (factorizationObjIso_actOn P₀ P₂ Pⱼ D)

/-- A pullback functor for a factored horizontal arrow is the composite of the two pullback
functors. -/
def pullbackFactorizationIso : P₀.functor ≅ P₂.functor ⋙ Pⱼ.functor :=
  (NatIso.ofComponents (factorizationDatumIso P₀ P₂ Pⱼ) (by
    intro D E g
    refine DescentData.hom_ext fun ⟨⟩ => ?_
    change ((Pⱼ.functor.map (P₂.functor.map g)).hom ()) ≫
        (factorizationObjIso P₀ P₂ Pⱼ E).hom =
      (factorizationObjIso P₀ P₂ Pⱼ D).hom ≫ ((P₀.functor.map g).hom ())
    apply (cancel_mono (P₀.objIso E).hom).mp
    simp only [Category.assoc, factorizationObjIso_hom_objIso]
    rw [← Category.assoc ((Pⱼ.functor.map (P₂.functor.map g)).hom ()),
      ← Pⱼ.map (P₂.functor.map g)]
    simp only [Category.assoc]
    rw [← Category.assoc ((Over.pullback j).map ((P₂.functor.map g).hom ())),
      ← Functor.map_comp, ← P₂.map g, Functor.map_comp]
    simp only [Category.assoc]
    rw [← P₀.map g, ← Category.assoc (factorizationObjIso P₀ P₂ Pⱼ D).hom,
      factorizationObjIso_hom_objIso]
    simp only [Category.assoc]
    rw [pullbackCompIso_naturality])).symm

end Factorization

section Identity

variable {S X : Scheme.{u}}

/-- Base change along the identity. -/
def pullbackIdObjIso (V : Over X) : V ≅ (Over.pullback (𝟙 X)).obj V :=
  (Over.pullbackId (X := X)).symm.app V

/-- The identification `pullbackIdObjIso` followed by the first projection is the identity. -/
lemma pullbackIdObjIso_hom_left_fst (V : Over X) :
    (pullbackIdObjIso V).hom.left ≫ pullback.fst V.hom (𝟙 X) = 𝟙 V.left := by
  simp [pullbackIdObjIso, Over.pullbackId, pullback.lift_fst]

/-- The pullback functor of the identity square: the identity functor on descent data. -/
def identityPullbackFunctor (a : X ⟶ S) :
    PullbackFunctor a a (𝟙 S) (𝟙 X) (by simp) where
  functor := 𝟭 _
  objIso D := pullbackIdObjIso (D.obj ())
  sourceMap _ := 𝟙 _
  sourceMap_fst D := by rw [pullbackIdObjIso_hom_left_fst]; simp
  sourceMap_snd _ := by simp
  targetMap _ := 𝟙 _
  targetMap_fst _ := by simp
  targetMap_snd D := by rw [pullbackIdObjIso_hom_left_fst]; simp
  gluing _ := by simp
  map := by
    intro D E φ
    simpa [pullbackIdObjIso, Functor.id_map] using
      ((Over.pullbackId (X := X)).symm.hom.naturality (φ.hom ())).symm

end Identity

end AlgebraicGeometry.DescentData
