module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompIso
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeIso

/-!
# The composition isomorphism of direct images with compact support and base change

Consider a diagram of a big étale site
```
X' --c--> X
|f'       |f
Y' --b--> Y
|g'       |g
Z' --a--> Z
```
with both squares cartesian and `f`, `g` locally quasi-finite. The composition isomorphisms of
Stacks 0F6T and the base-change isomorphisms of Stacks 0F5J form a commutative diagram
```
a⁻¹(g ∘ f)_! ----------------> (g' ∘ f')_! c⁻¹
     |                                |
a⁻¹ g_! f_! --> g'_! b⁻¹ f_! --> g'_! f'_! c⁻¹
```
which is part (5) of Stacks 0F6T. It is checked on the stalks at the geometric points of `Z'`,
where every arrow is a map of direct sums of stalks over geometric fibres.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekCompIso_baseChange` — part (5) of Stacks 0F6T.

## Implementation notes

The base-change isomorphism of Stacks 0F5J is available for abelian sheaves with values in
`AddCommGrpCat.{u + 1}`, so the statement is made there.

## References

* [Stacks Project, Tag 0F6T](https://stacks.math.columbia.edu/tag/0F6T)
* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped DirectSum

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' Z' : B.Scheme}
  (c : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y) (g' : Y' ⟶ Z') (g : Y ⟶ Z) (a : Z' ⟶ Z)
  (sq₁ : IsPullback c f' f b) (sq₂ : IsPullback b g' g a)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]
  [LocallyOfFiniteType (B.inclusion.map g')] [LocallyQuasiFinite (B.inclusion.map g')]

omit [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map g')] [LocallyQuasiFinite (B.inclusion.map g')] in
/-- The regrouping of the geometric fibres commutes with the identifications of geometric fibres
along the two cartesian squares and along the outer rectangle. -/
public theorem compFiberStalksMap_baseChange (t : GeometricPoint Z'.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (ξ : fiberStalks.{u, u + 1} B (f ≫ g) (t.map (B.inclusion.map a)) F) :
    compFiberStalksMap.{u, u + 1} B f' g' t ((abPullback.{u, u + 1} B c).obj F)
        (fiberStalksBaseChangeEquiv.{u, u + 1} B c (f' ≫ g') (f ≫ g) a (sq₁.paste_vert sq₂) t F
          ξ) =
      fiberStalksMap.{u, u + 1} B g' t (fShriekBaseChangeMap.{u} B c f' f b sq₁ F)
        (fiberStalksBaseChangeEquiv.{u, u + 1} B b g' g a sq₂ t
          ((fShriekFunctor.{u, u + 1} B f).obj F)
          (compFiberStalksMap.{u, u + 1} B f g (t.map (B.inclusion.map a)) F ξ)) := by
  refine DFinsupp.ext fun y => ?_
  refine (AddCommGrpCat.mono_iff_injective (fShriekStalkIso.{u, u + 1} B f'
    (y.toGeometricPoint B g' t) ((abPullback.{u, u + 1} B c).obj F)).hom).1 inferInstance ?_
  refine DFinsupp.ext fun x => ?_
  refine (compFiberStalksMap_apply.{u, u + 1} B f' g' t ((abPullback.{u, u + 1} B c).obj F) _ y
    x).trans ?_
  have h1 := ConcreteCategory.congr_hom (fShriekBaseChangeNatIso_stalk.{u} B c f' f b sq₁
    (y.toGeometricPoint B g' t) F)
    ((fiberStalksBaseChangeEquiv.{u, u + 1} B b g' g a sq₂ t ((fShriekFunctor.{u, u + 1} B f).obj F)
      (compFiberStalksMap.{u, u + 1} B f g (t.map (B.inclusion.map a)) F ξ)) y)
  refine Eq.symm ((congrArg (fun m => (m : fiberStalks.{u, u + 1} B f' _ _) x) h1).trans ?_)
  refine (fiberStalksBaseChangeEquiv_apply.{u, u + 1} B c f' f b sq₁ _ F _ x).trans ?_
  refine congrArg (fiberStalkBaseChangeIso.{u, u + 1} B c f' f b sq₁ _ F x).hom ?_
  have h2 : (etaleStalkSmallEtalePullObjIso B b (y.toGeometricPoint B g' t) AddCommGrpCat.{u + 1}
        ((fShriekFunctor.{u, u + 1} B f).obj F)).hom
      ((fiberStalksBaseChangeEquiv.{u, u + 1} B b g' g a sq₂ t
        ((fShriekFunctor.{u, u + 1} B f).obj F)
        (compFiberStalksMap.{u, u + 1} B f g (t.map (B.inclusion.map a)) F ξ)) y) =
      (compFiberStalksMap.{u, u + 1} B f g (t.map (B.inclusion.map a)) F ξ)
        (fiberPointBaseChange B b g' g a sq₂ t y) :=
    Iso.inv_hom_id_apply (etaleStalkSmallEtalePullObjIso B b (y.toGeometricPoint B g' t)
      AddCommGrpCat.{u + 1} ((fShriekFunctor.{u, u + 1} B f).obj F)) _
  refine (congrArg (fun m => ((fShriekStalkIso.{u, u + 1} B f _ F).hom m :
    fiberStalks.{u, u + 1} B f _ F) (fiberPointBaseChange B c f' f b sq₁ _ x)) h2).trans ?_
  exact compFiberStalksMap_apply.{u, u + 1} B f g (t.map (B.inclusion.map a)) F ξ
    (fiberPointBaseChange B b g' g a sq₂ t y) (fiberPointBaseChange B c f' f b sq₁ _ x)

/-- The diagram of part (5) of Stacks 0F6T, for given finiteness instances on the base changes. -/
public theorem fShriekCompIso_baseChange_app
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (fShriekBaseChangeNatIso.{u} B c (f' ≫ g') (f ≫ g) a (sq₁.paste_vert sq₂)).hom.app F ≫
        (fShriekCompIso.{u, u + 1} B f' g').hom.app ((abPullback.{u, u + 1} B c).obj F) =
      (abPullback.{u, u + 1} B a).map ((fShriekCompIso.{u, u + 1} B f g).hom.app F) ≫
        (fShriekBaseChangeNatIso.{u} B b g' g a sq₂).hom.app
          ((fShriekFunctor.{u, u + 1} B f).obj F) ≫
        (fShriekFunctor.{u, u + 1} B g').map
          ((fShriekBaseChangeNatIso.{u} B c f' f b sq₁).hom.app F) := by
  refine (jointlyFaithful_etaleStalkSheafFiber.{u, u + 1} B Z'.obj Z'.property).map_injective
    fun t => ?_
  refine (cancel_mono (fShriekStalkIso.{u, u + 1} B g' t ((fShriekFunctor.{u, u + 1} B f').obj
    ((abPullback.{u, u + 1} B c).obj F))).hom).1 ?_
  have s1 := fShriekCompIso_stalk.{u, u + 1} B f' g' t ((abPullback.{u, u + 1} B c).obj F)
  have s2 := fShriekBaseChangeNatIso_stalk.{u} B c (f' ≫ g') (f ≫ g) a (sq₁.paste_vert sq₂) t F
  have s3 := fShriekStalkIso_natural.{u, u + 1} B g' t
    ((fShriekBaseChangeNatIso.{u} B c f' f b sq₁).hom.app F)
  have s4 := fShriekBaseChangeNatIso_stalk.{u} B b g' g a sq₂ t
    ((fShriekFunctor.{u, u + 1} B f).obj F)
  have s5 := (smallEtalePullbackSheafFiberIso B a t AddCommGrpCat.{u + 1}).hom.naturality
    ((fShriekCompIso.{u, u + 1} B f g).hom.app F)
  have s6 := fShriekCompIso_stalk.{u, u + 1} B f g (t.map (B.inclusion.map a)) F
  have key {P Q R S T : AddCommGrpCat.{u + 1}} {x : P ⟶ Q} {y : Q ⟶ R} {v : P ⟶ S} {w : S ⟶ R}
      (h : x ≫ y = v ≫ w) (z : R ⟶ T) : x ≫ y ≫ z = v ≫ w ≫ z := by
    rw [← Category.assoc, h, Category.assoc]
  refine ((congrArg (· ≫ _) (CategoryTheory.Functor.map_comp _ _ _)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) s1))).trans ?_
  refine (key s2 _).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ _) (CategoryTheory.Functor.map_comp _ _ _).symm)
  refine Eq.trans ?_ (congrArg (· ≫ _) (congrArg (_ ≫ ·)
    (CategoryTheory.Functor.map_comp _ _ _).symm))
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) s3).symm)
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (key s4 _).symm)
  refine Eq.trans ?_ (key s5 _).symm
  refine congrArg (_ ≫ ·) ?_
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.assoc _ _ _)).symm
  refine Eq.trans ?_ (key s6 _).symm
  refine (Category.assoc _ _ _).trans (congrArg (fun k => (fShriekStalkIso.{u, u + 1} B (f ≫ g)
    (t.map (B.inclusion.map a)) F).hom ≫ k) (ConcreteCategory.hom_ext _ _ fun ξ => ?_))
  exact compFiberStalksMap_baseChange B c f' f b g' g a sq₁ sq₂ t F ξ

omit [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]
  [LocallyOfFiniteType (B.inclusion.map g')] [LocallyQuasiFinite (B.inclusion.map g')] in
/-- **Stacks 0F6T, part (5).** For a diagram with both squares cartesian
```
X' --c--> X
|f'       |f
Y' --b--> Y
|g'       |g
Z' --a--> Z
```
and `f`, `g` locally quasi-finite, the composition isomorphisms and the base-change isomorphisms
of Stacks 0F5J make the diagram
```
a⁻¹(g ∘ f)_! ----------------> (g' ∘ f')_! c⁻¹
     |                                |
a⁻¹ g_! f_! --> g'_! b⁻¹ f_! --> g'_! f'_! c⁻¹
```
commute. The base changes `f'` and `g'` are locally quasi-finite because `f` and `g` are. -/
@[stacks 0F6T "part (5)"]
public theorem fShriekCompIso_baseChange :
    letI := locallyOfFiniteType_of_isPullback B c f' f b sq₁
    letI := locallyQuasiFinite_of_isPullback B c f' f b sq₁
    letI := locallyOfFiniteType_of_isPullback B b g' g a sq₂
    letI := locallyQuasiFinite_of_isPullback B b g' g a sq₂
    (fShriekBaseChangeNatIso.{u} B c (f' ≫ g') (f ≫ g) a (sq₁.paste_vert sq₂)).hom ≫
        Functor.whiskerLeft (abPullback.{u, u + 1} B c) (fShriekCompIso.{u, u + 1} B f' g').hom =
      Functor.whiskerRight (fShriekCompIso.{u, u + 1} B f g).hom (abPullback.{u, u + 1} B a) ≫
        Functor.whiskerLeft (fShriekFunctor.{u, u + 1} B f)
          (fShriekBaseChangeNatIso.{u} B b g' g a sq₂).hom ≫
        Functor.whiskerRight (fShriekBaseChangeNatIso.{u} B c f' f b sq₁).hom
          (fShriekFunctor.{u, u + 1} B g') := by
  let := locallyOfFiniteType_of_isPullback B c f' f b sq₁
  let := locallyQuasiFinite_of_isPullback B c f' f b sq₁
  let := locallyOfFiniteType_of_isPullback B b g' g a sq₂
  let := locallyQuasiFinite_of_isPullback B b g' g a sq₂
  ext F : 2
  exact fShriekCompIso_baseChange_app B c f' f b g' g a sq₁ sq₂ F

end AlgebraicGeometry.SmallEtale

end
