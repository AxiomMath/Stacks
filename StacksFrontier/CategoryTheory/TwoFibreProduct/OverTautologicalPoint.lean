module

public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# The tautological point of a 2-fibre product taken along a functor

Fix a base category `𝒞` and categories `𝒜`, `𝒴`, `𝒵` over it with structure functors `r`, `p𝒴`,
`p𝒵`, together with a 1-morphism `G : 𝒴 ⥤ 𝒵` over `𝒞`. A functor `y : 𝒜 ⥤ 𝒴` over `𝒞`, read as
a point of `𝒴` with values in `𝒜`, determines a point of `𝒵` with values in `𝒜`, namely
`y ⋙ G`, and the 2-fibre product `𝒜 ×_{y ⋙ G, 𝒵, G} 𝒴` of Stacks 0040
(`CategoryTheory.TwoFibreProductOver`) then has a *tautological* point: the triple
`(a, y a, 𝟙)`, whose comparison isomorphism is the identity because the two legs agree on the
nose at `y`.

What makes this worth naming is that its second projection is `y` again, on the nose rather than
up to isomorphism. A statement about an arbitrary point of such a 2-fibre product therefore
specialises to a statement about the base change along the *given* `y`, which is what turns a
construction performed at an arbitrary point into one performed at a point in hand.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.pointOfFunctor`: the tautological point.

## Main results

* `CategoryTheory.TwoFibreProductOver.pointOfFunctor_comp_fst`,
  `CategoryTheory.TwoFibreProductOver.pointOfFunctor_comp_snd` and
  `CategoryTheory.TwoFibreProductOver.pointOfFunctor_comp_structureFunctor`: the three
  composites of the tautological point with the projections and the structure functor are the
  identity of `𝒜`, the functor `y` and the structure functor `r`, each on the nose.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒜 : Type u₂} [Category.{v₂} 𝒜]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒵 : Type u₄} [Category.{v₄} 𝒵]

/-- **The tautological point of `𝒜 ×_{y ⋙ G, 𝒵, G} 𝒴`.** For a 1-morphism `G : 𝒴 ⥤ 𝒵` over `𝒞`
and a functor `y : 𝒜 ⥤ 𝒴` over `𝒞`, this is the point of the 2-fibre product of `r` and `G`
along `y ⋙ G` sending an object `a` of `𝒜` to the triple consisting of `a`, of `y a`, and of the
identity comparison isomorphism. -/
def pointOfFunctor (r : 𝒜 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞) (G : 𝒴 ⥤ 𝒵) (hG : G ⋙ p𝒵 = p𝒴)
    (y : 𝒜 ⥤ 𝒴) (hy : y ⋙ p𝒴 = r) : 𝒜 ⥤ TwoFibreProductOver r p𝒴 p𝒵 (y ⋙ G) G where
  obj a :=
    { base := r.obj a
      x := a
      y := y.obj a
      hx := rfl
      hy := Functor.congr_obj hy a
      iso := Iso.refl _
      vertical := IsHomLift.id
        ((Functor.congr_obj hG (y.obj a)).trans (Functor.congr_obj hy a)) }
  map {_a _b} m :=
    { hbase := r.map m
      a := m
      b := y.map m
      ha := IsHomLift.map r m
      hb := Functor.isHomLift_map_of_comp_eq hy (r.map m) m
      w := by simp }
  map_id a := Hom.ext' rfl (y.map_id a)
  map_comp m m' := Hom.ext' rfl (y.map_comp m m')

/-- The tautological point is a section of the first projection: its `𝒜`-component is the
object it was formed at. -/
theorem pointOfFunctor_comp_fst (r : 𝒜 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞) (G : 𝒴 ⥤ 𝒵)
    (hG : G ⋙ p𝒵 = p𝒴) (y : 𝒜 ⥤ 𝒴) (hy : y ⋙ p𝒴 = r) :
    pointOfFunctor r p𝒴 p𝒵 G hG y hy ⋙ fst r p𝒴 p𝒵 (y ⋙ G) G = 𝟭 𝒜 := rfl

/-- **The second projection of the tautological point of `y` is `y`.** -/
theorem pointOfFunctor_comp_snd (r : 𝒜 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞) (G : 𝒴 ⥤ 𝒵)
    (hG : G ⋙ p𝒵 = p𝒴) (y : 𝒜 ⥤ 𝒴) (hy : y ⋙ p𝒴 = r) :
    pointOfFunctor r p𝒴 p𝒵 G hG y hy ⋙ snd r p𝒴 p𝒵 (y ⋙ G) G = y := rfl

/-- The tautological point is strictly over `𝒞`. -/
theorem pointOfFunctor_comp_structureFunctor (r : 𝒜 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (G : 𝒴 ⥤ 𝒵) (hG : G ⋙ p𝒵 = p𝒴) (y : 𝒜 ⥤ 𝒴) (hy : y ⋙ p𝒴 = r) :
    pointOfFunctor r p𝒴 p𝒵 G hG y hy ⋙ structureFunctor r p𝒴 p𝒵 (y ⋙ G) G = r := rfl

end CategoryTheory.TwoFibreProductOver

end
