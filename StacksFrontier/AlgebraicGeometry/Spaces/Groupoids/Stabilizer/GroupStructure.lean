module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Composition

/-!
# The stabilizer is a group algebraic space

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U`. The stabilizer of
`G` is an algebraic space over `U`, and composition in the groupoid makes it a group object in
the slice over `U`: a generalized point of the stabilizer is an arrow of `G` whose two
endpoints agree, two such over the same test object are composable, and composition, the
identity arrow and the inverse arrow give the multiplication, the unit and the inverse.

All names are in the namespace `AlgebraicGeometry.GroupoidInAlgebraicSpaces`.

## Main definitions

* `stabilizerMul`, `stabilizerOne` and `stabilizerInv`: the three structure morphisms.
* `IsStabilizerGroupStructure`: the property of a group-object structure on the stabilizer that
  its multiplication is groupoid composition on underlying arrows.
* `stabilizerGroup`: the stabilizer as a group algebraic space over the object space, an instance
  of **Stacks 043H** whose algebraicity is **Stacks 02X2** for the defining fibre product.

## Main results

* `stabilizerGroupStructure`: **Stacks 0447**, the stabilizer carries a group-object structure
  whose multiplication is groupoid composition.
* `stabilizer_mul_comp_arrow`: the resulting multiplication, read on underlying arrows.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The unit of the stabilizer: the identity arrow at each point of the object space. -/
noncomputable def stabilizerOne (G : GroupoidInAlgebraicSpaces C S hS B) :
    𝟙_ (Over G.objects.obj) ⟶ stabilizer G := by
  have huw := stabilizerArrow_condition G (identityArrow G).hom (𝟙 G.objects.obj)
    (identityArrow_hom_comp_source G) (identityArrow_hom_comp_target G)
  exact Over.homMk (pullback.lift (identityArrow G).hom (𝟙 G.objects.obj) huw) (by
    change pullback.lift (identityArrow G).hom (𝟙 G.objects.obj) huw ≫
      (stabilizer G).hom = 𝟙 G.objects.obj
    exact pullback.lift_snd _ _ huw)

/-- The multiplication of the stabilizer: composition in the groupoid. -/
noncomputable def stabilizerMul (G : GroupoidInAlgebraicSpaces C S hS B) :
    stabilizer G ⊗ stabilizer G ⟶ stabilizer G := by
  let P := stabilizer G ⊗ stabilizer G
  let f := stabilizerArrowHom G (fst (stabilizer G) (stabilizer G))
  let g := stabilizerArrowHom G (snd (stabilizer G) (stabilizer G))
  let u := groupoidCompose G f g (stabilizerArrowHom_composable G _ _)
  let v : P.left ⟶ G.objects.obj := P.hom
  have huₛ : u ≫ G.source.hom = v := by
    dsimp [u]
    rw [groupoidCompose_source]
    exact stabilizerArrowHom_source G (snd (stabilizer G) (stabilizer G))
  have huₜ : u ≫ G.target.hom = v := by
    dsimp [u]
    rw [groupoidCompose_target]
    exact stabilizerArrowHom_target G (fst (stabilizer G) (stabilizer G))
  have hw := stabilizerArrow_condition G u v huₛ huₜ
  exact Over.homMk (pullback.lift u v hw) (by
    change pullback.lift u v hw ≫ (stabilizer G).hom = P.hom
    exact pullback.lift_snd u v hw)

/-- The inverse of the stabilizer: the inverse arrow in the groupoid. -/
noncomputable def stabilizerInv (G : GroupoidInAlgebraicSpaces C S hS B) :
    stabilizer G ⟶ stabilizer G := by
  let P := stabilizer G
  let u : P.left ⟶ G.arrows.obj := stabilizerArrow G ≫ groupoidInverse G
  let v : P.left ⟶ G.objects.obj := P.hom
  have huₛ : u ≫ G.source.hom = v := by
    dsimp [u]
    rw [Category.assoc, groupoidInverse_source]
    exact stabilizerArrow_target G
  have huₜ : u ≫ G.target.hom = v := by
    dsimp [u]
    rw [Category.assoc, groupoidInverse_target]
    exact stabilizerArrow_source G
  have hw := stabilizerArrow_condition G u v huₛ huₜ
  exact Over.homMk (pullback.lift u v hw) (by
    change pullback.lift u v hw ≫ (stabilizer G).hom = P.hom
    exact pullback.lift_snd u v hw)

/-- The underlying arrow of a generalized point of the stabilizer is compatible with
precomposition in the slice. -/
theorem stabilizerArrowHom_comp (G : GroupoidInAlgebraicSpaces C S hS B)
    {T U : Over G.objects.obj} (k : T ⟶ U) (f : U ⟶ stabilizer G) :
    k.left ≫ stabilizerArrowHom G f = stabilizerArrowHom G (k ≫ f) := rfl

/-- The underlying arrow of a product of two generalized points of the stabilizer is the
composite of their underlying arrows. -/
theorem stabilizerArrowHom_mul (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (f g : T ⟶ stabilizer G) :
    stabilizerArrowHom G (lift f g ≫ stabilizerMul G) =
      groupoidCompose G (stabilizerArrowHom G f) (stabilizerArrowHom G g)
        (stabilizerArrowHom_composable G f g) := by
  let P := stabilizer G ⊗ stabilizer G
  let a := stabilizerArrowHom G (fst (stabilizer G) (stabilizer G))
  let b := stabilizerArrowHom G (snd (stabilizer G) (stabilizer G))
  let ab := stabilizerArrowHom_composable G
    (fst (stabilizer G) (stabilizer G)) (snd (stabilizer G) (stabilizer G))
  let c := groupoidCompose G a b ab
  let p : P.left ⟶ G.objects.obj := P.hom
  have cs : c ≫ G.source.hom = p := by
    dsimp [c, a, b]
    rw [groupoidCompose_source]
    exact stabilizerArrowHom_source G (snd (stabilizer G) (stabilizer G))
  have ct : c ≫ G.target.hom = p := by
    dsimp [c, a, b]
    rw [groupoidCompose_target]
    exact stabilizerArrowHom_target G (fst (stabilizer G) (stabilizer G))
  have cp := stabilizerArrow_condition G c p cs ct
  have hmul : (stabilizerMul G).left ≫ stabilizerArrow G = c := pullback.lift_fst c p cp
  change (lift f g).left ≫ (stabilizerMul G).left ≫ stabilizerArrow G = _
  rw [hmul]
  let k := (lift f g).left
  have e := groupoidCompose_pre G k a b ab
  have ea : k ≫ a = stabilizerArrowHom G f := by
    rw [stabilizerArrowHom_comp, lift_fst]
  have eb : k ≫ b = stabilizerArrowHom G g := by
    rw [stabilizerArrowHom_comp, lift_snd]
  have e' : k ≫ groupoidCompose G a b ab =
      groupoidCompose G (stabilizerArrowHom G f) (stabilizerArrowHom G g)
        (stabilizerArrowHom_composable G f g) := by
    simpa only [ea, eb, a, b] using e
  simpa [c, k] using e'

/-- The underlying arrow of the unit of the stabilizer is the identity arrow. -/
theorem stabilizerArrowHom_one (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (k : T ⟶ 𝟙_ (Over G.objects.obj)) :
    stabilizerArrowHom G (k ≫ stabilizerOne G) = T.hom ≫ (identityArrow G).hom := by
  change k.left ≫ (stabilizerOne G).left ≫ stabilizerArrow G =
    T.hom ≫ (identityArrow G).hom
  have h : (stabilizerOne G).left ≫ stabilizerArrow G = (identityArrow G).hom := by
    exact pullback.lift_fst _ _ _
  rw [h, show k.left = T.hom by simpa using k.w]

/-- The underlying arrow of the inverse of a generalized point of the stabilizer is the
inverse arrow. -/
theorem stabilizerArrowHom_inv (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (f : T ⟶ stabilizer G) :
    stabilizerArrowHom G (f ≫ stabilizerInv G) =
      stabilizerArrowHom G f ≫ groupoidInverse G := by
  change f.left ≫ (stabilizerInv G).left ≫ stabilizerArrow G =
    (f.left ≫ stabilizerArrow G) ≫ groupoidInverse G
  have h : (stabilizerInv G).left ≫ stabilizerArrow G =
      stabilizerArrow G ≫ groupoidInverse G := by
    exact pullback.lift_fst _ _ _
  rw [h, Category.assoc]

/-- Multiplication of generalized points of the stabilizer is associative, read on underlying
arrows. -/
theorem stabilizerArrowHom_mul_assoc (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (f g k : T ⟶ stabilizer G) :
    stabilizerArrowHom G (lift (lift f g ≫ stabilizerMul G) k ≫ stabilizerMul G) =
      stabilizerArrowHom G (lift f (lift g k ≫ stabilizerMul G) ≫ stabilizerMul G) := by
  let a := stabilizerArrowHom G f
  let b := stabilizerArrowHom G g
  let c := stabilizerArrowHom G k
  have wab : a ≫ G.source.hom = b ≫ G.target.hom := stabilizerArrowHom_composable G f g
  have wbc : b ≫ G.source.hom = c ≫ G.target.hom := stabilizerArrowHom_composable G g k
  have wL : groupoidCompose G a b wab ≫ G.source.hom = c ≫ G.target.hom := by
    rw [groupoidCompose_source]
    exact wbc
  have wR : a ≫ G.source.hom = groupoidCompose G b c wbc ≫ G.target.hom := by
    calc
      a ≫ G.source.hom = b ≫ G.target.hom := wab
      _ = groupoidCompose G b c wbc ≫ G.target.hom := by
        rw [groupoidCompose_target]
  have hfg : stabilizerArrowHom G (lift f g ≫ stabilizerMul G) =
      groupoidCompose G a b wab := by
    simpa only [a, b, wab] using stabilizerArrowHom_mul G f g
  have hgk : stabilizerArrowHom G (lift g k ≫ stabilizerMul G) =
      groupoidCompose G b c wbc := by
    simpa only [b, c, wbc] using stabilizerArrowHom_mul G g k
  calc
    stabilizerArrowHom G (lift (lift f g ≫ stabilizerMul G) k ≫ stabilizerMul G) =
        groupoidCompose G (stabilizerArrowHom G (lift f g ≫ stabilizerMul G)) c
          (stabilizerArrowHom_composable G (lift f g ≫ stabilizerMul G) k) :=
      stabilizerArrowHom_mul G (lift f g ≫ stabilizerMul G) k
    _ = groupoidCompose G (groupoidCompose G a b wab) c wL :=
      groupoidCompose_congr G _ _ hfg rfl
    _ = groupoidCompose G a (groupoidCompose G b c wbc) wR :=
      groupoidCompose_assoc G a b c wab wbc wL wR
    _ = groupoidCompose G a (stabilizerArrowHom G (lift g k ≫ stabilizerMul G))
          (stabilizerArrowHom_composable G f (lift g k ≫ stabilizerMul G)) :=
      (groupoidCompose_congr G _ _ rfl hgk).symm
    _ = stabilizerArrowHom G (lift f (lift g k ≫ stabilizerMul G) ≫ stabilizerMul G) :=
      (stabilizerArrowHom_mul G f (lift g k ≫ stabilizerMul G)).symm

/-- A group-object structure on the stabilizer whose multiplication agrees with groupoid
composition after projecting generalized points to their underlying arrows. -/
def IsStabilizerGroupStructure (G : GroupoidInAlgebraicSpaces C S hS B)
    (h : GrpObj (stabilizer G)) : Prop :=
  letI := h
  ∀ (T : Over G.objects.obj) (f g : T ⟶ stabilizer G),
    ∃ (w : (f.left ≫ stabilizerArrow G) ≫ G.source.hom =
        (g.left ≫ stabilizerArrow G) ≫ G.target.hom),
      (lift f g ≫ μ[stabilizer G]).left ≫ stabilizerArrow G =
        pullback.lift (f.left ≫ stabilizerArrow G) (g.left ≫ stabilizerArrow G) w ≫
          G.comp.hom

/-- **Stacks 0447.** The stabilizer of a groupoid in algebraic spaces is a group object in the
slice over the object space, with groupoid composition as multiplication. -/
@[stacks 0447]
noncomputable def stabilizerGroupStructure (G : GroupoidInAlgebraicSpaces C S hS B) :
    { h : GrpObj (stabilizer G) // IsStabilizerGroupStructure G h } := by
  let h : GrpObj (stabilizer G) := {
    one := stabilizerOne G
    mul := stabilizerMul G
    inv := stabilizerInv G
    one_mul := by
      rw [← lift_comp_fst_snd (stabilizerOne G ▷ stabilizer G)]
      simp only [whiskerRight_fst, whiskerRight_snd]
      apply stabilizer_hom_ext G
      rw [stabilizerArrowHom_mul]
      let f := snd (𝟙_ (Over G.objects.obj)) (stabilizer G)
      have hu : stabilizerArrowHom G
          (fst (𝟙_ (Over G.objects.obj)) (stabilizer G) ≫ stabilizerOne G) =
          stabilizerArrowHom G f ≫ G.target.hom ≫ (identityArrow G).hom := by
        rw [stabilizerArrowHom_one]
        simpa [stabilizerArrowHom, Category.assoc, f] using
          congrArg (fun z => z ≫ (identityArrow G).hom)
            (stabilizerArrowHom_target G f).symm
      calc
        groupoidCompose G
            (stabilizerArrowHom G
              (fst (𝟙_ (Over G.objects.obj)) (stabilizer G) ≫ stabilizerOne G))
            (stabilizerArrowHom G f) _ =
          groupoidCompose G (identityAfterTarget G (stabilizerArrowHom G f))
            (stabilizerArrowHom G f) (identityAfterTarget_composable G _) :=
          groupoidCompose_congr G _ _ hu rfl
        _ = stabilizerArrowHom G f := groupoidCompose_leftIdentity G _
    mul_one := by
      rw [← lift_comp_fst_snd (stabilizer G ◁ stabilizerOne G)]
      simp only [whiskerLeft_fst, whiskerLeft_snd]
      apply stabilizer_hom_ext G
      rw [stabilizerArrowHom_mul]
      let f := fst (stabilizer G) (𝟙_ (Over G.objects.obj))
      have hu : stabilizerArrowHom G
          (snd (stabilizer G) (𝟙_ (Over G.objects.obj)) ≫ stabilizerOne G) =
          stabilizerArrowHom G f ≫ G.source.hom ≫ (identityArrow G).hom := by
        rw [stabilizerArrowHom_one]
        simpa [stabilizerArrowHom, Category.assoc, f] using
          congrArg (fun z => z ≫ (identityArrow G).hom)
            (stabilizerArrowHom_source G f).symm
      calc
        groupoidCompose G (stabilizerArrowHom G f)
            (stabilizerArrowHom G
              (snd (stabilizer G) (𝟙_ (Over G.objects.obj)) ≫ stabilizerOne G)) _ =
          groupoidCompose G (stabilizerArrowHom G f)
            (identityAfterSource G (stabilizerArrowHom G f))
            (identityAfterSource_composable G _) :=
          groupoidCompose_congr G _ _ rfl hu
        _ = stabilizerArrowHom G f := groupoidCompose_rightIdentity G _
    mul_assoc := by
      let H := stabilizer G
      let f : (H ⊗ H) ⊗ H ⟶ H := fst (H ⊗ H) H ≫ fst H H
      let g : (H ⊗ H) ⊗ H ⟶ H := fst (H ⊗ H) H ≫ snd H H
      let k : (H ⊗ H) ⊗ H ⟶ H := snd (H ⊗ H) H
      have hfg : lift f g = fst (H ⊗ H) H := by
        dsimp [f, g]
        rw [← comp_lift, lift_fst_snd, Category.comp_id]
      have hgk : lift g k = (α_ H H H).hom ≫ snd H (H ⊗ H) := by
        apply hom_ext
        · simp only [lift_fst, Category.assoc, associator_hom_snd_fst]
          rfl
        · simp only [lift_snd, Category.assoc, associator_hom_snd_snd]
          rfl
      have eL : lift (lift f g ≫ stabilizerMul G) k = stabilizerMul G ▷ H := by
        apply hom_ext
        · simp only [lift_fst, whiskerRight_fst, hfg]
          rfl
        · simp only [lift_snd, whiskerRight_snd]
          rfl
      have eR : lift f (lift g k ≫ stabilizerMul G) =
          (α_ H H H).hom ≫ H ◁ stabilizerMul G := by
        apply hom_ext
        · simp only [lift_fst, Category.assoc, whiskerLeft_fst, associator_hom_fst]
          rfl
        · simp only [lift_snd, Category.assoc, whiskerLeft_snd, hgk]
      apply stabilizer_hom_ext G
      simpa only [eL, eR, Category.assoc, H] using stabilizerArrowHom_mul_assoc G f g k
    left_inv := by
      apply stabilizer_hom_ext G
      rw [stabilizerArrowHom_mul]
      let f := stabilizerArrowHom G (𝟙 (stabilizer G))
      have hi : stabilizerArrowHom G (stabilizerInv G) = f ≫ groupoidInverse G := by
        simpa only [Category.id_comp] using stabilizerArrowHom_inv G (𝟙 (stabilizer G))
      have hu : stabilizerArrowHom G (toUnit (stabilizer G) ≫ stabilizerOne G) =
          f ≫ G.source.hom ≫ (identityArrow G).hom := by
        rw [stabilizerArrowHom_one]
        simpa [stabilizerArrowHom, Category.assoc, f] using
          congrArg (fun z => z ≫ (identityArrow G).hom)
            (stabilizerArrowHom_source G (𝟙 (stabilizer G))).symm
      calc
        groupoidCompose G (stabilizerArrowHom G (stabilizerInv G))
            (stabilizerArrowHom G (𝟙 (stabilizer G))) _ =
          groupoidCompose G (f ≫ groupoidInverse G) f _ :=
          groupoidCompose_congr G _ _ hi rfl
        _ = identityAfterSource G f := groupoidCompose_inverseRight G f
        _ = stabilizerArrowHom G (toUnit (stabilizer G) ≫ stabilizerOne G) := hu.symm
    right_inv := by
      apply stabilizer_hom_ext G
      rw [stabilizerArrowHom_mul]
      let f := stabilizerArrowHom G (𝟙 (stabilizer G))
      have hi : stabilizerArrowHom G (stabilizerInv G) = f ≫ groupoidInverse G := by
        simpa only [Category.id_comp] using stabilizerArrowHom_inv G (𝟙 (stabilizer G))
      have hu : stabilizerArrowHom G (toUnit (stabilizer G) ≫ stabilizerOne G) =
          f ≫ G.target.hom ≫ (identityArrow G).hom := by
        rw [stabilizerArrowHom_one]
        simpa [stabilizerArrowHom, Category.assoc, f] using
          congrArg (fun z => z ≫ (identityArrow G).hom)
            (stabilizerArrowHom_target G (𝟙 (stabilizer G))).symm
      calc
        groupoidCompose G (stabilizerArrowHom G (𝟙 (stabilizer G)))
            (stabilizerArrowHom G (stabilizerInv G)) _ =
          groupoidCompose G f (f ≫ groupoidInverse G) _ :=
          groupoidCompose_congr G _ _ rfl hi
        _ = identityAfterTarget G f := groupoidCompose_inverseLeft G f
        _ = stabilizerArrowHom G (toUnit (stabilizer G) ≫ stabilizerOne G) := hu.symm }
  exact ⟨h, by
    let _ := h
    intro T f g
    let w := stabilizerArrowHom_composable G f g
    refine ⟨w, ?_⟩
    change stabilizerArrowHom G (lift f g ≫ stabilizerMul G) =
      pullback.lift (stabilizerArrowHom G f) (stabilizerArrowHom G g) w ≫ G.comp.hom
    simpa only [groupoidCompose] using stabilizerArrowHom_mul G f g⟩

/-- The canonical group-object structure on the stabilizer of a groupoid in algebraic
spaces. -/
noncomputable instance (G : GroupoidInAlgebraicSpaces C S hS B) : GrpObj (stabilizer G) :=
  (stabilizerGroupStructure G).1

/-- Multiplication in the stabilizer is groupoid composition on generalized arrows. -/
theorem stabilizer_mul_comp_arrow (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : Over G.objects.obj) (f g : T ⟶ stabilizer G) :
    ∃ (w : (f.left ≫ stabilizerArrow G) ≫ G.source.hom =
        (g.left ≫ stabilizerArrow G) ≫ G.target.hom),
      (lift f g ≫ μ[stabilizer G]).left ≫ stabilizerArrow G =
        pullback.lift (f.left ≫ stabilizerArrow G) (g.left ≫ stabilizerArrow G) w ≫
          G.comp.hom :=
  (stabilizerGroupStructure G).2 T f g

/-- The stabilizer group algebraic space over the object space of a groupoid in algebraic
spaces. -/
@[stacks 0448 "the stabilizer as a group algebraic space over the object space"]
noncomputable def stabilizerGroup (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.GroupAlgebraicSpace C S hS G.objects.obj G.objects.property :=
  ⟨⟨stabilizer G⟩, (stabilizerOverBase G).property⟩

end AlgebraicGeometry.GroupoidInAlgebraicSpaces
