module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Action
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Torsor
public import StacksCore.Tactic.StacksAttribute

/-!
# The stabilizer pseudo-torsor of a groupoid scheme

The stabilizer, pulled back to the pair scheme of a groupoid, acts on its arrows by
composition.  This action makes the arrows a pseudo-torsor over the pair scheme.

## Main definitions

* `AlgebraicGeometry.stabilizerOverPairs` is the pullback of the stabilizer to the pair scheme.
* `AlgebraicGeometry.arrowsOverPairs` is the arrow scheme over the pair scheme.
* `AlgebraicGeometry.stabilizerActionOverPairs` is the action of `stabilizerOverPairs` on
  `arrowsOverPairs` which, on generalized points, agrees with the stabilizer action over the
  target after projection.

## Main results

* `AlgebraicGeometry.stabilizerActionOverPairs_pseudoTorsor` asserts the pseudo-torsor
  property.

## References

* [Stacks Project, Tag 04Q2](https://stacks.math.columbia.edu/tag/04Q2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The first projection from the scheme of pairs to the object scheme. -/
abbrev firstProjection {S : Scheme.{u}} (G : GroupoidScheme S) :
    (G.objects ⊗ G.objects).left ⟶ G.objects.left :=
  (fst G.objects G.objects).left

/-- The stabilizer group scheme after base change to the pair scheme. -/
abbrev stabilizerOverPairs {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over (G.objects ⊗ G.objects).left :=
  Over.mk (pullback.snd (stabilizer G).hom (firstProjection G))

/-- The arrow scheme over the pair scheme by `(target, source)`. -/
abbrev arrowsOverPairs {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over (G.objects ⊗ G.objects).left :=
  Over.mk (sourceTarget G).left

/-- The base-changed stabilizer is a group scheme over the pair scheme. -/
instance stabilizerOverPairsGrpObj {S : Scheme.{u}} (G : GroupoidScheme S) :
    GrpObj (stabilizerOverPairs G) := by
  letI : GrpObj (Over.mk (stabilizer G).hom) :=
    inferInstanceAs (GrpObj (stabilizer G))
  exact Over.grpObjMkPullbackSnd

/-- A generalized point of the base-changed stabilizer, projected to the stabilizer. -/
def stabilizerPoint {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left} (g : T ⟶ stabilizerOverPairs G) :
    (Over.map (firstProjection G)).obj T ⟶ stabilizer G :=
  Over.homMk (g.left ≫ pullback.fst (stabilizer G).hom (firstProjection G))
    (by
      change g.left ≫ pullback.fst (stabilizer G).hom (firstProjection G) ≫
          (stabilizer G).hom = T.hom ≫ firstProjection G
      calc
        g.left ≫ pullback.fst (stabilizer G).hom (firstProjection G) ≫
            (stabilizer G).hom =
          g.left ≫ pullback.snd (stabilizer G).hom (firstProjection G) ≫
            firstProjection G := by simp only [pullback.condition]
        _ = T.hom ≫ firstProjection G := by
          rw [← Category.assoc]
          exact congrArg (· ≫ firstProjection G) g.w)

/-- A generalized arrow over a pair, viewed as an arrow over its target. -/
def arrowPoint {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left} (r : T ⟶ arrowsOverPairs G) :
    (Over.map (firstProjection G)).obj T ⟶ arrowsOverTarget G :=
  Over.homMk r.left (by
    change r.left ≫ G.target.left = T.hom ≫ firstProjection G
    calc
      r.left ≫ G.target.left = r.left ≫ (sourceTarget G).left ≫ firstProjection G := by
        simp only [sourceTarget, firstProjection, Over.lift_left, Over.fst_left,
          pullback.lift_fst]
      _ = T.hom ≫ firstProjection G := by
        rw [← Category.assoc]
        exact congrArg (· ≫ firstProjection G) r.w)

/-- The action on the pair scheme agrees with the original stabilizer action after projection
to the target. -/
def IsInducedAction {S : Scheme.{u}} (G : GroupoidScheme S)
    (h : ModObj (stabilizerOverPairs G) (arrowsOverPairs G)) : Prop :=
  letI := h
  ∀ (T : Over (G.objects ⊗ G.objects).left)
    (g : T ⟶ stabilizerOverPairs G) (r : T ⟶ arrowsOverPairs G),
    arrowPoint G (lift g r ≫ γ[stabilizerOverPairs G, arrowsOverPairs G]) =
      lift (stabilizerPoint G g) (arrowPoint G r) ≫
        γ[stabilizer G, arrowsOverTarget G]

/-- The action morphism of the base-changed stabilizer on the arrows over the pair scheme:
on generalized points it is composition in the groupoid. -/
private noncomputable def pairActionMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerOverPairs G ⊗ arrowsOverPairs G ⟶ arrowsOverPairs G := by
  let P : Over (G.objects ⊗ G.objects).left :=
    stabilizerOverPairs G ⊗ arrowsOverPairs G
  let T := (Over.map (firstProjection G)).obj P
  let g : T ⟶ stabilizer G := stabilizerPoint G (fst _ _)
  let r : T ⟶ arrowsOverTarget G := arrowPoint G (snd _ _)
  let a := stabilizerArrowHom G g
  let b := arrowOverTargetHom G r
  let w := stabilizerArrowHom_arrowOverTarget_composable G g r
  let c : (Over.map G.objects.hom).obj T ⟶ G.arrows := G.compose a b w
  have hfst : (sourceTarget G).left ≫ pullback.fst G.objects.hom G.objects.hom =
      G.target.left := by
    rw [sourceTarget, Over.lift_left, pullback.lift_fst]
  have hsnd : (sourceTarget G).left ≫ pullback.snd G.objects.hom G.objects.hom =
      G.source.left := by
    rw [sourceTarget, Over.lift_left, pullback.lift_snd]
  refine Over.homMk c.left ?_
  change c.left ≫ (sourceTarget G).left = P.hom
  apply pullback.hom_ext
  · -- The target of a composite is the target of its first arrow.
    have hcomp : G.comp.left ≫ G.target.left =
        (pullback.fst G.source G.target).left ≫ G.target.left :=
      congrArg Over.Hom.left G.target_comp
    calc
      c.left ≫ (sourceTarget G).left ≫ pullback.fst G.objects.hom G.objects.hom =
          c.left ≫ G.target.left := by rw [hfst]
      _ = a.left ≫ G.target.left := by
        dsimp [c, GroupoidScheme.compose]
        calc
          _ = (pullback.lift a b w).left ≫ (G.comp.left ≫ G.target.left) := by
            rw [Category.assoc]
          _ = (pullback.lift a b w).left ≫
              ((pullback.fst G.source G.target).left ≫ G.target.left) := by rw [hcomp]
          _ = a.left ≫ G.target.left := by
            have hlift : (pullback.lift a b w).left ≫
                (pullback.fst G.source G.target).left = a.left :=
              congrArg Over.Hom.left (pullback.lift_fst a b w)
            rw [← Category.assoc, hlift]
      _ = P.hom ≫ pullback.fst G.objects.hom G.objects.hom := by
        have hh : a.left ≫ G.target.left = T.hom :=
          congrArg Over.Hom.left (stabilizerArrowHom_target G g)
        simpa [T, firstProjection] using hh
  · -- The source of a composite is the source of its second arrow.
    have hcomp : G.comp.left ≫ G.source.left =
        (pullback.snd G.source G.target).left ≫ G.source.left :=
      congrArg Over.Hom.left G.source_comp
    calc
      c.left ≫ (sourceTarget G).left ≫ pullback.snd G.objects.hom G.objects.hom =
          c.left ≫ G.source.left := by rw [hsnd]
      _ = b.left ≫ G.source.left := by
        dsimp [c, GroupoidScheme.compose]
        calc
          _ = (pullback.lift a b w).left ≫ (G.comp.left ≫ G.source.left) := by
            rw [Category.assoc]
          _ = (pullback.lift a b w).left ≫
              ((pullback.snd G.source G.target).left ≫ G.source.left) := by rw [hcomp]
          _ = b.left ≫ G.source.left := by
            have hlift : (pullback.lift a b w).left ≫
                (pullback.snd G.source G.target).left = b.left :=
              congrArg Over.Hom.left (pullback.lift_snd a b w)
            rw [← Category.assoc, hlift]
      _ = P.hom ≫ pullback.snd G.objects.hom G.objects.hom := by
        have hh := congrArg (fun q => q ≫ pullback.snd G.objects.hom G.objects.hom)
          (snd _ _ : P ⟶ arrowsOverPairs G).w
        calc
          (snd _ _ : P ⟶ arrowsOverPairs G).left ≫ G.source.left =
              (snd _ _ : P ⟶ arrowsOverPairs G).left ≫
                ((sourceTarget G).left ≫ pullback.snd G.objects.hom G.objects.hom) := by
                  rw [hsnd]
          _ = ((snd _ _ : P ⟶ arrowsOverPairs G).left ≫ (sourceTarget G).left) ≫
                pullback.snd G.objects.hom G.objects.hom := (Category.assoc _ _ _).symm
          _ = P.hom ≫ pullback.snd G.objects.hom G.objects.hom := hh

/-- A generalized point of the arrows over the pair scheme is determined by the generalized arrow
over the target that it induces. -/
private lemma arrowPoint_injective {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left} {f g : T ⟶ arrowsOverPairs G}
    (h : arrowPoint G f = arrowPoint G g) : f = g :=
  Over.OverMorphism.ext (congrArg (fun q => q.left) h)

/-- The unit of the base-changed stabilizer projects to the unit of the stabilizer. -/
private lemma stabilizerPoint_one {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left}
    (k : T ⟶ 𝟙_ (Over (G.objects ⊗ G.objects).left)) :
    stabilizerPoint G (k ≫ η[stabilizerOverPairs G]) =
      Over.homMk ((Over.map (firstProjection G)).obj T).hom ≫ η[stabilizer G] := by
  let : GrpObj (Over.mk (stabilizer G).hom) := inferInstanceAs (GrpObj (stabilizer G))
  apply Over.OverMorphism.ext
  change (k ≫ η[stabilizerOverPairs G]).left ≫
      pullback.fst (stabilizer G).hom (firstProjection G) =
    ((Over.map (firstProjection G)).obj T).hom ≫ η[stabilizer G].left
  rw [Over.grpObjMkPullbackSnd_one]
  simp only [Over.comp_left, Over.ε_pullback_left, Over.pullback_map_left]
  let e := pullback.snd (𝟙 G.objects.left) (firstProjection G)
  let f₀ := pullback.fst (𝟙 G.objects.left) (firstProjection G)
  have hcompat : (f₀ ≫ η[stabilizer G].left) ≫ (stabilizer G).hom =
      e ≫ firstProjection G := by
    calc
      _ = f₀ ≫ (η[stabilizer G].left ≫ (stabilizer G).hom) := by
        simp only [Category.assoc]
      _ = f₀ := by rw [η[stabilizer G].w]; exact Category.comp_id _
      _ = e ≫ firstProjection G := by
        simpa [e, f₀] using
          (pullback.condition (f := 𝟙 G.objects.left) (g := firstProjection G))
  have hmap : pullback.lift (f₀ ≫ η[stabilizer G].left) e
        hcompat ≫ pullback.fst (stabilizer G).hom (firstProjection G) =
      f₀ ≫ η[stabilizer G].left := pullback.lift_fst _ _ _
  have hc : f₀ = e ≫ firstProjection G := by
    simpa [e, f₀] using
      (pullback.condition (f := 𝟙 G.objects.left) (g := firstProjection G))
  have hc' : pullback.fst (𝟙 G.objects.left) (firstProjection G) =
      pullback.snd (𝟙 G.objects.left) (firstProjection G) ≫ firstProjection G := by
    simpa [e, f₀] using hc
  have hfst : inv (pullback.snd (𝟙 G.objects.left) (firstProjection G)) ≫
      pullback.fst (𝟙 G.objects.left) (firstProjection G) = firstProjection G := by
    calc
      _ = inv (pullback.snd (𝟙 G.objects.left) (firstProjection G)) ≫
          (pullback.snd (𝟙 G.objects.left) (firstProjection G) ≫ firstProjection G) := by
            rw [hc']
      _ = firstProjection G := by simp [← Category.assoc]
  simp only [Over.tensorUnit_hom] at hmap ⊢
  simp only [e, f₀] at hmap ⊢
  calc
    _ = k.left ≫ inv (pullback.snd (𝟙 G.objects.left) (firstProjection G)) ≫
          (pullback.lift (pullback.fst (𝟙 G.objects.left) (firstProjection G) ≫
            η[stabilizer G].left)
            (pullback.snd (𝟙 G.objects.left) (firstProjection G)) _ ≫
            pullback.fst (stabilizer G).hom (firstProjection G)) := by
              simp only [Category.assoc]
    _ = k.left ≫ inv (pullback.snd (𝟙 G.objects.left) (firstProjection G)) ≫
          (pullback.fst (𝟙 G.objects.left) (firstProjection G) ≫
            η[stabilizer G].left) := by
              exact congrArg (fun q => k.left ≫
                inv (pullback.snd (𝟙 G.objects.left) (firstProjection G)) ≫ q) hmap
    _ = k.left ≫ firstProjection G ≫ η[stabilizer G].left := by
      simpa only [Category.assoc] using congrArg
        (fun q => k.left ≫ q ≫ η[stabilizer G].left) hfst
    _ = ((Over.map (firstProjection G)).obj T).hom ≫ η[stabilizer G].left := by
      change k.left ≫ firstProjection G ≫ η[stabilizer G].left =
        (T.hom ≫ firstProjection G) ≫ η[stabilizer G].left
      have hk : k.left = T.hom := by simpa using k.w
      rw [hk, Category.assoc]

/-- Multiplication in the base-changed stabilizer projects to multiplication in the stabilizer. -/
private lemma stabilizerPoint_mul {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left}
    (g h : T ⟶ stabilizerOverPairs G) :
    stabilizerPoint G (lift g h ≫ μ[stabilizerOverPairs G]) =
      lift (stabilizerPoint G g) (stabilizerPoint G h) ≫ μ[stabilizer G] := by
  let : GrpObj (Over.mk (stabilizer G).hom) := inferInstanceAs (GrpObj (stabilizer G))
  apply Over.OverMorphism.ext
  change (lift g h ≫ μ[stabilizerOverPairs G]).left ≫
      pullback.fst (stabilizer G).hom (firstProjection G) =
    (lift (stabilizerPoint G g) (stabilizerPoint G h) ≫ μ[stabilizer G]).left
  rw [Over.grpObjMkPullbackSnd_mul]
  simp only [Over.comp_left, Over.pullback_map_left]
  let Q := Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom
  have hcompat :
      (pullback.fst (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom
          (firstProjection G) ≫ μ[stabilizer G].left) ≫
          (stabilizer G).hom =
        pullback.snd (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom
          (firstProjection G) ≫ firstProjection G := by
    calc
      _ = pullback.fst (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom
          (firstProjection G) ≫
          (μ[stabilizer G].left ≫ (stabilizer G).hom) := by
            simp only [Category.assoc]
      _ = pullback.fst (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom
          (firstProjection G) ≫
          (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom := by
        simpa [Q] using congrArg
          (fun q => pullback.fst (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom
              (firstProjection G) ≫ q)
          (μ[stabilizer G].w)
      _ = pullback.snd (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom
          (firstProjection G) ≫ firstProjection G :=
        pullback.condition
  have hmap :
      pullback.lift
          (pullback.fst (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom
            (firstProjection G) ≫ μ[stabilizer G].left)
          (pullback.snd (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom
            (firstProjection G)) hcompat ≫
          pullback.fst (stabilizer G).hom (firstProjection G) =
        pullback.fst (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom
          (firstProjection G) ≫ μ[stabilizer G].left :=
    pullback.lift_fst _ _ _
  have hliftFst : (lift g h).left ≫
      pullback.fst (stabilizerOverPairs G).hom (stabilizerOverPairs G).hom ≫
      pullback.fst (stabilizer G).hom (firstProjection G) = (stabilizerPoint G g).left := by
    have hf := congrArg Over.Hom.left (lift_fst g h)
    change (lift g h).left ≫ pullback.fst (stabilizerOverPairs G).hom
      (stabilizerOverPairs G).hom = g.left at hf
    calc
      _ = g.left ≫ pullback.fst (stabilizer G).hom (firstProjection G) := by
        rw [← Category.assoc, hf]
      _ = (stabilizerPoint G g).left := rfl
  have hliftSnd : (lift g h).left ≫
      pullback.snd (stabilizerOverPairs G).hom (stabilizerOverPairs G).hom ≫
      pullback.fst (stabilizer G).hom (firstProjection G) = (stabilizerPoint G h).left := by
    have hf := congrArg Over.Hom.left (lift_snd g h)
    change (lift g h).left ≫ pullback.snd (stabilizerOverPairs G).hom
      (stabilizerOverPairs G).hom = h.left at hf
    calc
      _ = h.left ≫ pullback.fst (stabilizer G).hom (firstProjection G) := by
        rw [← Category.assoc, hf]
      _ = (stabilizerPoint G h).left := rfl
  calc
    _ = (lift g h).left ≫
          (Functor.LaxMonoidal.μ (Over.pullback (firstProjection G))
            (Over.mk (stabilizer G).hom) (Over.mk (stabilizer G).hom)).left ≫
          (pullback.fst (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom
            (firstProjection G) ≫ μ[stabilizer G].left) :=
              congrArg (fun q => (lift g h).left ≫
                (Functor.LaxMonoidal.μ (Over.pullback (firstProjection G))
                  (Over.mk (stabilizer G).hom) (Over.mk (stabilizer G).hom)).left ≫ q)
                hmap
    _ = _ := by
      change ((lift g h).left ≫
          (Functor.LaxMonoidal.μ (Over.pullback (firstProjection G))
            (Over.mk (stabilizer G).hom) (Over.mk (stabilizer G).hom)).left ≫
          pullback.fst (Over.mk (stabilizer G).hom ⊗ Over.mk (stabilizer G).hom).hom
            (firstProjection G)) ≫ μ[stabilizer G].left =
        (lift (stabilizerPoint G g) (stabilizerPoint G h)).left ≫ μ[stabilizer G].left
      apply congrArg (fun q => q ≫ μ[stabilizer G].left)
      apply pullback.hom_ext
      · have hp := Over.μ_pullback_left_fst_fst'
          (f := firstProjection G) (g₁ := (stabilizer G).hom) (g₂ := (stabilizer G).hom)
        calc
          _ = (lift g h).left ≫
              pullback.fst (stabilizerOverPairs G).hom (stabilizerOverPairs G).hom ≫
              pullback.fst (stabilizer G).hom (firstProjection G) :=
                congrArg (fun q => (lift g h).left ≫ q) hp
          _ = (stabilizerPoint G g).left := hliftFst
          _ = (lift (stabilizerPoint G g) (stabilizerPoint G h)).left ≫
              pullback.fst (stabilizer G).hom (stabilizer G).hom := by
                symm
                have hf := congrArg Over.Hom.left
                  (lift_fst (stabilizerPoint G g) (stabilizerPoint G h))
                change (lift (stabilizerPoint G g) (stabilizerPoint G h)).left ≫
                  (fst (stabilizer G) (stabilizer G)).left = (stabilizerPoint G g).left at hf
                simpa only [Over.fst_left] using hf
      · have hp := Over.μ_pullback_left_fst_snd'
          (f := firstProjection G) (g₁ := (stabilizer G).hom) (g₂ := (stabilizer G).hom)
        calc
          _ = (lift g h).left ≫
              pullback.snd (stabilizerOverPairs G).hom (stabilizerOverPairs G).hom ≫
              pullback.fst (stabilizer G).hom (firstProjection G) :=
                congrArg (fun q => (lift g h).left ≫ q) hp
          _ = (stabilizerPoint G h).left := hliftSnd
          _ = (lift (stabilizerPoint G g) (stabilizerPoint G h)).left ≫
              pullback.snd (stabilizer G).hom (stabilizer G).hom := by
                symm
                have hf := congrArg Over.Hom.left
                  (lift_snd (stabilizerPoint G g) (stabilizerPoint G h))
                change (lift (stabilizerPoint G g) (stabilizerPoint G h)).left ≫
                  (snd (stabilizer G) (stabilizer G)).left = (stabilizerPoint G h).left at hf
                simpa only [Over.snd_left] using hf

/-- The action over the pair scheme agrees, after projection, with the stabilizer action over the
target. -/
private lemma pairActionMap_spec {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left}
    (g : T ⟶ stabilizerOverPairs G) (r : T ⟶ arrowsOverPairs G) :
    arrowPoint G (lift g r ≫ pairActionMap G) =
      lift (stabilizerPoint G g) (arrowPoint G r) ≫
        γ[stabilizer G, arrowsOverTarget G] := by
  let P : Over (G.objects ⊗ G.objects).left :=
    stabilizerOverPairs G ⊗ arrowsOverPairs G
  let T₀ := (Over.map (firstProjection G)).obj P
  let T₁ := (Over.map (firstProjection G)).obj T
  let U := (Over.map G.objects.hom).obj T₀
  let V := (Over.map G.objects.hom).obj T₁
  let gs := fst (stabilizerOverPairs G) (arrowsOverPairs G)
  let ar := snd (stabilizerOverPairs G) (arrowsOverPairs G)
  let a : U ⟶ G.arrows :=
    stabilizerArrowHom G (stabilizerPoint G gs)
  let b : U ⟶ G.arrows := arrowOverTargetHom G (arrowPoint G ar)
  let w : a ≫ G.source = b ≫ G.target := stabilizerArrowHom_arrowOverTarget_composable G
    (stabilizerPoint G gs) (arrowPoint G ar)
  let kPair : T₁ ⟶ T₀ := (Over.map (firstProjection G)).map (lift g r)
  let k : V ⟶ U := (Over.map G.objects.hom).map kPair
  have ha : k ≫ a = stabilizerArrowHom G (stabilizerPoint G g) := by
    apply Over.OverMorphism.ext
    have hf := congrArg Over.Hom.left (lift_fst g r)
    change (lift g r ≫ gs).left ≫
      pullback.fst (stabilizer G).hom (firstProjection G) ≫ stabilizerArrow G =
      g.left ≫ pullback.fst (stabilizer G).hom (firstProjection G) ≫ stabilizerArrow G
    rw [hf]
  have hb : k ≫ b = arrowOverTargetHom G (arrowPoint G r) := by
    apply Over.OverMorphism.ext
    change (lift g r ≫ ar).left = r.left
    exact congrArg Over.Hom.left (lift_snd g r)
  have hbase : arrowOverTargetHom G (arrowPoint G (pairActionMap G)) =
      G.compose a b w := by
    apply Over.OverMorphism.ext
    rfl
  have hpoint : arrowPoint G (lift g r ≫ pairActionMap G) =
      kPair ≫ arrowPoint G (pairActionMap G) := by
    apply Over.OverMorphism.ext
    rfl
  have hleft0 := congrArg (arrowOverTargetHom G) hpoint
  rw [arrowOverTargetHom_comp, hbase, groupoidCompose_pre G k a b w] at hleft0
  have hleft : arrowOverTargetHom G (arrowPoint G (lift g r ≫ pairActionMap G)) =
      G.compose (stabilizerArrowHom G (stabilizerPoint G g))
        (arrowOverTargetHom G (arrowPoint G r))
        (stabilizerArrowHom_arrowOverTarget_composable G
          (stabilizerPoint G g) (arrowPoint G r)) := by
    simpa only [ha, hb] using hleft0
  have hright := stabilizer_smul_arrow G T₁ (stabilizerPoint G g)
    (arrowPoint G r)
  have h : arrowOverTargetHom G (arrowPoint G (lift g r ≫ pairActionMap G)) =
      arrowOverTargetHom G
        (lift (stabilizerPoint G g) (arrowPoint G r) ≫
          γ[stabilizer G, arrowsOverTarget G]) := hleft.trans hright.symm
  exact arrowOverTargetHom_injective G h

/-- A generalized arrow over a pair has source the second component of that pair. -/
private lemma arrowPoint_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left} (r : T ⟶ arrowsOverPairs G) :
    (arrowOverTargetHom G (arrowPoint G r) ≫ G.source).left =
      T.hom ≫ (snd G.objects G.objects).left := by
  have hs : (sourceTarget G).left ≫ (snd G.objects G.objects).left = G.source.left := by
    simp [sourceTarget, Over.lift_left, Over.snd_left]
  change r.left ≫ G.source.left = T.hom ≫ (snd G.objects G.objects).left
  calc
    r.left ≫ G.source.left = r.left ≫ (sourceTarget G).left ≫
        (snd G.objects G.objects).left := by rw [hs]
    _ = T.hom ≫ (snd G.objects G.objects).left :=
      congrArg (fun q => q ≫ (snd G.objects G.objects).left) r.w

/-- A loop at the first component of a pair has the same source and target as the diagonal. -/
private lemma loop_comp_sourceTarget {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left}
    (f : (Over.map (G.objects.hom)).obj
      ((Over.map (firstProjection G)).obj T) ⟶ G.arrows)
    (hsource : (f ≫ G.source).left = T.hom ≫ (fst G.objects G.objects).left)
    (htarget : (f ≫ G.target).left = T.hom ≫ (fst G.objects G.objects).left) :
    f ≫ sourceTarget G =
      (Over.homMk ((Over.map (firstProjection G)).obj T).hom :
        (Over.map G.objects.hom).obj ((Over.map (firstProjection G)).obj T) ⟶ G.objects) ≫
        diagonal G := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have h₁ : (sourceTarget G).left ≫ pullback.fst G.objects.hom G.objects.hom =
        G.target.left := by
      simp [sourceTarget, Over.lift_left]
    have h₂ : (diagonal G).left ≫ pullback.fst G.objects.hom G.objects.hom = 𝟙 _ := by
      simp [diagonal, Over.lift_left]
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, h₁, h₂,
      Category.comp_id]
    exact htarget
  · have h₁ : (sourceTarget G).left ≫ pullback.snd G.objects.hom G.objects.hom =
        G.source.left := by
      simp [sourceTarget, Over.lift_left]
    have h₂ : (diagonal G).left ≫ pullback.snd G.objects.hom G.objects.hom = 𝟙 _ := by
      simp [diagonal, Over.lift_left]
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, h₁, h₂,
      Category.comp_id]
    exact hsource

/-- A generalized arrow whose source and target are both the first component of a pair is a
generalized point of the stabilizer. -/
private noncomputable def stabilizerPointOfLoop {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left}
    (f : (Over.map (G.objects.hom)).obj
      ((Over.map (firstProjection G)).obj T) ⟶ G.arrows)
    (hsource : (f ≫ G.source).left = T.hom ≫ (fst G.objects G.objects).left)
    (htarget : (f ≫ G.target).left = T.hom ≫ (fst G.objects G.objects).left) :
    (Over.map (firstProjection G)).obj T ⟶ stabilizer G := by
  let T₀ := (Over.map (firstProjection G)).obj T
  let B := (Over.map G.objects.hom).obj T₀
  let b : B ⟶ G.objects := Over.homMk T₀.hom
  have hcompat := loop_comp_sourceTarget G f hsource htarget
  let L : B ⟶ stabilizerOverBase G := pullback.lift f b hcompat
  refine Over.homMk L.left ?_
  change L.left ≫ (pullback.snd (sourceTarget G) (diagonal G)).left = T₀.hom
  exact congrArg Over.Hom.left (pullback.lift_snd f b hcompat)

/-- The generalized arrow attached to `stabilizerPointOfLoop` is the arrow it was built from. -/
private lemma stabilizerArrowHom_pointOfLoop {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left}
    (f : (Over.map (G.objects.hom)).obj
      ((Over.map (firstProjection G)).obj T) ⟶ G.arrows)
    (hsource : (f ≫ G.source).left = T.hom ≫ (fst G.objects G.objects).left)
    (htarget : (f ≫ G.target).left = T.hom ≫ (fst G.objects G.objects).left) :
    stabilizerArrowHom G (stabilizerPointOfLoop G f hsource htarget) = f := by
  apply Over.OverMorphism.ext
  let T₀ := (Over.map (firstProjection G)).obj T
  let B := (Over.map G.objects.hom).obj T₀
  let b : B ⟶ G.objects := Over.homMk T₀.hom
  have hcompat := loop_comp_sourceTarget G f hsource htarget
  change (pullback.lift f b hcompat).left ≫
      (pullback.fst (sourceTarget G) (diagonal G)).left = f.left
  exact congrArg Over.Hom.left (pullback.lift_fst f b hcompat)

/-- A generalized point of the stabilizer over the first projection of a pair is a generalized
point of the base-changed stabilizer. -/
private noncomputable def stabilizerOverPairsPoint {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left}
    (g : (Over.map (firstProjection G)).obj T ⟶ stabilizer G) :
    T ⟶ stabilizerOverPairs G := by
  have hc : g.left ≫ (stabilizer G).hom = T.hom ≫ firstProjection G := g.w
  let q := pullback.lift g.left T.hom hc
  exact Over.homMk q (by
    change q ≫ pullback.snd (stabilizer G).hom (firstProjection G) = T.hom
    exact pullback.lift_snd g.left T.hom hc)

/-- Projecting `stabilizerOverPairsPoint` back to the stabilizer recovers the original point. -/
private lemma stabilizerPoint_stabilizerOverPairsPoint {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left}
    (g : (Over.map (firstProjection G)).obj T ⟶ stabilizer G) :
    stabilizerPoint G (stabilizerOverPairsPoint G g) = g := by
  apply Over.OverMorphism.ext
  dsimp [stabilizerPoint, stabilizerOverPairsPoint]
  exact pullback.lift_fst _ _ _

/-- A generalized point of the base-changed stabilizer is determined by its projection to the
stabilizer. -/
private lemma stabilizerPoint_injective {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over (G.objects ⊗ G.objects).left} {g h : T ⟶ stabilizerOverPairs G}
    (e : stabilizerPoint G g = stabilizerPoint G h) : g = h := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun q => q.left) e
  · have eg := g.w
    have eh := h.w
    change g.left ≫ pullback.snd (stabilizer G).hom (firstProjection G) =
      h.left ≫ pullback.snd (stabilizer G).hom (firstProjection G)
    calc
      _ = T.hom := by simpa [stabilizerOverPairs] using eg
      _ = _ := by simpa [stabilizerOverPairs] using eh.symm

/-- An action of the base-changed stabilizer with the required compatibility exists. -/
private theorem stabilizerActionOverPairs_nonempty {S : Scheme.{u}} (G : GroupoidScheme S) :
    Nonempty { h : ModObj (stabilizerOverPairs G) (arrowsOverPairs G) // IsInducedAction G h } := by
  let : ModObj (stabilizerOverPairs G) (arrowsOverPairs G) := {
    smul := pairActionMap G
    one_smul := by
      change η ▷ arrowsOverPairs G ≫ pairActionMap G =
        (λ_ (arrowsOverPairs G)).hom
      rw [← lift_comp_fst_snd (η[stabilizerOverPairs G] ▷ arrowsOverPairs G)]
      simp only [whiskerRight_fst, whiskerRight_snd]
      apply Over.OverMorphism.ext
      let T : Over (G.objects ⊗ G.objects).left :=
        𝟙_ (Over (G.objects ⊗ G.objects).left) ⊗ arrowsOverPairs G
      let k : T ⟶ 𝟙_ (Over (G.objects ⊗ G.objects).left) := fst _ _
      let r : T ⟶ arrowsOverPairs G := snd _ _
      have hlift : lift (k ≫ η[stabilizerOverPairs G]) r =
          η[stabilizerOverPairs G] ▷ arrowsOverPairs G := by
        apply hom_ext <;> simp [k, r]
      have hpoint := pairActionMap_spec G (k ≫ η[stabilizerOverPairs G]) r
      rw [hlift] at hpoint
      have hunit := stabilizerPoint_one G k
      have hunitAction :
          lift (stabilizerPoint G (k ≫ η[stabilizerOverPairs G]))
              (arrowPoint G r) ≫ γ[stabilizer G, arrowsOverTarget G] =
            arrowPoint G r := by
        rw [hunit]
        exact one_smul (M :=
          (Over.map (firstProjection G)).obj T ⟶ stabilizer G) (arrowPoint G r)
      have hright : arrowPoint G ((λ_ (arrowsOverPairs G)).hom) = arrowPoint G r := by
        apply Over.OverMorphism.ext
        rfl
      have hpoint' :
          arrowPoint G (η[stabilizerOverPairs G] ▷ arrowsOverPairs G ≫ pairActionMap G) =
            arrowPoint G r := hpoint.trans hunitAction
      exact congrArg (fun q => q.left)
        (arrowPoint_injective G (hpoint'.trans hright.symm))
    mul_smul := by
      change μ[stabilizerOverPairs G] ▷ arrowsOverPairs G ≫ pairActionMap G =
        (α_ (stabilizerOverPairs G) (stabilizerOverPairs G)
          (arrowsOverPairs G)).hom ≫
          stabilizerOverPairs G ◁ pairActionMap G ≫ pairActionMap G
      let T : Over (G.objects ⊗ G.objects).left :=
        (stabilizerOverPairs G ⊗ stabilizerOverPairs G) ⊗ arrowsOverPairs G
      let p12 : T ⟶ stabilizerOverPairs G ⊗ stabilizerOverPairs G := fst _ _
      let p3 : T ⟶ arrowsOverPairs G := snd _ _
      let p1 : T ⟶ stabilizerOverPairs G := p12 ≫ fst _ _
      let p2 : T ⟶ stabilizerOverPairs G := p12 ≫ snd _ _
      let m : T ⟶ stabilizerOverPairs G := p12 ≫ μ[stabilizerOverPairs G]
      let inner : T ⟶ arrowsOverPairs G := lift p2 p3 ≫ pairActionMap G
      let leftPair : T ⟶ stabilizerOverPairs G ⊗ arrowsOverPairs G := lift m p3
      let rightPair : T ⟶ stabilizerOverPairs G ⊗ arrowsOverPairs G := lift p1 inner
      have hleftPair : leftPair = μ[stabilizerOverPairs G] ▷ arrowsOverPairs G := by
        apply hom_ext
        · simp [leftPair, m, p12, p3]
        · simp [leftPair, p3]
      have hαsnd :
          (α_ (stabilizerOverPairs G) (stabilizerOverPairs G)
            (arrowsOverPairs G)).hom ≫
              snd (stabilizerOverPairs G)
                (stabilizerOverPairs G ⊗ arrowsOverPairs G) = lift p2 p3 := by
        apply hom_ext
        · simp [p2, p12]
        · simp [p3]
      have hrightPair : rightPair =
          (α_ (stabilizerOverPairs G) (stabilizerOverPairs G)
            (arrowsOverPairs G)).hom ≫
            stabilizerOverPairs G ◁ pairActionMap G := by
        apply hom_ext
        · simp [rightPair, inner, p1, p12, p3]
        · calc
            lift p1 inner ≫ snd _ _ = inner := lift_snd _ _
            _ = lift p2 p3 ≫ pairActionMap G := rfl
            _ = ((α_ (stabilizerOverPairs G) (stabilizerOverPairs G)
                  (arrowsOverPairs G)).hom ≫
                  snd (stabilizerOverPairs G)
                    (stabilizerOverPairs G ⊗ arrowsOverPairs G)) ≫
                  pairActionMap G := by rw [hαsnd]
            _ = (α_ (stabilizerOverPairs G) (stabilizerOverPairs G)
                  (arrowsOverPairs G)).hom ≫
                  (snd _ _ ≫ pairActionMap G) := by
                    simp only [Category.assoc]
            _ = (α_ (stabilizerOverPairs G) (stabilizerOverPairs G)
                  (arrowsOverPairs G)).hom ≫
                  (stabilizerOverPairs G ◁ pairActionMap G ≫ snd _ _) := by
                    rw [whiskerLeft_snd]
            _ = _ := (Category.assoc _ _ _).symm
      have hp12 : p12 = lift p1 p2 := by
        apply hom_ext <;> simp [p12, p1, p2]
      have hmulPoint := stabilizerPoint_mul G p1 p2
      have hsp : stabilizerPoint G m =
          lift (stabilizerPoint G p1) (stabilizerPoint G p2) ≫ μ[stabilizer G] := by
        dsimp [m]
        rw [hp12]
        exact hmulPoint
      have hleft := pairActionMap_spec G m p3
      have hleft' : arrowPoint G (leftPair ≫ pairActionMap G) =
          lift (stabilizerPoint G m) (arrowPoint G p3) ≫
            γ[stabilizer G, arrowsOverTarget G] := by
        simpa [leftPair] using hleft
      have hinner := pairActionMap_spec G p2 p3
      have hright := pairActionMap_spec G p1 inner
      have hright' : arrowPoint G (rightPair ≫ pairActionMap G) =
          lift (stabilizerPoint G p1) (arrowPoint G inner) ≫
            γ[stabilizer G, arrowsOverTarget G] := by
        simpa [rightPair] using hright
      have hmulAction :
          (lift (stabilizerPoint G p1) (stabilizerPoint G p2) ≫ μ[stabilizer G]) •
              arrowPoint G p3 =
            stabilizerPoint G p1 •
              (stabilizerPoint G p2 • arrowPoint G p3) :=
        mul_smul (stabilizerPoint G p1) (stabilizerPoint G p2)
          (arrowPoint G p3)
      have hinner' :
          arrowPoint G inner =
            stabilizerPoint G p2 • arrowPoint G p3 := by
        change arrowPoint G (lift p2 p3 ≫ pairActionMap G) = _
        exact hinner
      have hpoint :
          arrowPoint G (leftPair ≫ pairActionMap G) =
            arrowPoint G (rightPair ≫ pairActionMap G) := by
        calc
          arrowPoint G (leftPair ≫ pairActionMap G) =
              lift (stabilizerPoint G m) (arrowPoint G p3) ≫
                γ[stabilizer G, arrowsOverTarget G] := hleft'
          _ = (lift (stabilizerPoint G p1) (stabilizerPoint G p2) ≫
                μ[stabilizer G]) • arrowPoint G p3 := by
                  rw [Hom.smul_def, hsp]
          _ = stabilizerPoint G p1 •
                (stabilizerPoint G p2 • arrowPoint G p3) := hmulAction
          _ = stabilizerPoint G p1 • arrowPoint G inner := by rw [← hinner']
          _ = arrowPoint G (rightPair ≫ pairActionMap G) := hright'.symm
      calc
        μ[stabilizerOverPairs G] ▷ arrowsOverPairs G ≫ pairActionMap G =
            leftPair ≫ pairActionMap G := by rw [hleftPair]
        _ = rightPair ≫ pairActionMap G := arrowPoint_injective G hpoint
        _ = (α_ (stabilizerOverPairs G) (stabilizerOverPairs G)
              (arrowsOverPairs G)).hom ≫
              stabilizerOverPairs G ◁ pairActionMap G ≫ pairActionMap G := by
                rw [hrightPair]
                exact Category.assoc _ _ _
  }
  refine ⟨⟨inferInstance, ?_⟩⟩
  intro T g r
  exact pairActionMap_spec G g r

/-- The stabilizer action on arrows induces the canonical action of the base-changed stabilizer
on arrows over the pair scheme. -/
@[stacks 04Q2 "induced action"]
def stabilizerActionOverPairs {S : Scheme.{u}} (G : GroupoidScheme S) :
    { h : ModObj (stabilizerOverPairs G) (arrowsOverPairs G) // IsInducedAction G h } :=
  Classical.choice (by exact stabilizerActionOverPairs_nonempty G)

/-- The canonical action of the base-changed stabilizer on the arrows over the pair scheme. -/
instance {S : Scheme.{u}} (G : GroupoidScheme S) :
    ModObj (stabilizerOverPairs G) (arrowsOverPairs G) :=
  (stabilizerActionOverPairs G).1

/-- In a groupoid, two parallel arrows differ by a unique endomorphism of their target. -/
private lemma evaluation_existsUnique_comp {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} {a b : G.Evaluation T} (f g : a ⟶ b) :
    ∃! h : b ⟶ b, f ≫ h = g := by
  refine ⟨inv f ≫ g, by simp, ?_⟩
  intro h hh
  apply (cancel_epi f).1
  simpa using hh

/-- The generalized arrow underlying a composite in the evaluation groupoid is the groupoid
composite of the two arrows, in the opposite order. -/
private lemma evaluation_comp_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} {a b c : G.Evaluation T} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).arrow = G.compose g.arrow f.arrow
      (g.source_eq.trans f.target_eq.symm) := rfl

/-- The arrow scheme is a pseudo-torsor under the stabilizer over the pair scheme. -/
@[stacks 04Q2 "pseudo-torsor"]
theorem stabilizerActionOverPairs_pseudoTorsor {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    IsPseudoTorsor (stabilizerOverPairs G) (arrowsOverPairs G) := by
  apply (ModObj.isIso_leftSMul_iff (M := stabilizerOverPairs G)
    (X := arrowsOverPairs G)).2
  intro T x y
  let T₀ := (Over.map (firstProjection G)).obj T
  let B := (Over.map G.objects.hom).obj T₀
  let fx : B ⟶ G.arrows := arrowOverTargetHom G (arrowPoint G x)
  let fy : B ⟶ G.arrows := arrowOverTargetHom G (arrowPoint G y)
  have hxTarget : fx ≫ G.target = Over.homMk T₀.hom :=
    arrowOverTargetHom_target G (arrowPoint G x)
  have hyTarget : fy ≫ G.target = Over.homMk T₀.hom :=
    arrowOverTargetHom_target G (arrowPoint G y)
  have hxySource : fx ≫ G.source = fy ≫ G.source :=
    Over.OverMorphism.ext ((arrowPoint_source G x).trans (arrowPoint_source G y).symm)
  let a : G.Evaluation B := fx ≫ G.source
  let b : G.Evaluation B := fx ≫ G.target
  let xEval : a ⟶ b := ⟨fx, rfl, rfl⟩
  let yEval : a ⟶ b := ⟨fy, hxySource.symm, hyTarget.trans hxTarget.symm⟩
  obtain ⟨loop, hloop, huniq⟩ := evaluation_existsUnique_comp G xEval yEval
  have hsource : (loop.arrow ≫ G.source).left =
      T.hom ≫ (fst G.objects G.objects).left :=
    congrArg Over.Hom.left (loop.source_eq.trans hxTarget)
  have htarget : (loop.arrow ≫ G.target).left =
      T.hom ≫ (fst G.objects G.objects).left :=
    congrArg Over.Hom.left (loop.target_eq.trans hxTarget)
  let loopPoint := stabilizerPointOfLoop G loop.arrow hsource htarget
  have hloopPoint : stabilizerArrowHom G loopPoint = loop.arrow :=
    stabilizerArrowHom_pointOfLoop G loop.arrow hsource htarget
  let pairPoint := stabilizerOverPairsPoint G loopPoint
  have hpairPoint : stabilizerPoint G pairPoint = loopPoint :=
    stabilizerPoint_stabilizerOverPairsPoint G loopPoint
  have hcompose : G.compose (stabilizerArrowHom G loopPoint) fx
      (stabilizerArrowHom_arrowOverTarget_composable G loopPoint (arrowPoint G x)) = fy := by
    have h := congrArg GroupoidScheme.EvaluationHom.arrow hloop
    rw [evaluation_comp_arrow] at h
    simpa only [hloopPoint] using h
  have hact : pairPoint • x = y := by
    apply arrowPoint_injective G
    rw [Hom.smul_def, (stabilizerActionOverPairs G).2 T pairPoint x, hpairPoint]
    apply arrowOverTargetHom_injective G
    rw [stabilizer_smul_arrow]
    exact hcompose
  refine ⟨pairPoint, hact, ?_⟩
  intro g hg
  have hcomposeG : G.compose (stabilizerArrowHom G (stabilizerPoint G g)) fx
      (stabilizerArrowHom_arrowOverTarget_composable G (stabilizerPoint G g)
        (arrowPoint G x)) = fy := by
    have hp := (stabilizerActionOverPairs G).2 T g x
    change arrowPoint G (g • x) = _ at hp
    rw [hg] at hp
    have h := congrArg (arrowOverTargetHom G) hp.symm
    rw [stabilizer_smul_arrow] at h
    exact h
  let gEval : b ⟶ b :=
    ⟨stabilizerArrowHom G (stabilizerPoint G g),
      (stabilizerArrowHom_source G (stabilizerPoint G g)).trans hxTarget.symm,
      (stabilizerArrowHom_target G (stabilizerPoint G g)).trans hxTarget.symm⟩
  have hgEval : xEval ≫ gEval = yEval := by
    apply GroupoidScheme.EvaluationHom.ext
    rw [evaluation_comp_arrow]
    exact hcomposeG
  have heq : stabilizerArrowHom G (stabilizerPoint G g) = loop.arrow :=
    congrArg GroupoidScheme.EvaluationHom.arrow (huniq gEval hgEval)
  apply stabilizerPoint_injective G
  rw [hpairPoint]
  apply stabilizerArrowHom_injective G
  exact heq.trans hloopPoint.symm


end AlgebraicGeometry

end
