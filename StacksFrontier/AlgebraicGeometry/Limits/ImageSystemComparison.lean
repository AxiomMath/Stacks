module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeSystemMorphism

/-!
# Comparison of the image systems of two good diagrams

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms and let `X ⟶ S` be quasi-separated and of finite type. A good diagram for
`X ⟶ S` (Tag 0CNN) determines an inverse system of scheme-theoretic images whose limit is `X`
(Tag 0CNQ), and a morphism of schemes over `S` is induced by a morphism of those systems on a
late common tail, uniquely at late stages (Tag 0CNR).

This file records that the system attached to a good diagram is independent of the choice of
good diagram: any two choices become isomorphic on a common tail, and the isomorphism is
natural for morphisms over `S`. It also builds the three operations on
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt` -- restriction to a later tail, the
identity and composition -- that the comparison is assembled from.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.restrict`: restriction of a morphism of
  systems to a later common tail.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.id`: the identity morphism of systems.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.comp`: composition of morphisms of
  systems.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.exists_eventual_iso_imageSystem`: the systems
  attached to two good diagrams for the same `X ⟶ S` become isomorphic on a common tail, by an
  isomorphism inducing the identity of `X`.
* `AlgebraicGeometry.LimitNoetherianSituation.eventually_natural_imageSystem_comparison`: those
  comparisons commute, eventually, with any morphism of schemes over `S`.

## Implementation notes

An isomorphism of systems is represented by two morphisms of systems in opposite directions whose
composites are the identity at every stage of a common tail; both are required to induce the
identity of `X` and to lie over the base system, which is what pins them down. Eventual
uniqueness (Tag 0CNR) is what makes the two composites eventually the identity, and equally what
makes the comparison eventually natural.

The smallness hypothesis `CategoryTheory.FinallySmall.{u} I` is inherited from Tag 0CNR; see the
module documentation of
`StacksFrontier/AlgebraicGeometry/Limits/FiniteTypeSystemMorphism.lean`. The three operations on
`MorphismAt` need no smallness, since they construct nothing.

## References

* [Stacks Project, Tag 0CNS](https://stacks.math.columbia.edu/tag/0CNS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-! ### Operations on morphisms of image systems -/

namespace MorphismAt

/-- A morphism of image systems starting at `i₀` restricts to one starting at a later stage
`i₁`. -/
noncomputable def restrict (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    {i₀ i₁ : I} (k : i₀ ≤ i₁) {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}
    (F : MorphismAt D f GX GY i₀ hX hY) :
    MorphismAt D f GX GY i₁ (hX.trans k) (hY.trans k) := by
  let R : Over (op i₁) ⥤ Over (op i₀) := Over.map ((homOfLE k).op)
  refine ⟨?_, ?_, ?_⟩
  · refine { app := fun j => F.maps.app (R.obj j), naturality := ?_ }
    intro j j' a
    have ha : (Over.map ((homOfLE (hX.trans k)).op)).map a =
        (Over.map ((homOfLE hX).op)).map (R.map a) := by
      apply CostructuredArrow.hom_ext
      rfl
    have haX := congrArg (GoodDiagram.imageSystem GX).map ha
    have haY : (GoodDiagram.imageSystem GY).map
        ((Over.map ((homOfLE (hY.trans k)).op)).map a) =
        (GoodDiagram.imageSystem GY).map
          ((Over.map ((homOfLE hY).op)).map (R.map a)) := by
      apply congrArg (GoodDiagram.imageSystem GY).map
      apply CostructuredArrow.hom_ext
      rfl
    change (GoodDiagram.imageSystem GX).map
        ((Over.map ((homOfLE (hX.trans k)).op)).map a) ≫
      F.maps.app (R.obj j') = F.maps.app (R.obj j) ≫
        (GoodDiagram.imageSystem GY).map
          ((Over.map ((homOfLE (hY.trans k)).op)).map a)
    rw [haX, haY]
    exact F.maps.naturality (R.map a)
  · intro j
    have hobjX : (Over.map ((homOfLE (hX.trans k)).op)).obj j =
        (Over.map ((homOfLE hX).op)).obj (R.obj j) := by
      apply CostructuredArrow.obj_ext
      · rfl
      · simp [R]
    have hobjY : (Over.map ((homOfLE (hY.trans k)).op)).obj j =
        (Over.map ((homOfLE hY).op)).obj (R.obj j) := by
      apply CostructuredArrow.obj_ext
      · rfl
      · simp [R]
    have hb := F.over_base (R.obj j)
    cases hobjX
    cases hobjY
    exact hb
  · intro j
    have hobjX : (Over.map ((homOfLE (hX.trans k)).op)).obj j =
        (Over.map ((homOfLE hX).op)).obj (R.obj j) := by
      apply CostructuredArrow.obj_ext
      · rfl
      · simp [R]
    have hobjY : (Over.map ((homOfLE (hY.trans k)).op)).obj j =
        (Over.map ((homOfLE hY).op)).obj (R.obj j) := by
      apply CostructuredArrow.obj_ext
      · rfl
      · simp [R]
    have hi := F.induces (R.obj j)
    cases hobjX
    cases hobjY
    exact hi

/-- The identity morphism of the image system of a good diagram. -/
noncomputable def id (D : LimitNoetherianSituation.{v, u} I)
    {X : Scheme.{u}} {p : X ⟶ D.limitScheme}
    (G : GoodDiagram D p) (i₀ : I) (h : G.index ≤ i₀) :
    MorphismAt D (𝟙 X) G G i₀ h h where
  maps := 𝟙 _
  over_base := by intro j; rfl
  induces := by
    intro j
    dsimp only [GoodDiagram.imageCone, Functor.const_obj_obj]
    calc
      _ ≫ 𝟙 _ = _ := Category.comp_id _
      _ = 𝟙 _ ≫ _ := (Category.id_comp _).symm

/-- Composition of morphisms of image systems. -/
noncomputable def comp (D : LimitNoetherianSituation.{v, u} I)
    {X Y Z : Scheme.{u}} {pX : X ⟶ D.limitScheme}
    {pY : Y ⟶ D.limitScheme} {pZ : Z ⟶ D.limitScheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) (GX : GoodDiagram D pX)
    (GY : GoodDiagram D pY) (GZ : GoodDiagram D pZ)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (hZ : GZ.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY)
    (G : MorphismAt D g GY GZ i₀ hY hZ) :
    MorphismAt D (f ≫ g) GX GZ i₀ hX hZ where
  maps := F.maps ≫ G.maps
  over_base := by
    intro j
    change (F.maps.app j ≫ G.maps.app j) ≫
      (GoodDiagram.stageMap GZ
        ((Over.map ((homOfLE hZ).op)).obj j)).imageι ≫
      pullback.fst _ _ = _
    have hG := G.over_base j
    have hF := F.over_base j
    cat_disch
  induces := by
    intro j
    let qX := GoodDiagram.stageMap GX ((Over.map ((homOfLE hX).op)).obj j)
    let qY := GoodDiagram.stageMap GY ((Over.map ((homOfLE hY).op)).obj j)
    let qZ := GoodDiagram.stageMap GZ ((Over.map ((homOfLE hZ).op)).obj j)
    let mF : qX.image ⟶ qY.image := F.maps.app j
    let mG : qY.image ⟶ qZ.image := G.maps.app j
    have hF : qX.toImage ≫ mF = f ≫ qY.toImage := by
      simpa [qX, qY, mF, GoodDiagram.imageCone, GoodDiagram.imageSystem,
        Functor.const_obj_obj, Functor.comp_obj] using F.induces j
    have hG : qY.toImage ≫ mG = g ≫ qZ.toImage := by
      simpa [qY, qZ, mG, GoodDiagram.imageCone, GoodDiagram.imageSystem,
        Functor.const_obj_obj, Functor.comp_obj] using G.induces j
    change qX.toImage ≫ (mF ≫ mG) = (f ≫ g) ≫ qZ.toImage
    rw [← Category.assoc, hF, Category.assoc, hG, ← Category.assoc]

end MorphismAt

/-- A morphism of image systems over `f` is one over any `f'` equal to `f`, with the same maps. -/
private noncomputable def MorphismAt.ofEq (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    {f f' : X ⟶ Y} (e : f = f') {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
    {i₀ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀} (F : MorphismAt D f GX GY i₀ hX hY) :
    MorphismAt D f' GX GY i₀ hX hY :=
  ⟨F.maps, F.over_base, fun j => by subst e; exact F.induces j⟩

/-! ### Independence of the choice of good diagram -/

/-- **Stacks Project, Tag 0CNS.** The systems associated to two good diagrams for the same
scheme over the limit become isomorphic on a common tail, by an isomorphism of systems inducing
the identity of `X` and lying over the base system. -/
@[stacks 0CNS "eventual isomorphism"]
theorem exists_eventual_iso_imageSystem [FinallySmall.{u} I]
    (D : LimitNoetherianSituation.{v, u} I)
    {X : Scheme.{u}} (p : X ⟶ D.limitScheme)
    [QuasiSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (G₁ G₂ : GoodDiagram D p) :
    ∃ (i₀ : I) (h₁ : G₁.index ≤ i₀) (h₂ : G₂.index ≤ i₀)
      (F : MorphismAt D (𝟙 X) G₁ G₂ i₀ h₁ h₂)
      (G : MorphismAt D (𝟙 X) G₂ G₁ i₀ h₂ h₁),
      ∀ j : Over (op i₀),
        (F.maps.app j ≫ G.maps.app j = 𝟙 _) ∧
        (G.maps.app j ≫ F.maps.app j = 𝟙 _) := by
  classical
  obtain ⟨iF, hF₁, hF₂, hF₀⟩ :=
    exists_morphismAt D (𝟙 X) (by simp) G₁ G₂
  obtain ⟨iG, hG₂, hG₁, hG₀⟩ :=
    exists_morphismAt D (𝟙 X) (by simp) G₂ G₁
  obtain ⟨i₀, kF, kG⟩ := @IsDirected.directed I (· ≤ ·) inferInstance iF iG
  rcases hF₀ with ⟨F₀⟩
  rcases hG₀ with ⟨G₀⟩
  let h₁ := hF₁.trans kF
  let h₂ := hF₂.trans kF
  let F := MorphismAt.restrict D (𝟙 X) G₁ G₂ kF F₀
  let G := MorphismAt.restrict D (𝟙 X) G₂ G₁ kG G₀
  let FG := MorphismAt.ofEq D (Category.id_comp (𝟙 X))
    (MorphismAt.comp D (𝟙 X) (𝟙 X) G₁ G₂ G₁ i₀ h₁ h₂ h₁ F G)
  let GF := MorphismAt.ofEq D (Category.id_comp (𝟙 X))
    (MorphismAt.comp D (𝟙 X) (𝟙 X) G₂ G₁ G₂ i₀ h₂ h₁ h₂ G F)
  obtain ⟨i₃F, k₃F, hEqF⟩ :=
    eventually_eq_morphismAt D (𝟙 X) G₁ G₁ i₀ h₁ h₁ FG
      (MorphismAt.id D G₁ i₀ h₁)
  obtain ⟨i₃G, k₃G, hEqG⟩ :=
    eventually_eq_morphismAt D (𝟙 X) G₂ G₂ i₀ h₂ h₂ GF
      (MorphismAt.id D G₂ i₀ h₂)
  obtain ⟨i₄, kF₄, kG₄⟩ := @IsDirected.directed I (· ≤ ·) inferInstance i₃F i₃G
  let k₀₄F := k₃F.trans kF₄
  let F' := MorphismAt.restrict D (𝟙 X) G₁ G₂ k₀₄F F
  let G' := MorphismAt.restrict D (𝟙 X) G₂ G₁ k₀₄F G
  refine ⟨i₄, h₁.trans k₀₄F, h₂.trans k₀₄F, F', G', ?_⟩
  intro j
  let RF : Over (op i₄) ⥤ Over (op i₀) :=
    Over.map ((homOfLE k₀₄F).op)
  have hj : i₄ ≤ unop j.left := leOfHom j.hom.unop
  have hjF : i₃F ≤ unop (RF.obj j).left := by
    simpa [RF] using kF₄.trans hj
  have hjG : i₃G ≤ unop (RF.obj j).left := by
    simpa [RF] using kG₄.trans hj
  have hFcomp := hEqF (RF.obj j) hjF
  have hGcomp := hEqG (RF.obj j) hjG
  constructor <;> [convert hFcomp using 1; convert hGcomp using 1] <;>
    simp only [F', G', FG, GF, MorphismAt.ofEq, MorphismAt.restrict, MorphismAt.comp,
      MorphismAt.id,
      Functor.comp_obj, RF, homOfLE_leOfHom, GoodDiagram.imageSystem_obj,
      Over.map_obj_left, Over.map_obj_hom] <;>
    rfl

/-- **Stacks Project, Tag 0CNS, naturality.** The comparison between the systems of two choices
of good diagrams commutes, eventually, with any morphism of schemes over the limit. -/
@[stacks 0CNS "naturality"]
theorem eventually_natural_imageSystem_comparison [FinallySmall.{u} I]
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme}
    {pY : Y ⟶ D.limitScheme} (f : X ⟶ Y)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    (GX₁ GX₂ : GoodDiagram D pX) (GY₁ GY₂ : GoodDiagram D pY)
    (i₀ : I) (hX₁ : GX₁.index ≤ i₀) (hX₂ : GX₂.index ≤ i₀)
    (hY₁ : GY₁.index ≤ i₀) (hY₂ : GY₂.index ≤ i₀)
    (FX : MorphismAt D (𝟙 X) GX₁ GX₂ i₀ hX₁ hX₂)
    (FY : MorphismAt D (𝟙 Y) GY₁ GY₂ i₀ hY₁ hY₂)
    (H₁ : MorphismAt D f GX₁ GY₁ i₀ hX₁ hY₁)
    (H₂ : MorphismAt D f GX₂ GY₂ i₀ hX₂ hY₂) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)) (_ : i₃ ≤ unop j.left),
        H₁.maps.app j ≫ FY.maps.app j =
          FX.maps.app j ≫ H₂.maps.app j := by
  let L₀ := MorphismAt.comp D f (𝟙 Y) GX₁ GY₁ GY₂ i₀ hX₁ hY₁ hY₂ H₁ FY
  let R₀ := MorphismAt.comp D (𝟙 X) f GX₁ GX₂ GY₂ i₀ hX₁ hX₂ hY₂ FX H₂
  let L := MorphismAt.ofEq D (Category.comp_id f) L₀
  let R := MorphismAt.ofEq D (Category.id_comp f) R₀
  obtain ⟨i₃, hi₀, hEq⟩ :=
    eventually_eq_morphismAt D f GX₁ GY₂ i₀ hX₁ hY₂ L R
  refine ⟨i₃, hi₀, ?_⟩
  intro j hj
  have h := hEq j hj
  simpa [L, R, L₀, R₀, MorphismAt.ofEq, MorphismAt.comp, NatTrans.comp_app] using h

end LimitNoetherianSituation

end AlgebraicGeometry
