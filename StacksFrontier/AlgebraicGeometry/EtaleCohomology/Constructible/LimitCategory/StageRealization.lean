module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Fullness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.StageLeg

/-!
# Maps on the limit realized at a stage

Let `(X_i)` be an inverse system of schemes inside a big étale site with a cone of vertex `X`, and
let `F`, `G` be sheaves at a stage `X_i`. A map `a : p_i⁻¹F ⟶ p_i⁻¹G` on `X` is *realized* at a
later stage `X_j` by a map `b : f_{ji}⁻¹F ⟶ f_{ji}⁻¹G` when `b` induces `a` through the canonical
comparison `AlgebraicGeometry.smallEtaleStageComparison`; this is the relation in the fullness
assertion `AlgebraicGeometry.SmallEtaleStagesFull`.

This file proves the two facts about it that the fullness proof uses: a realization persists to
every later stage (by the associativity of the comparisons of inverse images), and a realization
is read on the stage `X_i` through the adjunctions as the factorization of the adjoint transpose
of `a` through the leg `AlgebraicGeometry.smallEtaleStageLeg`.

## Main results

* `AlgebraicGeometry.smallEtaleStageComparison_hom_naturality` and `..._inv_naturality` — the
  stage comparison is natural (through `AlgebraicGeometry.smallEtaleStageComparison_eq`).
* `AlgebraicGeometry.smallEtaleStageRealizes_of_le` — realizations persist.
* `AlgebraicGeometry.unit_comp_map_smallEtaleStageRealization` — the adjoint form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u iu

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {I : Type iu} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- The stage comparison is natural. -/
@[reassoc]
theorem smallEtaleStageComparison_hom_naturality {i j : I} (h : i ≤ j)
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    (x : F ⟶ G) :
    (smallEtaleStageProjection B A Dg c hX j).map ((smallEtaleStageTransition B A Dg h).map x) ≫
        (smallEtaleStageComparison B A Dg c hX h G).hom =
      (smallEtaleStageComparison B A Dg c hX h F).hom ≫
        (smallEtaleStageProjection B A Dg c hX i).map x := by
  simp only [smallEtaleStageComparison_eq, Iso.app_hom]
  exact (smallEtaleSheafPullbackCompIso' B A _ _ _
    (coneStageHom_comp B Dg c hX h)).hom.naturality x

/-- The inverse of the stage comparison is natural. -/
@[reassoc]
theorem smallEtaleStageComparison_inv_naturality {i j : I} (h : i ≤ j)
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    (x : F ⟶ G) :
    (smallEtaleStageProjection B A Dg c hX i).map x ≫
        (smallEtaleStageComparison B A Dg c hX h G).inv =
      (smallEtaleStageComparison B A Dg c hX h F).inv ≫
        (smallEtaleStageProjection B A Dg c hX j).map
          ((smallEtaleStageTransition B A Dg h).map x) := by
  simp only [smallEtaleStageComparison_eq, Iso.app_inv]
  exact (smallEtaleSheafPullbackCompIso' B A _ _ _
    (coneStageHom_comp B Dg c hX h)).inv.naturality x

/-- **Realizations persist to later stages.** If `b` at the stage `j` realizes `a`, then so does
its inverse image at any stage `k ≥ j`, read through the comparison
`f_{kj}⁻¹f_{ji}⁻¹ ≅ f_{ki}⁻¹`. -/
theorem smallEtaleStageRealizes_trans {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    (a : (smallEtaleStageProjection B A Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B A Dg c hX i).obj G)
    (b : (smallEtaleStageTransition B A Dg hij).obj F ⟶
      (smallEtaleStageTransition B A Dg hij).obj G)
    (hb : (smallEtaleStageComparison B A Dg c hX hij F).inv ≫
        (smallEtaleStageProjection B A Dg c hX j).map b ≫
        (smallEtaleStageComparison B A Dg c hX hij G).hom = a) :
    (smallEtaleStageComparison B A Dg c hX (hij.trans hjk) F).inv ≫
        (smallEtaleStageProjection B A Dg c hX k).map
          (((smallEtaleSheafPullbackCompIso' B A (systemStageHom B Dg hjk) (systemStageHom B Dg hij)
            (systemStageHom B Dg (hij.trans hjk)) (systemStageHom_comp B Dg hij hjk)).app F).inv ≫
            (smallEtaleStageTransition B A Dg hjk).map b ≫
            ((smallEtaleSheafPullbackCompIso' B A (systemStageHom B Dg hjk)
              (systemStageHom B Dg hij) (systemStageHom B Dg (hij.trans hjk))
              (systemStageHom_comp B Dg hij hjk)).app G).hom) ≫
        (smallEtaleStageComparison B A Dg c hX (hij.trans hjk) G).hom = a := by
  let ψ := smallEtaleSheafPullbackCompIso' B A (systemStageHom B Dg hjk) (systemStageHom B Dg hij)
    (systemStageHom B Dg (hij.trans hjk)) (systemStageHom_comp B Dg hij hjk)
  have hass : ∀ H, (smallEtaleSheafPullback B A (coneStageHom B Dg c hX k)).map (ψ.hom.app H) ≫
      (smallEtaleStageComparison B A Dg c hX (hij.trans hjk) H).hom =
      (smallEtaleStageComparison B A Dg c hX hjk
          ((smallEtaleStageTransition B A Dg hij).obj H)).hom ≫
        (smallEtaleStageComparison B A Dg c hX hij H).hom := fun H => by
    simp only [smallEtaleStageComparison_eq, Iso.app_hom]
    exact smallEtaleSheafPullbackCompIso'_assoc B A _ _ _ _ _ _ (coneStageHom_comp B Dg c hX hjk)
      (systemStageHom_comp B Dg hij hjk) (coneStageHom_comp B Dg c hX hij)
      (coneStageHom_comp B Dg c hX (hij.trans hjk)) H
  have hassF : (smallEtaleStageComparison B A Dg c hX (hij.trans hjk) F).inv ≫
      (smallEtaleSheafPullback B A (coneStageHom B Dg c hX k)).map (ψ.inv.app F) =
      (smallEtaleStageComparison B A Dg c hX hij F).inv ≫
        (smallEtaleStageComparison B A Dg c hX hjk
          ((smallEtaleStageTransition B A Dg hij).obj F)).inv := by
    have he : (smallEtaleSheafPullback B A (coneStageHom B Dg c hX k)).mapIso (ψ.app F) ≪≫
        smallEtaleStageComparison B A Dg c hX (hij.trans hjk) F =
      smallEtaleStageComparison B A Dg c hX hjk ((smallEtaleStageTransition B A Dg hij).obj F) ≪≫
        smallEtaleStageComparison B A Dg c hX hij F := Iso.ext (hass F)
    simpa using congrArg Iso.inv he
  simp only [Functor.map_comp, Category.assoc, Iso.app_inv, Iso.app_hom]
  rw [hass G, ← Category.assoc, ← Category.assoc, hassF, ← hb]
  simp only [Category.assoc]
  rw [smallEtaleStageComparison_hom_naturality_assoc B A Dg c hX hjk b, Iso.inv_hom_id_assoc]

/-- **Realizations persist to later stages**, as an existence statement. -/
theorem smallEtaleStageRealizes_of_le {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    (a : (smallEtaleStageProjection B A Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B A Dg c hX i).obj G)
    (b : (smallEtaleStageTransition B A Dg hij).obj F ⟶
      (smallEtaleStageTransition B A Dg hij).obj G)
    (hb : (smallEtaleStageComparison B A Dg c hX hij F).inv ≫
        (smallEtaleStageProjection B A Dg c hX j).map b ≫
        (smallEtaleStageComparison B A Dg c hX hij G).hom = a) :
    ∃ b' : (smallEtaleStageTransition B A Dg (hij.trans hjk)).obj F ⟶
        (smallEtaleStageTransition B A Dg (hij.trans hjk)).obj G,
      (smallEtaleStageComparison B A Dg c hX (hij.trans hjk) F).inv ≫
          (smallEtaleStageProjection B A Dg c hX k).map b' ≫
          (smallEtaleStageComparison B A Dg c hX (hij.trans hjk) G).hom = a :=
  ⟨_, smallEtaleStageRealizes_trans B A Dg c hX hij hjk a b hb⟩

/-- **The adjoint form of a realization.** For `f ≫ g = h` and a map `b : g⁻¹F ⟶ g⁻¹G`, the map
`h⁻¹F ⟶ h⁻¹G` it induces through the comparisons, transposed along `h⁻¹ ⊣ h_*` and read through
the comparison of direct images, is the transpose of `b` along `g⁻¹ ⊣ g_*` followed by `g_*` of
the leg of `G`. -/
theorem unit_comp_map_smallEtaleStageRealization {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) {F G : Sheaf (SmallEtale.topology B Z.obj Z.property) A}
    (b : (smallEtaleSheafPullback B A g).obj F ⟶ (smallEtaleSheafPullback B A g).obj G) :
    (smallEtaleSheafAdjunction B A h).unit.app F ≫
        (smallEtaleSheafPushforward B A h).map
          (((smallEtaleSheafPullbackCompIso' B A f g h e).app F).inv ≫
            (smallEtaleSheafPullback B A f).map b ≫
            ((smallEtaleSheafPullbackCompIso' B A f g h e).app G).hom) ≫
        (smallEtalePushforwardCompHom B A f g h e).app ((smallEtaleSheafPullback B A h).obj G) =
      ((smallEtaleSheafAdjunction B A g).unit.app F ≫ (smallEtaleSheafPushforward B A g).map b) ≫
        (smallEtaleSheafPushforward B A g).map (smallEtaleStageLeg B A f g h e G) := by
  rw [(smallEtalePushforwardCompHom B A f g h e).naturality, Functor.comp_map,
    ← Category.assoc, ← unit_comp_map_smallEtaleStageLeg B A f g h e F, Category.assoc,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  simp only [smallEtaleStageLeg, Category.assoc, Iso.app_hom, Iso.app_inv]
  rw [← Functor.map_comp, Iso.hom_inv_id_app_assoc, Functor.map_comp,
    ← (smallEtaleSheafAdjunction B A f).unit_naturality_assoc]

end AlgebraicGeometry
