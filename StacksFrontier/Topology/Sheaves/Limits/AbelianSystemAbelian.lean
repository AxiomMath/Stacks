module

public import StacksFrontier.Topology.Sheaves.Limits.AbelianSystemCategory

/-!
# Systems of abelian sheaves form an abelian category

The category `SpectralDiagram.AbelianSystem D` of systems of abelian sheaves over a fixed diagram
`D` of spectral spaces has all the limits and colimits its stages have, computed stagewise. It is
abelian, and the evaluation functors `SpectralDiagram.ev j` are exact.

## Main definitions

* `SpectralDiagram.AbelianSystem.evaluationJointlyReflectsLimits` and
  `SpectralDiagram.AbelianSystem.evaluationJointlyReflectsColimits`: a cone (cocone) of systems is
  limiting (colimiting) as soon as it is so at every stage.
* `SpectralDiagram.AbelianSystem.limitSystem` and `SpectralDiagram.AbelianSystem.colimitSystem`:
  the stagewise limit and colimit of a diagram of systems, as systems, with their cone
  `SpectralDiagram.AbelianSystem.limitCone` and cocone `colimitCocone`.

## Main results

* `SpectralDiagram.AbelianSystem.isLimitLimitCone` and `isColimitColimitCocone`: the stagewise
  limit cone is a limit cone and the stagewise colimit cocone is a colimit cocone.
* `SpectralDiagram.AbelianSystem.hasLimitsOfShape`, `hasColimitsOfShape`, `hasFiniteLimits` and
  `hasFiniteColimits`: the category of systems has the limits and colimits its stages have.
* `SpectralDiagram.AbelianSystem.ev_preservesFiniteLimits` and `ev_preservesFiniteColimits`:
  evaluation at a stage is exact.
* `SpectralDiagram.AbelianSystem.instAbelian`: the category of systems is abelian.
* `SpectralDiagram.AbelianSystem.mono_of_app_mono` and `epi_of_app_epi`: a morphism of systems that
  is a monomorphism (epimorphism) at every stage is a monomorphism (epimorphism).
* `SpectralDiagram.AbelianSystem.shortExact_map_ev`: a short exact sequence of systems is short
  exact at every stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
open AlgebraicGeometry

universe v u v₂ u₂

noncomputable section

namespace SpectralDiagram

variable {J : Type v} [SmallCategory J] [IsCofiltered J] {D : SpectralDiagram.{v, u} J}

/-! ### Naturality of the two pushforward comparisons -/

/-- Naturality of the comparison `SpectralDiagram.pushIdHom j` in the stage sheaf. -/
lemma pushIdHom_naturality {j : J} {G H : D.StageSheaf j} (f : G ⟶ H) :
    (D.pushFunctor (𝟙 j)).map f ≫ (D.pushIdHom j).app H = (D.pushIdHom j).app G ≫ f :=
  (D.pushIdHom j).naturality f

/-- Naturality of the comparison `SpectralDiagram.pushCompHom b a` in the stage sheaf. -/
lemma pushCompHom_naturality {k j i : J} (b : k ⟶ j) (a : j ⟶ i) {G H : D.StageSheaf k}
    (f : G ⟶ H) :
    (D.pushFunctor (b ≫ a)).map f ≫ (D.pushCompHom b a).app H =
      (D.pushCompHom b a).app G ≫ (D.pushFunctor a).map ((D.pushFunctor b).map f) :=
  (D.pushCompHom b a).naturality f

namespace AbelianSystem

variable {K : Type u₂} [Category.{v₂} K]

/-! ### Limits -/

/-- **A cone of systems is limiting as soon as it is limiting at every stage.** -/
def evaluationJointlyReflectsLimits (Φ : K ⥤ D.AbelianSystem) (c : Cone Φ)
    (hc : ∀ j : J, IsLimit ((D.ev j).mapCone c)) : IsLimit c where
  lift s :=
    { app := fun j => (hc j).lift ((D.ev j).mapCone s)
      push_app := fun {j i} a => by
        refine (isLimitOfPreserves (D.pushFunctor a) (hc j)).hom_ext fun k => ?_
        have h1 : (hc j).lift ((D.ev j).mapCone s) ≫ (c.π.app k).app j = (s.π.app k).app j :=
          (hc j).fac ((D.ev j).mapCone s) k
        have h2 : (hc i).lift ((D.ev i).mapCone s) ≫ (c.π.app k).app i = (s.π.app k).app i :=
          (hc i).fac ((D.ev i).mapCone s) k
        have h3 : s.pt.pushSheaf a ≫ (D.pushFunctor a).map ((s.π.app k).app j) =
            (s.π.app k).app i ≫ (Φ.obj k).pushSheaf a := (s.π.app k).push_app a
        have h4 : c.pt.pushSheaf a ≫ (D.pushFunctor a).map ((c.π.app k).app j) =
            (c.π.app k).app i ≫ (Φ.obj k).pushSheaf a := (c.π.app k).push_app a
        change (s.pt.pushSheaf a ≫ (D.pushFunctor a).map ((hc j).lift ((D.ev j).mapCone s))) ≫
              (D.pushFunctor a).map ((c.π.app k).app j) =
            ((hc i).lift ((D.ev i).mapCone s) ≫ c.pt.pushSheaf a) ≫
              (D.pushFunctor a).map ((c.π.app k).app j)
        simp only [Category.assoc]
        rw [← CategoryTheory.Functor.map_comp, h1, h3, h4, ← Category.assoc, h2] }
  fac s k := Hom.ext fun j => (hc j).fac ((D.ev j).mapCone s) k
  uniq s m hm := Hom.ext fun j =>
    (hc j).uniq ((D.ev j).mapCone s) (m.app j) fun k => congrArg (fun α => Hom.app α j) (hm k)

section Limits

variable (Φ : K ⥤ D.AbelianSystem) [∀ j : J, HasLimit (Φ ⋙ D.ev j)]

/-- The `f_a`-map of the stagewise limit of a diagram of systems: the morphism into the
pushforward of the limit, a limit of the pushed-forward diagram, whose legs are the limit
projections followed by the `f_a`-maps of the members. -/
def limitPush {j i : J} (a : j ⟶ i) :
    limit (Φ ⋙ D.ev i) ⟶ (D.pushFunctor a).obj (limit (Φ ⋙ D.ev j)) :=
  (isLimitOfPreserves (D.pushFunctor a) (limit.isLimit (Φ ⋙ D.ev j))).lift
    { pt := limit (Φ ⋙ D.ev i)
      π :=
        { app := fun k => limit.π (Φ ⋙ D.ev i) k ≫ (Φ.obj k).pushSheaf a
          naturality := fun {k k'} g => by
            have hw : limit.π (Φ ⋙ D.ev i) k ≫ (Φ.map g).app i = limit.π (Φ ⋙ D.ev i) k' :=
              limit.w (Φ ⋙ D.ev i) g
            dsimp
            rw [Category.id_comp, Category.assoc, (Φ.map g).push_app a, ← Category.assoc,
              hw] } }

/-- The `f_a`-map of the stagewise limit, followed by the pushforward of the `k`-th limit
projection, is the `k`-th limit projection followed by the `f_a`-map of the `k`-th member. -/
@[reassoc (attr := simp)] lemma limitPush_fac {j i : J} (a : j ⟶ i) (k : K) :
    limitPush Φ a ≫ (D.pushFunctor a).map (limit.π (Φ ⋙ D.ev j) k) =
      limit.π (Φ ⋙ D.ev i) k ≫ (Φ.obj k).pushSheaf a :=
  (isLimitOfPreserves (D.pushFunctor a) (limit.isLimit (Φ ⋙ D.ev j))).fac _ k

/-- **The stagewise limit of a diagram of systems, as a system.** -/
def limitSystem : D.AbelianSystem :=
  ofPushSheaf (fun j => limit (Φ ⋙ D.ev j)) (limitPush Φ)
    (fun j => limit.hom_ext fun k => by
      dsimp only [Functor.comp_obj, ev_obj]
      simp only [Category.assoc, Category.id_comp]
      rw [← pushIdHom_naturality, limitPush_fac_assoc, pushSheaf_id]
      exact Category.comp_id _)
    (fun {k j i} b a => by
      refine (isLimitOfPreserves (D.pushFunctor a)
        (isLimitOfPreserves (D.pushFunctor b) (limit.isLimit (Φ ⋙ D.ev k)))).hom_ext fun m => ?_
      change (limitPush Φ (b ≫ a) ≫ (D.pushCompHom b a).app (limit (Φ ⋙ D.ev k))) ≫
            (D.pushFunctor a).map ((D.pushFunctor b).map (limit.π (Φ ⋙ D.ev k) m)) =
          (limitPush Φ a ≫ (D.pushFunctor a).map (limitPush Φ b)) ≫
            (D.pushFunctor a).map ((D.pushFunctor b).map (limit.π (Φ ⋙ D.ev k) m))
      dsimp only [Functor.comp_obj, ev_obj]
      simp only [Category.assoc]
      rw [← pushCompHom_naturality, limitPush_fac_assoc, pushSheaf_comp,
        ← CategoryTheory.Functor.map_comp, limitPush_fac, CategoryTheory.Functor.map_comp,
        limitPush_fac_assoc])

/-- The stage-`j` sheaf of the stagewise limit system is the limit of the diagram at stage `j`. -/
@[simp] lemma limitSystem_sheaf (j : J) : (limitSystem Φ).sheaf j = limit (Φ ⋙ D.ev j) := rfl

/-- The `f_a`-map of the stagewise limit system is `limitPush`. -/
@[simp] lemma limitSystem_pushSheaf {j i : J} (a : j ⟶ i) :
    (limitSystem Φ).pushSheaf a = limitPush Φ a := rfl

/-- The cone of the stagewise limit of a diagram of systems. -/
def limitCone : Cone Φ where
  pt := limitSystem Φ
  π :=
    { app := fun k =>
        { app := fun j => limit.π (Φ ⋙ D.ev j) k
          push_app := fun a => limitPush_fac Φ a k }
      naturality := fun {k k'} g => Hom.ext fun j => by
        have hw : limit.π (Φ ⋙ D.ev j) k ≫ (Φ.map g).app j = limit.π (Φ ⋙ D.ev j) k' :=
          limit.w (Φ ⋙ D.ev j) g
        dsimp
        exact (Category.id_comp _).trans hw.symm }

/-- The evaluation of the stagewise limit cone at a stage is a limit cone: it is the limit cone of
the evaluated diagram, up to the identity of its vertex. -/
def isLimitEvMapLimitCone (j : J) : IsLimit ((D.ev j).mapCone (limitCone Φ)) :=
  (limit.isLimit (Φ ⋙ D.ev j)).ofIsoLimit
    (Cone.ext (Iso.refl _) fun _ => (Category.id_comp _).symm)

/-- **The stagewise limit cone of a diagram of systems is a limit cone.** -/
def isLimitLimitCone : IsLimit (limitCone Φ) :=
  evaluationJointlyReflectsLimits _ _ (isLimitEvMapLimitCone Φ)

/-- A diagram of systems has a limit as soon as it has a limit at every stage. -/
instance hasLimit : HasLimit Φ := ⟨_, isLimitLimitCone Φ⟩

/-- **Evaluation at a stage preserves limits**, by construction of the limit of systems. -/
instance ev_preservesLimit (j : J) : PreservesLimit Φ (D.ev j) :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone Φ) (isLimitEvMapLimitCone Φ j)

end Limits

/-- The category of systems has limits of shape `K` when every stage category has them. -/
instance hasLimitsOfShape [∀ j : J, HasLimitsOfShape K (D.StageSheaf j)] :
    HasLimitsOfShape K D.AbelianSystem where
  has_limit Φ := hasLimit Φ

/-- Evaluation at a stage preserves limits of shape `K` when every stage category has them. -/
instance ev_preservesLimitsOfShape [∀ j : J, HasLimitsOfShape K (D.StageSheaf j)] (j : J) :
    PreservesLimitsOfShape K (D.ev j) where
  preservesLimit := ev_preservesLimit _ j

/-- The category of systems has finite limits. -/
instance hasFiniteLimits : HasFiniteLimits D.AbelianSystem where
  out _ _ _ := hasLimitsOfShape

/-- **Evaluation at a stage is left exact.** -/
instance ev_preservesFiniteLimits (j : J) : PreservesFiniteLimits (D.ev j) where
  preservesFiniteLimits _ _ _ := ev_preservesLimitsOfShape j

/-! ### Colimits -/

/-- **A cocone of systems is colimiting as soon as it is colimiting at every stage.** -/
def evaluationJointlyReflectsColimits (Φ : K ⥤ D.AbelianSystem) (c : Cocone Φ)
    (hc : ∀ j : J, IsColimit ((D.ev j).mapCocone c)) : IsColimit c where
  desc s :=
    { app := fun j => (hc j).desc ((D.ev j).mapCocone s)
      push_app := fun {j i} a => by
        refine (hc i).hom_ext fun k => ?_
        have h1 : (c.ι.app k).app j ≫ (hc j).desc ((D.ev j).mapCocone s) = (s.ι.app k).app j :=
          (hc j).fac ((D.ev j).mapCocone s) k
        have h2 : (c.ι.app k).app i ≫ (hc i).desc ((D.ev i).mapCocone s) = (s.ι.app k).app i :=
          (hc i).fac ((D.ev i).mapCocone s) k
        have h3 : (Φ.obj k).pushSheaf a ≫ (D.pushFunctor a).map ((c.ι.app k).app j) =
            (c.ι.app k).app i ≫ c.pt.pushSheaf a := (c.ι.app k).push_app a
        have h4 : (Φ.obj k).pushSheaf a ≫ (D.pushFunctor a).map ((s.ι.app k).app j) =
            (s.ι.app k).app i ≫ s.pt.pushSheaf a := (s.ι.app k).push_app a
        change (c.ι.app k).app i ≫ c.pt.pushSheaf a ≫
              (D.pushFunctor a).map ((hc j).desc ((D.ev j).mapCocone s)) =
            (c.ι.app k).app i ≫ (hc i).desc ((D.ev i).mapCocone s) ≫ s.pt.pushSheaf a
        rw [← Category.assoc, ← h3, Category.assoc, ← CategoryTheory.Functor.map_comp, h1, h4,
          ← Category.assoc, h2] }
  fac s k := Hom.ext fun j => (hc j).fac ((D.ev j).mapCocone s) k
  uniq s m hm := Hom.ext fun j =>
    (hc j).uniq ((D.ev j).mapCocone s) (m.app j) fun k => congrArg (fun α => Hom.app α j) (hm k)

section Colimits

variable (Φ : K ⥤ D.AbelianSystem) [∀ j : J, HasColimit (Φ ⋙ D.ev j)]

/-- The `f_a`-map of the stagewise colimit of a diagram of systems: on the `k`-th member of the
colimit it is the `f_a`-map of that member followed by the pushforward of the `k`-th colimit
inclusion. -/
def colimitPush {j i : J} (a : j ⟶ i) :
    colimit (Φ ⋙ D.ev i) ⟶ (D.pushFunctor a).obj (colimit (Φ ⋙ D.ev j)) :=
  colimit.desc (Φ ⋙ D.ev i)
    { pt := (D.pushFunctor a).obj (colimit (Φ ⋙ D.ev j))
      ι :=
        { app := fun k =>
            (Φ.obj k).pushSheaf a ≫ (D.pushFunctor a).map (colimit.ι (Φ ⋙ D.ev j) k)
          naturality := fun {k k'} g => by
            have hw : (Φ.map g).app j ≫ colimit.ι (Φ ⋙ D.ev j) k' =
                colimit.ι (Φ ⋙ D.ev j) k := colimit.w (Φ ⋙ D.ev j) g
            have hp : (Φ.map g).app i ≫ (Φ.obj k').pushSheaf a =
                (Φ.obj k).pushSheaf a ≫ (D.pushFunctor a).map ((Φ.map g).app j) :=
              ((Φ.map g).push_app a).symm
            dsimp
            rw [Category.comp_id, ← Category.assoc, hp, Category.assoc,
              ← CategoryTheory.Functor.map_comp, hw] } }

/-- The `k`-th colimit inclusion followed by the `f_a`-map of the stagewise colimit is the
`f_a`-map of the `k`-th member followed by the pushforward of the `k`-th colimit inclusion. -/
@[reassoc (attr := simp)] lemma colimitPush_fac {j i : J} (a : j ⟶ i) (k : K) :
    colimit.ι (Φ ⋙ D.ev i) k ≫ colimitPush Φ a =
      (Φ.obj k).pushSheaf a ≫ (D.pushFunctor a).map (colimit.ι (Φ ⋙ D.ev j) k) :=
  colimit.ι_desc _ k

/-- **The stagewise colimit of a diagram of systems, as a system.** -/
def colimitSystem : D.AbelianSystem :=
  ofPushSheaf (fun j => colimit (Φ ⋙ D.ev j)) (colimitPush Φ)
    (fun j => colimit.hom_ext fun k => by
      dsimp only [Functor.comp_obj, ev_obj]
      simp only [Category.comp_id]
      rw [colimitPush_fac_assoc, pushIdHom_naturality, ← Category.assoc, pushSheaf_id]
      exact Category.id_comp _)
    (fun {k j i} b a => colimit.hom_ext fun m => by
      dsimp only [Functor.comp_obj, ev_obj]
      rw [colimitPush_fac_assoc, pushCompHom_naturality,
        reassoc_of% ((Φ.obj m).pushSheaf_comp b a), ← CategoryTheory.Functor.map_comp,
        colimitPush_fac_assoc, ← CategoryTheory.Functor.map_comp, colimitPush_fac])

/-- The stage-`j` sheaf of the stagewise colimit system is the colimit of the diagram at stage
`j`. -/
@[simp] lemma colimitSystem_sheaf (j : J) :
    (colimitSystem Φ).sheaf j = colimit (Φ ⋙ D.ev j) := rfl

/-- The `f_a`-map of the stagewise colimit system is `colimitPush`. -/
@[simp] lemma colimitSystem_pushSheaf {j i : J} (a : j ⟶ i) :
    (colimitSystem Φ).pushSheaf a = colimitPush Φ a := rfl

/-- The cocone of the stagewise colimit of a diagram of systems. -/
def colimitCocone : Cocone Φ where
  pt := colimitSystem Φ
  ι :=
    { app := fun k =>
        { app := fun j => colimit.ι (Φ ⋙ D.ev j) k
          push_app := fun a => (colimitPush_fac Φ a k).symm }
      naturality := fun {k k'} g => Hom.ext fun j => by
        have hw : (Φ.map g).app j ≫ colimit.ι (Φ ⋙ D.ev j) k' =
            colimit.ι (Φ ⋙ D.ev j) k := colimit.w (Φ ⋙ D.ev j) g
        dsimp
        exact hw.trans (Category.comp_id _).symm }

/-- The evaluation of the stagewise colimit cocone at a stage is a colimit cocone. -/
def isColimitEvMapColimitCocone (j : J) : IsColimit ((D.ev j).mapCocone (colimitCocone Φ)) :=
  (colimit.isColimit (Φ ⋙ D.ev j)).ofIsoColimit
    (Cocone.ext (Iso.refl _) fun _ => Category.comp_id _)

/-- **The stagewise colimit cocone of a diagram of systems is a colimit cocone.** -/
def isColimitColimitCocone : IsColimit (colimitCocone Φ) :=
  evaluationJointlyReflectsColimits _ _ (isColimitEvMapColimitCocone Φ)

/-- A diagram of systems has a colimit as soon as it has a colimit at every stage. -/
instance hasColimit : HasColimit Φ := ⟨_, isColimitColimitCocone Φ⟩

/-- **Evaluation at a stage preserves colimits**, by construction of the colimit of systems. -/
instance ev_preservesColimit (j : J) : PreservesColimit Φ (D.ev j) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone Φ)
    (isColimitEvMapColimitCocone Φ j)

end Colimits

/-- The category of systems has colimits of shape `K` when every stage category has them. -/
instance hasColimitsOfShape [∀ j : J, HasColimitsOfShape K (D.StageSheaf j)] :
    HasColimitsOfShape K D.AbelianSystem where
  has_colimit Φ := hasColimit Φ

/-- Evaluation at a stage preserves colimits of shape `K` when every stage category has them. -/
instance ev_preservesColimitsOfShape [∀ j : J, HasColimitsOfShape K (D.StageSheaf j)] (j : J) :
    PreservesColimitsOfShape K (D.ev j) where
  preservesColimit := ev_preservesColimit _ j

/-- The category of systems has finite colimits. -/
instance hasFiniteColimits : HasFiniteColimits D.AbelianSystem where
  out _ _ _ := hasColimitsOfShape

/-- **Evaluation at a stage is right exact.** -/
instance ev_preservesFiniteColimits (j : J) : PreservesFiniteColimits (D.ev j) where
  preservesFiniteColimits _ _ _ := ev_preservesColimitsOfShape j

/-! ### The abelian structure -/

/-- Every epimorphism of systems is the cokernel of its kernel. -/
instance : IsNormalEpiCategory D.AbelianSystem where
  normalEpiOfEpi p _ := ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (evaluationJointlyReflectsColimits _ _ fun _ =>
      Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _)⟩

/-- Every monomorphism of systems is the kernel of its cokernel. -/
instance : IsNormalMonoCategory D.AbelianSystem where
  normalMonoOfMono i _ := ⟨NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (evaluationJointlyReflectsLimits _ _ fun _ =>
      Abelian.isLimitMapConeOfKernelForkOfι _ _)⟩

/-- **The category of systems of abelian sheaves over a fixed diagram of spectral spaces is
abelian.** -/
instance instAbelian : Abelian D.AbelianSystem where

/-! ### Monomorphisms, epimorphisms and short exactness are stagewise -/

/-- **A morphism of systems all of whose components are monomorphisms is a monomorphism.** -/
lemma mono_of_app_mono {A B : D.AbelianSystem} (α : A ⟶ B) (h : ∀ j, Mono (α.app j)) : Mono α := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro _ β hβ
  refine Hom.ext fun j => ?_
  exact (Preadditive.mono_iff_cancel_zero (α.app j)).1 (h j) _ (β.app j)
    (congrArg (fun γ => Hom.app γ j) hβ)

/-- **A morphism of systems all of whose components are epimorphisms is an epimorphism.** -/
lemma epi_of_app_epi {A B : D.AbelianSystem} (α : A ⟶ B) (h : ∀ j, Epi (α.app j)) : Epi α := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro _ β hβ
  refine Hom.ext fun j => ?_
  exact (Preadditive.epi_iff_cancel_zero (α.app j)).1 (h j) _ (β.app j)
    (congrArg (fun γ => Hom.app γ j) hβ)

/-- **A short exact sequence of systems is short exact at every stage.** -/
lemma shortExact_map_ev {S : ShortComplex D.AbelianSystem} (hS : S.ShortExact) (j : J) :
    (S.map (D.ev j)).ShortExact :=
  hS.map_of_exact (D.ev j)

end AbelianSystem

end SpectralDiagram

end

end
