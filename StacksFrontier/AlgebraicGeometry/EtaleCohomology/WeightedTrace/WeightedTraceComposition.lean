module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceExistence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CompGerm
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceProperties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.Composition

/-!
# Composition of weighted trace maps on abelian sheaves

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be locally quasi-finite morphisms with weightings `w_f`, `w_g`.
For an abelian sheaf `F` on the small étale site of `Z`, the composite

`(f ≫ g)_!(f ≫ g)^{-1}F ⟶ g_! f_! f^{-1} g^{-1}F ⟶ g_! g^{-1}F ⟶ F`

of the comparisons of Stacks 021J and Stacks 0F6T, `g_!` of the trace of `(f, w_f)` and the trace
of `(g, w_g)`, is the trace map of `(f ≫ g, w_{f ≫ g})` with `w_{f ≫ g}(x) = w_f(x) w_g(f(x))`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section Germ

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Moving the germ of a section along an equality of geometric points with the same residue
field. -/
public theorem eqToHom_etaleGerm (k : Type u) [Field k] [IsAlgClosed k]
    {a₁ a₂ : Spec (CommRingCat.of k) ⟶ S} (h : a₁ = a₂)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) (V : SmallEtale B S hS)
    (q : (geometricPointFiber B S hS ⟨k, a₁⟩).obj V)
    (q' : (geometricPointFiber B S hS ⟨k, a₂⟩).obj V)
    (hq : q.1 = q'.1) (a : P.obj (op V)) :
    (eqToHom (congrArg (fun r => etaleStalk B S hS ⟨k, r⟩ P) h))
        (etaleGerm B S hS ⟨k, a₁⟩ P V q a) =
      etaleGerm B S hS ⟨k, a₂⟩ P V q' a := by
  subst h
  obtain rfl : q = q' := Subtype.ext hq
  simp

/-- An identification of an object with itself along an equality is the identity on elements. -/
public theorem eqToHom_self_apply {A : AddCommGrpCat.{max (u + 1) v}} (h : A = A) (a : A) :
    (eqToHom h) a = a := by
  simp

end Germ

section PullbackStalk

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  (s : GeometricPoint Z.obj)
  (F : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{max (u + 1) v})

/-- **The composition law for inverse images of Stacks 021J**, `g^{-1} ⋙ f^{-1} ≅ (f ≫ g)^{-1}`,
on abelian sheaves. -/
public abbrev compPullbackIso :
    abPullback.{u, v} B g ⋙ abPullback.{u, v} B f ≅ abPullback.{u, v} B (f ≫ g) :=
  smallEtaleSheafPullbackCompIso B X Y Z f g AddCommGrpCat.{max (u + 1) v}

/-- **The identifications of Stacks 03Q1 compose**: at a point of the geometric fibre of `f ≫ g`,
identifying the stalk of `f^{-1}g^{-1}F` with the stalk of `g^{-1}F` and then with the stalk of
`F` is identifying it, through the comparison of Stacks 021J, with the stalk of `F` directly. -/
public theorem fiberPointPullbackStalkIso_comp (x : GeometricFiberPoint B (f ≫ g) s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s)
      ((abPullback.{u, v} B f).obj ((abPullback.{u, v} B g).obj F)).obj)) :
    (fiberPointPullbackStalkIso.{u, v} B g s F (compFiberPoint B f g s x)).hom
        ((fiberPointPullbackStalkIso.{u, v} B f _ ((abPullback.{u, v} B g).obj F)
          (compFiberPointLift B f g s x)).hom z) =
      (fiberPointPullbackStalkIso.{u, v} B (f ≫ g) s F x).hom
        ((colim.map (Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber B X.obj
          X.property (x.toGeometricPoint B (f ≫ g) s))).op
          ((compPullbackIso B f g).hom.app F).hom)) z) := by
  let p := x.toGeometricPoint B (f ≫ g) s
  let t := (etaleStalkSmallEtalePullObjIso B g (p.map (B.inclusion.map f))
    AddCommGrpCat.{max (u + 1) v} F).hom
      ((etaleStalkSmallEtalePullObjIso B f p AddCommGrpCat.{max (u + 1) v}
        ((abPullback.{u, v} B g).obj F)).hom z)
  have hz : z = (etaleStalkSmallEtalePullObjIso B f p AddCommGrpCat.{max (u + 1) v}
        ((abPullback.{u, v} B g).obj F)).inv
      ((etaleStalkSmallEtalePullObjIso B g (p.map (B.inclusion.map f))
        AddCommGrpCat.{max (u + 1) v} F).inv t) := by
    simp only [t, Iso.hom_inv_id_apply]
  obtain ⟨V, w, τ, ht⟩ := exists_etaleGerm_eq B Z.obj Z.property
    ((p.map (B.inclusion.map f)).map (B.inclusion.map g)) F.obj t
  rw [hz, ← ht]
  let w' : (geometricPointFiber B Z.obj Z.property (p.map (B.inclusion.map (f ≫ g)))).obj V :=
    ⟨w.1, w.2.trans (Category.assoc _ _ _)⟩
  have hc := etaleGerm_smallEtaleSheafPullbackFactoredCompIso B f g (f ≫ g) rfl p F V w w' rfl τ
  rw [smallEtaleSheafPullbackFactoredCompIso_rfl] at hc
  have hA : (fiberPointPullbackStalkIso.{u, v} B f _ ((abPullback.{u, v} B g).obj F)
        (compFiberPointLift B f g s x)).hom
      ((etaleStalkSmallEtalePullObjIso B f p AddCommGrpCat.{max (u + 1) v}
        ((abPullback.{u, v} B g).obj F)).inv
        ((etaleStalkSmallEtalePullObjIso B g (p.map (B.inclusion.map f))
          AddCommGrpCat.{max (u + 1) v} F).inv
          (etaleGerm B Z.obj Z.property _ F.obj V w τ))) =
      (etaleStalkSmallEtalePullObjIso B g (p.map (B.inclusion.map f))
          AddCommGrpCat.{max (u + 1) v} F).inv
        (etaleGerm B Z.obj Z.property _ F.obj V w τ) :=
    (ConcreteCategory.comp_apply _ _ _).trans
      ((congrArg (fun m => (eqToHom (congrArg (fun r => etaleStalk B Y.obj Y.property r
          ((abPullback.{u, v} B g).obj F).obj) (toGeometricPoint_map B f _
            (compFiberPointLift B f g s x)))) m)
        (Iso.inv_hom_id_apply (etaleStalkSmallEtalePullObjIso B f p
          AddCommGrpCat.{max (u + 1) v} ((abPullback.{u, v} B g).obj F)) _)).trans
        (eqToHom_self_apply.{u, v} _ _))
  refine (congrArg (fiberPointPullbackStalkIso.{u, v} B g s F (compFiberPoint B f g s x)).hom
    hA).trans ?_
  refine Eq.trans (b := etaleGerm B Z.obj Z.property s F.obj V
      ⟨w.1, by exact w.2.trans (compFiberPoint B f g s x).2⟩ τ)
          ((ConcreteCategory.comp_apply _ _ _).trans
    ((congrArg (fun m => (eqToHom (congrArg (fun r => etaleStalk B Z.obj Z.property r F.obj)
        (toGeometricPoint_map B g s (compFiberPoint B f g s x)))) m)
      (Iso.inv_hom_id_apply (etaleStalkSmallEtalePullObjIso B g (p.map (B.inclusion.map f))
          AddCommGrpCat.{max (u + 1) v} F) _)).trans
      (eqToHom_etaleGerm B Z.obj Z.property s.residueField (compFiberPoint B f g s x).2 F.obj V w
        ⟨w.1, by exact w.2.trans (compFiberPoint B f g s x).2⟩ rfl τ))) ?_
  refine Eq.symm ((ConcreteCategory.comp_apply _ _ _).trans
    ((congrArg (fun m => (eqToHom (congrArg (fun r => etaleStalk B Z.obj Z.property r F.obj)
        (toGeometricPoint_map B (f ≫ g) s x))) ((etaleStalkSmallEtalePullObjIso B (f ≫ g) p
          AddCommGrpCat.{max (u + 1) v} F).hom m)) hc).trans ?_))
  refine (congrArg (fun m => (eqToHom (congrArg (fun r => etaleStalk B Z.obj Z.property r F.obj)
        (toGeometricPoint_map B (f ≫ g) s x))) m)
      (Iso.inv_hom_id_apply (etaleStalkSmallEtalePullObjIso B (f ≫ g) p
          AddCommGrpCat.{max (u + 1) v} F) _)).trans ?_
  exact eqToHom_etaleGerm B Z.obj Z.property s.residueField x.2 F.obj V w'
      ⟨w.1, by exact w.2.trans (compFiberPoint B f g s x).2⟩ rfl τ

end PullbackStalk

section Summand

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (s : GeometricPoint Y.obj)

/-- A square of abelian group homomorphisms between isomorphic objects commutes after conjugating
by the inverse isomorphisms. -/
private theorem map_inv_apply_eq_inv_map_apply.{w} {A B C D : AddCommGrpCat.{w}}
    (e : A ≅ C) (e' : B ≅ D) (a : A ⟶ B) (k : C ⟶ D) (h : a ≫ e'.hom = e.hom ≫ k) (y : C) :
    a (e.inv y) = e'.inv (k y) := by
  have := ConcreteCategory.congr_hom h (e.inv y)
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at this
  rw [← this]
  simp

/-- The map induced by `f_!φ` on the stalk carries a summand of the stalk decomposition of
Stacks 0F5F to the same summand, through the map induced by `φ`. -/
public theorem fShriekFunctor_map_fiberStalkOf
    {G G' : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : G ⟶ G') (x : GeometricFiberPoint B f s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) G.obj)) :
    (colim.map (Functor.whiskerLeft (CategoryOfElements.π
        (geometricPointFiber B Y.obj Y.property s)).op ((fShriekFunctor.{u, v} B f).map φ).1))
      ((fShriekStalkIso.{u, v} B f s G).inv (fiberStalkOf.{u, v} B f s G x z)) =
      (fShriekStalkIso.{u, v} B f s G').inv (fiberStalkOf.{u, v} B f s G' x
        ((colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s))).op φ.1)) z)) := by
  exact (map_inv_apply_eq_inv_map_apply _ _ _ _ (fShriekStalkIso_natural.{u, v} B f s φ) _).trans
    (congrArg _ (fiberStalksMap_fiberStalkOf.{u, v} B f s φ x z))

end Summand

section CompSummand

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (s : GeometricPoint Z.obj)

omit [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)] in
/-- The regrouping of the geometric fibre on a summand. -/
public theorem compFiberStalksMap_of
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (x : GeometricFiberPoint B (f ≫ g) s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s) G.obj)) :
    compFiberStalksMap B f g s G (fiberStalkOf.{u, v} B (f ≫ g) s G x z) =
      fiberStalkOf.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj G) (compFiberPoint B f g s x)
        ((fShriekStalkIso.{u, v} B f _ G).inv
          (fiberStalkOf.{u, v} B f _ G (compFiberPointLift B f g s x) z)) := by
  let := Classical.decEq (GeometricFiberPoint B (f ≫ g) s)
  let := Classical.decEq (GeometricFiberPoint B g s)
  exact DirectSum.toAddMonoid_of (β := fun x : GeometricFiberPoint B (f ≫ g) s =>
    ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s) G.obj))
    (γ := fiberStalks.{u, max (u + 1) v} B g s ((fShriekFunctor.{u, v} B f).obj G)) _ x z

/-- **Stacks 0F6T, part (3), on a summand**: the composition isomorphism carries the summand of
a point `x̄` of the geometric fibre of `g ∘ f` to the summand of `f(x̄)`, and there to the summand
of `x̄` in the stalk of `f_!`. -/
public theorem fShriekCompIso_fiberStalkOf
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (x : GeometricFiberPoint B (f ≫ g) s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s) G.obj)) :
    ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map ((fShriekCompIso B f g).hom.app G)
      ((fShriekStalkIso.{u, v} B (f ≫ g) s G).inv (fiberStalkOf.{u, v} B (f ≫ g) s G x z)) =
      (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj G)).inv
        (fiberStalkOf.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj G) (compFiberPoint B f g s x)
          ((fShriekStalkIso.{u, v} B f _ G).inv
            (fiberStalkOf.{u, v} B f _ G (compFiberPointLift B f g s x) z))) := by
  exact (map_inv_apply_eq_inv_map_apply _ _ _ _ (fShriekCompIso_stalk B f g s G) _).trans
    (congrArg _ (compFiberStalksMap_of B f g s G x z))

end CompSummand

section Abelian

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  {w_f : X.obj → ℤ} {w_g : Y.obj → ℤ} (hw_f : IsWeighting (B.inclusion.map f) w_f)
  (hw_g : IsWeighting (B.inclusion.map g) w_g)
  (F : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{max (u + 1) v})

/-- The composite `(g ∘ f)_!(g ∘ f)^{-1}F = g_! f_! f^{-1} g^{-1}F ⟶ g_! g^{-1}F ⟶ F` of the
comparisons of Stacks 021J and Stacks 0F6T, `g_!` of the trace of `(f, w_f)` and the trace of
`(g, w_g)`. -/
public def compWeightedTrace :
    (fShriekFunctor.{u, v} B (f ≫ g)).obj ((abPullback.{u, v} B (f ≫ g)).obj F) ⟶ F :=
  (fShriekFunctor.{u, v} B (f ≫ g)).map ((compPullbackIso B f g).inv.app F) ≫
    (fShriekCompIso B f g).hom.app ((abPullback.{u, v} B f).obj ((abPullback.{u, v} B g).obj F)) ≫
    (fShriekFunctor.{u, v} B g).map
        (weightedTrace.{u, v} B f hw_f ((abPullback.{u, v} B g).obj F)) ≫
    weightedTrace.{u, v} B g hw_g F

/-- The composite of the two traces on a summand: the comparisons and `g_!` of the trace of
`(f, w_f)` move the summand of a point of the geometric fibre of `g ∘ f` to the summand of its
image in the geometric fibre of `g`. -/
public theorem compWeightedTrace_fiberStalkOf (s : GeometricPoint Z.obj)
    (x : GeometricFiberPoint B (f ≫ g) s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s)
      ((abPullback.{u, v} B (f ≫ g)).obj F).obj)) :
    ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map (compWeightedTrace B f g hw_f hw_g F)
      ((fShriekStalkIso.{u, v} B (f ≫ g) s ((abPullback.{u, v} B (f ≫ g)).obj F)).inv
        (fiberStalkOf.{u, v} B (f ≫ g) s ((abPullback.{u, v} B (f ≫ g)).obj F) x z)) =
      ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map (weightedTrace.{u, v} B g hw_g F)
      ((fShriekStalkIso.{u, v} B g s ((abPullback.{u, v} B g).obj F)).inv
        (fiberStalkOf.{u, v} B g s ((abPullback.{u, v} B g).obj F) (compFiberPoint B f g s x)
          ((colim.map (Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber B Y.obj
              Y.property ((compFiberPoint B f g s x).toGeometricPoint B g s))).op
              (weightedTrace.{u, v} B f hw_f ((abPullback.{u, v} B g).obj F)).1))
            ((fShriekStalkIso.{u, v} B f _ ((abPullback.{u, v} B f).obj
                ((abPullback.{u, v} B g).obj F))).inv
              (fiberStalkOf.{u, v} B f _ ((abPullback.{u, v} B f).obj
                ((abPullback.{u, v} B g).obj F)) (compFiberPointLift B f g s x)
                ((colim.map (Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber B
                  X.obj X.property (x.toGeometricPoint B (f ≫ g) s))).op
                  ((compPullbackIso B f g).inv.app F).1)) z)))))) := by
  have hτ : ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map (compWeightedTrace B f g hw_f hw_g F) =
      ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
          ((fShriekFunctor.{u, v} B (f ≫ g)).map ((compPullbackIso B f g).inv.app F)) ≫
      ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map ((fShriekCompIso B f g).hom.app
          ((abPullback.{u, v} B f).obj ((abPullback.{u, v} B g).obj F))) ≫
      ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map ((fShriekFunctor.{u, v} B g).map
          (weightedTrace.{u, v} B f hw_f ((abPullback.{u, v} B g).obj F))) ≫
      ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map (weightedTrace.{u, v} B g hw_g F) := by
    simp only [compWeightedTrace, CategoryTheory.Functor.map_comp]
  refine (ConcreteCategory.congr_hom hτ _).trans ?_
  have e1 := fShriekFunctor_map_fiberStalkOf.{u, v} B (f ≫ g) s
    ((compPullbackIso B f g).inv.app F) x z
  refine (congrArg (fun m => ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map (weightedTrace.{u, v} B g hw_g F)
    (((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map ((fShriekFunctor.{u, v} B g).map
        (weightedTrace.{u, v} B f hw_f ((abPullback.{u, v} B g).obj F)))
    (((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map ((fShriekCompIso B f g).hom.app
        ((abPullback.{u, v} B f).obj ((abPullback.{u, v} B g).obj F))) m))) e1).trans ?_
  refine (congrArg (fun m => ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map (weightedTrace.{u, v} B g hw_g F)
    (((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map ((fShriekFunctor.{u, v} B g).map
        (weightedTrace.{u, v} B f hw_f ((abPullback.{u, v} B g).obj F))) m))
    (fShriekCompIso_fiberStalkOf B f g s _ x _)).trans ?_
  exact congrArg (fun m => ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map (weightedTrace.{u, v} B g hw_g F) m)
    (fShriekFunctor_map_fiberStalkOf.{u, v} B g s
      (weightedTrace.{u, v} B f hw_f ((abPullback.{u, v} B g).obj F))
      (compFiberPoint B f g s x) _)

/-- The trace of `(g, w_g)` after the trace of `(f, w_f)` on a summand. -/
public theorem weightedTrace_weightedTrace_fiberStalkOf (s : GeometricPoint Z.obj)
    (x : GeometricFiberPoint B (f ≫ g) s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s)
      ((abPullback.{u, v} B (f ≫ g)).obj F).obj)) :
    ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map (weightedTrace.{u, v} B g hw_g F)
      ((fShriekStalkIso.{u, v} B g s ((abPullback.{u, v} B g).obj F)).inv
        (fiberStalkOf.{u, v} B g s ((abPullback.{u, v} B g).obj F) (compFiberPoint B f g s x)
          ((colim.map (Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber B Y.obj
              Y.property ((compFiberPoint B f g s x).toGeometricPoint B g s))).op
              (weightedTrace.{u, v} B f hw_f ((abPullback.{u, v} B g).obj F)).1))
            ((fShriekStalkIso.{u, v} B f _ ((abPullback.{u, v} B f).obj
                ((abPullback.{u, v} B g).obj F))).inv
              (fiberStalkOf.{u, v} B f _ ((abPullback.{u, v} B f).obj
                ((abPullback.{u, v} B g).obj F)) (compFiberPointLift B f g s x)
                ((colim.map (Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber B
                  X.obj X.property (x.toGeometricPoint B (f ≫ g) s))).op
                  ((compPullbackIso B f g).inv.app F).1)) z)))))) =
      (w_f (x.1 default) * w_g (B.inclusion.map f (x.1 default))) •
        (fiberPointPullbackStalkIso.{u, v} B (f ≫ g) s F x).hom z := by
  refine (congrArg (fun m => ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map (weightedTrace.{u, v} B g hw_g F)
      ((fShriekStalkIso.{u, v} B g s ((abPullback.{u, v} B g).obj F)).inv
        (fiberStalkOf.{u, v} B g s ((abPullback.{u, v} B g).obj F) (compFiberPoint B f g s x) m)))
    (hasWeightedTraceStalks_fiberStalkOf.{u, v} B f w_f ((abPullback.{u, v} B g).obj F)
      (weightedTrace_hasWeightedTraceStalks.{u, v} B f hw_f _) _
      (compFiberPointLift B f g s x) _)).trans ?_
  refine (hasWeightedTraceStalks_fiberStalkOf.{u, v} B g w_g F
    (weightedTrace_hasWeightedTraceStalks.{u, v} B g hw_g F) s (compFiberPoint B f g s x)
    _).trans ?_
  rw [map_zsmul, smul_smul]
  have hz := Iso.inv_hom_id_apply (((geometricPointSitePoint B X.obj X.property
    (x.toGeometricPoint B (f ≫ g) s)).sheafFiber (A := AddCommGrpCat.{max (u + 1) v})).mapIso
      ((compPullbackIso B f g).app F)) z
  have hw : w_g ((compFiberPoint B f g s x).1 default) *
      w_f ((compFiberPointLift B f g s x).1 default) =
      w_f (x.1 default) * w_g (B.inclusion.map f (x.1 default)) := by
    rw [mul_comm]
    rfl
  have hs := (fiberPointPullbackStalkIso_comp B f g s F x _).trans
    (congrArg (fiberPointPullbackStalkIso.{u, v} B (f ≫ g) s F x).hom hz)
  rw [hw]
  exact congrArg (_ • ·) hs

/-- The composite of the two traces has the stalks of the trace of `(g ∘ f, w_{g ∘ f})`. -/
public theorem hasWeightedTraceStalks_compWeightedTrace :
    HasWeightedTraceStalks.{u, v} B (f ≫ g) (fun x => w_f x * w_g (B.inclusion.map f x)) F
      (compWeightedTrace B f g hw_f hw_g F) := by
  intro s
  refine fiberStalks_hom_ext.{u, v} B (f ≫ g) s fun x z => ?_
  exact ((compWeightedTrace_fiberStalkOf B f g hw_f hw_g F s x z).trans
    (weightedTrace_weightedTrace_fiberStalkOf B f g hw_f hw_g F s x z)).trans
    (weightedTraceStalkMap_fiberStalkOf.{u, v} B (f ≫ g)
      (fun x => w_f x * w_g (B.inclusion.map f x)) F s x z).symm

include hw_f hw_g in
/-- **Weights compose** (Stacks 0GK9): `w_{g ∘ f}(x) = w_f(x) w_g(f(x))` is a weighting of
`g ∘ f`. -/
public theorem isWeighting_comp :
    IsWeighting (B.inclusion.map (f ≫ g)) (fun x => w_f x * w_g (B.inclusion.map f x)) := by
  rw [CategoryTheory.Functor.map_comp]
  exact IsWeighting.mul_comp hw_f hw_g

/-- **The weighted traces compose, on abelian sheaves.** For an abelian sheaf `F` on the small
étale site of `Z` the composite
`(g ∘ f)_!(g ∘ f)^{-1}F = g_! f_! f^{-1} g^{-1}F ⟶ g_! g^{-1}F ⟶ F` of `g_!` of the trace of
`(f, w_f)` and the trace of `(g, w_g)` is the trace of `(g ∘ f, w_{g ∘ f})`. -/
public theorem weightedTrace_comp :
    weightedTrace.{u, v} B (f ≫ g) (isWeighting_comp B f g hw_f hw_g) F =
      compWeightedTrace B f g hw_f hw_g F :=
  (eq_weightedTrace.{u, v} B (f ≫ g) (isWeighting_comp B f g hw_f hw_g) F
    (hasWeightedTraceStalks_compWeightedTrace B f g hw_f hw_g F)).symm

end Abelian

end AlgebraicGeometry.SmallEtale

end
