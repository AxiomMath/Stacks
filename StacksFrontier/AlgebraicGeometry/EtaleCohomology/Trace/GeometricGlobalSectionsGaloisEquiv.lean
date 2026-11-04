module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeGlobalSectionsGaloisAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricCoverSectionsMonodromy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTautologicalSection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapTwistUnitSections

/-!
# `Γ(X_k̄, ℱ_ρ) = M` for `ρ` trivial on the geometric fundamental group, Galois-equivariantly

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraically closed
algebraic extension of `k`, `η̄` a geometric point of `X_k̄` with image `x̄` in `X`, `Λ` a finite
ring, and `ρ` a finite `Λ`-module `M` with a continuous action of `π₁(X, x̄)` which is trivial on
the image of `π₁(X_k̄, η̄)`. This file constructs a canonical isomorphism of `Λ`-modules
`Γ(X_k̄, ℱ_ρ|_{X_k̄}) ≅ M` and shows that it carries the action of `σ ∈ Aut(k̄/k)` on the left to
the action of any `γ ∈ π₁(X, x̄)` mapping to `σ` on the right.

## Main definitions

* `AlgebraicGeometry.geometricGlobalSectionsEval` — evaluation of a global section at `η̄`, read in
  `M`, for any `ρ`.
* `AlgebraicGeometry.geometricGlobalSectionsTrivialEquiv` — the isomorphism, for `ρ` trivial on
  `π₁(X_k̄)`.

## Main results

* `AlgebraicGeometry.geometricGlobalSectionsTrivialEquiv_galois` — Galois equivariance.
* `AlgebraicGeometry.geometricGlobalSectionsTrivialEquiv_naturality` — naturality in `ρ`.
* `CategoryTheory.Functor.map_add_of_naturality` — a natural map between additive functors to
  modules is additive.

## Implementation notes

**Canonicity.** The isomorphism is evaluation at `η̄`. A global section of `pr⁻¹ℱ_ρ` is the pulled
back tautological section of `ℱ_ρ` (`AlgebraicGeometry.representationTautologicalSection`)
restricted along a unique `X`-morphism `τ : X_k̄ ⟶ V` to the representing cover `V`
(`Stacks.EtaleCohomology.bijective_map_moduleUnitSection`); its value is the fibre point `τ ∘ η̄`,
an element of `M` by `AlgebraicGeometry.representationFibreEquiv`. No isomorphism is chosen. In
particular the existence-only comparison of Tag 0DV6
(`AlgebraicGeometry.representationSheafPullbackIso`) is not used to define the map: it is built on
`Classical.choice` of an isomorphism, and a different choice changes it by an automorphism of the
restriction functor, which can break Galois equivariance. It is used once, inside the proof of
additivity, to know that global sections of `pr⁻¹ℱ_ρ` form an additive functor of `ρ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleCohomology Stacks.GroupCohomology Stacks.Frobenius

universe u

namespace CategoryTheory.Functor

universe w

/-- **A natural map between additive functors to modules is additive.** If `F G : C ⥤ Mod_R` are
additive functors on a preadditive category with binary biproducts and `θ` is a family of maps of
the underlying sets, natural for every morphism of `C`, then each `θ_X` is additive: `a + b` is the
image of `(a, b) ∈ F(X ⊞ X)` under the codiagonal, and `θ` is natural for the projections and the
codiagonal. -/
theorem map_add_of_naturality {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
    {R : Type*} [Ring R] (F G : C ⥤ ModuleCat.{w} R) [F.Additive] [G.Additive]
    (θ : ∀ X, F.obj X → G.obj X)
    (hθ : ∀ {X Y : C} (f : X ⟶ Y) (a : F.obj X), θ Y (F.map f a) = G.map f (θ X a))
    (X : C) (a b : F.obj X) : θ X (a + b) = θ X a + θ X b := by
  have hF : ∀ {A A' A'' : C} (f : A ⟶ A') (g : A' ⟶ A'') (x : F.obj A),
      F.map g (F.map f x) = F.map (f ≫ g) x := fun f g x => by
    rw [F.map_comp]
    rfl
  have hG : ∀ {A A' A'' : C} (f : A ⟶ A') (g : A' ⟶ A'') (x : G.obj A),
      G.map g (G.map f x) = G.map (f ≫ g) x := fun f g x => by
    rw [G.map_comp]
    rfl
  have hF0 : ∀ {A A' : C} (x : F.obj A), F.map (0 : A ⟶ A') x = 0 := fun x => by
    rw [F.map_zero]
    rfl
  have hF1 : ∀ {A : C} (x : F.obj A), F.map (𝟙 A) x = x := fun x => by
    rw [F.map_id]
    rfl
  have hG1 : ∀ {A : C} (x : G.obj A), G.map (𝟙 A) x = x := fun x => by
    rw [G.map_id]
    rfl
  let w := F.map (biprod.inl : X ⟶ X ⊞ X) a + F.map biprod.inr b
  have hfst : F.map biprod.fst w = a := by
    show F.map biprod.fst (F.map biprod.inl a + F.map biprod.inr b) = a
    rw [_root_.map_add, hF, hF, biprod.inl_fst, biprod.inr_fst, hF1, hF0, add_zero]
  have hsnd : F.map biprod.snd w = b := by
    show F.map biprod.snd (F.map biprod.inl a + F.map biprod.inr b) = b
    rw [_root_.map_add, hF, hF, biprod.inl_snd, biprod.inr_snd, hF1, hF0, zero_add]
  have hsum : F.map (biprod.desc (𝟙 X) (𝟙 X)) w = a + b := by
    show F.map (biprod.desc (𝟙 X) (𝟙 X)) (F.map biprod.inl a + F.map biprod.inr b) = a + b
    rw [_root_.map_add, hF, hF, biprod.inl_desc, biprod.inr_desc, hF1, hF1]
  have hdec : ∀ c : G.obj (X ⊞ X),
      c = G.map biprod.inl (G.map biprod.fst c) + G.map biprod.inr (G.map biprod.snd c) := by
    intro c
    rw [hG, hG]
    have h := congrArg (fun φ => ConcreteCategory.hom (G.map φ) c) (biprod.total (X := X) (Y := X))
    simp only [G.map_add] at h
    exact (hG1 c).symm.trans h.symm
  rw [← hsum, hθ, hdec (θ (X ⊞ X) w), ← hθ biprod.fst w, ← hθ biprod.snd w, hfst, hsnd,
    _root_.map_add, hG, hG,
    biprod.inl_desc, biprod.inr_desc, hG1, hG1]

end CategoryTheory.Functor

namespace AlgebraicGeometry

section Main

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

/-- The restriction `pr⁻¹ℱ_ρ` of `ℱ_ρ` to `X_k̄`. -/
abbrev geometricRepresentationRestriction
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar) :=
  letI := connectedSpace_of_isCurve B X f
  (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).obj
    ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)

/-- **Global sections of `pr⁻¹ℱ_ρ` are sections of the pulled back representing cover.** A global
section of the restriction of `ℱ_ρ` to `X_k̄` is, through its restriction to the final object, the
restriction of the pulled back tautological section `u(ε)` along a unique morphism from the final
object to the pullback `X_k̄ ×_X V` of the representing cover `V` of `ℱ_ρ`. -/
def geometricGlobalSectionsCoverEquiv
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ)) ≃
      (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)) ⟶
        (Stacks.EtaleCohomology.smallEtaleBaseChange (fieldBaseChangeProj (Over.mk f) kbar)).obj
          (representationCover B X _ Λ ρ)) :=
  letI := connectedSpace_of_isCurve B X f
  ((Sheaf.ΓNatIsoSheafSections (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) (isTerminalEtaleMkId _)).app
        (geometricRepresentationRestriction B X f kbar Λ y ρ)).toLinearEquiv.toEquiv.trans
    (Equiv.ofBijective _ (bijective_map_moduleUnitSection Λ (fieldBaseChangeProj (Over.mk f) kbar)
      _ _ (isIso_sectionEquiv_symm_representationTautologicalSection B X _ Λ ρ) _)).symm

omit [IsAlgClosed kbar] in
/-- The defining property of `AlgebraicGeometry.geometricGlobalSectionsCoverEquiv`: a global
section restricts, over the final object, to the pulled back tautological section restricted along
the corresponding morphism; and that morphism is the only one with this property. -/
theorem geometricGlobalSectionsCoverEquiv_eq_iff
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ)))
    (t : Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)) ⟶
        (Stacks.EtaleCohomology.smallEtaleBaseChange (fieldBaseChangeProj (Over.mk f) kbar)).obj
          (letI := connectedSpace_of_isCurve B X f; representationCover B X _ Λ ρ)) :
    letI := connectedSpace_of_isCurve B X f
    geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ z = t ↔
      (geometricRepresentationRestriction B X f kbar Λ y ρ).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)))) z =
        (geometricRepresentationRestriction B X f kbar Λ y ρ).obj.map t.op
          (moduleUnitSection Λ (fieldBaseChangeProj (Over.mk f) kbar) _
            (representationTautologicalSection B X _ Λ ρ)) := by
  let := connectedSpace_of_isCurve B X f
  rw [geometricGlobalSectionsCoverEquiv, Equiv.trans_apply, Equiv.symm_apply_eq,
    Equiv.ofBijective_apply]
  have h := Sheaf.ΓNatIsoSheafSections_hom_app_general (J := (fieldBaseChange (Over.mk f)
    kbar).smallEtaleTopology) (A := ModuleCat.{u + 1} Λ) (isTerminalEtaleMkId _)
    (geometricRepresentationRestriction B X f kbar Λ y ρ)
  have h2 : ((Sheaf.ΓNatIsoSheafSections (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) (isTerminalEtaleMkId _)).app
        (geometricRepresentationRestriction B X f kbar Λ y ρ)).toLinearEquiv.toEquiv z =
      (geometricRepresentationRestriction B X f kbar Λ y ρ).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)))) z :=
    ConcreteCategory.congr_hom h z
  rw [h2]

/-- The point of the geometric fibre at `x̄` of the representing cover `V` of `ℱ_ρ` given by a
section `X_k̄ ⟶ X_k̄ ×_X V`, that is by an `X`-morphism `X_k̄ ⟶ V`, evaluated at `η̄`. -/
def geometricGlobalSectionsFibrePoint
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (t : Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)) ⟶
        (Stacks.EtaleCohomology.smallEtaleBaseChange (fieldBaseChangeProj (Over.mk f) kbar)).obj
          (letI := connectedSpace_of_isCurve B X f; representationCover B X _ Λ ρ)) :
    letI := connectedSpace_of_isCurve B X f
    finiteEtaleFiber (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
      (representationFiniteEtaleCover B X _ Λ ρ) :=
  letI := connectedSpace_of_isCurve B X f
  fieldBaseChangeCoverPoint B X f kbar y (representationFiniteEtaleCover B X _ Λ ρ) (𝟙 _)
    (Category.id_comp _) (t.left ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans ((congrArg (t.left ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (smallEtaleBaseChange_w _ t)).trans (Category.id_comp _)))))

/-- **The evaluation of a global section of `pr⁻¹ℱ_ρ` at `η̄`, read in `M`.** A global section of
the restriction of `ℱ_ρ` to `X_k̄` is an `X`-morphism `X_k̄ ⟶ V` to the representing cover of
`ℱ_ρ` (`AlgebraicGeometry.geometricGlobalSectionsCoverEquiv`); evaluating it at `η̄` gives a point
of the geometric fibre of `V` at `x̄`, which is an element of `M`
(`AlgebraicGeometry.representationFibreEquiv`). -/
def geometricGlobalSectionsEval
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ))) :
    ρ.obj.obj.obj.V :=
  letI := connectedSpace_of_isCurve B X f
  representationFibreEquiv B X _ Λ ρ (geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ
    (geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ z))

omit [Fintype Λ] in
/-- Restricting the pulled back tautological section along a morphism of covers: if `ε` restricts
along `w : V ⟶ V'` to `ε'`-data, the pulled back sections do too. -/
lemma moduleUnitSection_map {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (F : EtaleModules.{u, 0} Λ Y)
    {V W : Y.Etale} (w : V ⟶ W) (ε : F.obj.obj (op W)) :
    moduleUnitSection Λ g F (F.obj.map w.op ε) =
      ((etaleModuleInverseImage.{u, 0} Λ g).obj F).obj.map
        ((Stacks.EtaleCohomology.smallEtaleBaseChange g).map w).op (moduleUnitSection Λ g F ε) :=
  ConcreteCategory.congr_hom (((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app F).hom.naturality
    w.op) ε

/-- If a global section of `pr⁻¹ℱ_ρ'` corresponds to the morphism `t ≫ Vw` to the cover of `ℱ_ρ'`,
where `t` corresponds to a section of `pr⁻¹ℱ_ρ`, its evaluation is that of `t` pushed along `m`. -/
private theorem geometricGlobalSectionsEval_eq_of_coverEquiv_eq
    {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsCurve k f]
    {kbar : Type u} [Field kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
    (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))}
    (z' : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ')))
    (t : letI := connectedSpace_of_isCurve B X f
      Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)) ⟶
        (Stacks.EtaleCohomology.smallEtaleBaseChange (fieldBaseChangeProj (Over.mk f) kbar)).obj
          (representationCover B X _ Λ ρ))
    (Vw : letI := connectedSpace_of_isCurve B X f
      representationCover B X _ Λ ρ ⟶ representationCover B X _ Λ ρ')
    (m : letI := connectedSpace_of_isCurve B X f
      representationFiniteEtaleCover B X _ Λ ρ ⟶ representationFiniteEtaleCover B X _ Λ ρ')
    (hm : m.left = Vw.left)
    (hcov : letI := connectedSpace_of_isCurve B X f
      geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ' z' =
        t ≫ (Stacks.EtaleCohomology.smallEtaleBaseChange
          (fieldBaseChangeProj (Over.mk f) kbar)).map Vw) :
    letI := connectedSpace_of_isCurve B X f
    geometricGlobalSectionsEval B X f kbar Λ y ρ' z' =
      representationFibreEquiv B X _ Λ ρ' ((finiteEtaleFiberFunctor _).map m
        (geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ t)) := by
  let := connectedSpace_of_isCurve B X f
  have hpt : geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ'
      (t ≫ (Stacks.EtaleCohomology.smallEtaleBaseChange (fieldBaseChangeProj (Over.mk f) kbar)).map
        Vw) =
      (finiteEtaleFiberFunctor _).map m (geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ t) := by
    refine Subtype.ext ?_
    show y.hom ≫ 𝟙 _ ≫ (t.left ≫ ((Stacks.EtaleCohomology.smallEtaleBaseChange
      (fieldBaseChangeProj (Over.mk f) kbar)).map Vw).left) ≫ pullback.fst _ _ =
      (y.hom ≫ 𝟙 _ ≫ t.left ≫ pullback.fst _ _) ≫ m.left
    rw [hm]
    have e1 := smallEtaleBaseChange_map_left_fst (fieldBaseChangeProj (Over.mk f) kbar) Vw
    exact (congrArg (fun w => y.hom ≫ 𝟙 _ ≫ w) ((Category.assoc _ _ _).trans
      ((congrArg (t.left ≫ ·) e1).trans (Category.assoc _ _ _).symm))).trans
      ((congrArg (y.hom ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)
  exact (congrArg (fun w => representationFibreEquiv B X _ Λ ρ'
    (geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ' w)) hcov).trans
    (congrArg (representationFibreEquiv B X _ Λ ρ') hpt)

omit [IsAlgClosed kbar] in
/-- **The evaluation is `Λ`-linear.** Multiplication by `a` on a global section of `pr⁻¹ℱ_ρ`
corresponds to composing the `X`-morphism to the representing cover with the endomorphism of the
cover representing multiplication by `a`, which acts on the geometric fibre as multiplication by
`a` on `M`. -/
theorem geometricGlobalSectionsEval_smul
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (a : Λ)
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ))) :
    geometricGlobalSectionsEval B X f kbar Λ y ρ (a • z) =
      a • geometricGlobalSectionsEval B X f kbar Λ y ρ z := by
  let := connectedSpace_of_isCurve B X f
  set t := geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ z with ht
  have hz := (geometricGlobalSectionsCoverEquiv_eq_iff B X f kbar Λ y ρ z t).mp ht.symm
  let Va := (SmallEtale.toEtaleSite B X.1 X.2).map
    ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.map
      (representationSetSheafScalar B X _ Λ ρ a)).hom
  have hcov : geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ (a • z) =
      t ≫ (Stacks.EtaleCohomology.smallEtaleBaseChange (fieldBaseChangeProj (Over.mk f) kbar)).map
        Va := by
    refine (geometricGlobalSectionsCoverEquiv_eq_iff B X f kbar Λ y ρ (a • z) _).mpr ?_
    refine (map_smul (ModuleCat.Hom.hom ((geometricRepresentationRestriction B X f kbar Λ y ρ).ΓRes
      (op (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)))))) a z).trans ?_
    refine (congrArg (a • ·) hz).trans ?_
    refine (map_smul (ModuleCat.Hom.hom
      ((geometricRepresentationRestriction B X f kbar Λ y ρ).obj.map t.op)) a _).symm.trans ?_
    refine Eq.trans ?_ (moduleSheaf_map_comp_op_apply Λ _ _ _ _).symm
    refine congrArg
      (fun w => (geometricRepresentationRestriction B X f kbar Λ y ρ).obj.map t.op w) ?_
    refine (map_smul (ModuleCat.Hom.hom (((etaleModuleInverseImageAdj.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk f) kbar)).unit.app _).hom.app _)) a _).symm.trans ?_
    refine Eq.trans ?_ (moduleUnitSection_map Λ _ _ Va _)
    exact congrArg (fun w => moduleUnitSection Λ (fieldBaseChangeProj (Over.mk f) kbar) _ w)
      (representationTautologicalSection_smul B X _ Λ ρ a)
  have h3 := representationFibreEquiv_scalar B X _ Λ ρ a
    (geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ t)
  exact (geometricGlobalSectionsEval_eq_of_coverEquiv_eq B X Λ f y (a • z) t Va
    ((representingCover B X).map (representationSetSheafScalar B X _ Λ ρ a)) rfl hcov).trans
    h3

omit [IsAlgClosed kbar] in
/-- **The evaluation is natural in `ρ`.** For a morphism `φ : ρ ⟶ ρ'`, evaluating the image of a
global section under `Γ(X_k̄, pr⁻¹ℱ_φ)` is `φ` applied to the evaluation. -/
theorem geometricGlobalSectionsEval_naturality
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))}
    (φ : ρ ⟶ ρ')
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ))) :
    letI := connectedSpace_of_isCurve B X f
    geometricGlobalSectionsEval B X f kbar Λ y ρ'
        ((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).map
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).map
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map φ)) z) =
      φ.hom.hom.hom.hom.hom (geometricGlobalSectionsEval B X f kbar Λ y ρ z) := by
  let := connectedSpace_of_isCurve B X f
  set t := geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ z with ht
  have hz := (geometricGlobalSectionsCoverEquiv_eq_iff B X f kbar Λ y ρ z t).mp ht.symm
  let Vφ := (SmallEtale.toEtaleSite B X.1 X.2).map ((representationCoverSmall B X _ Λ).map φ).hom
  let g := (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).map
    ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map φ)
  have hcov : geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ'
      ((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).map g z) =
      t ≫ (Stacks.EtaleCohomology.smallEtaleBaseChange (fieldBaseChangeProj (Over.mk f) kbar)).map
        Vφ := by
    refine (geometricGlobalSectionsCoverEquiv_eq_iff B X f kbar Λ y ρ' _ _).mpr ?_
    refine (ConcreteCategory.congr_hom (Sheaf.ΓRes_naturality g
      (op (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar))))) z).trans ?_
    refine (congrArg (fun w => g.hom.app _ w) hz).trans ?_
    refine (ConcreteCategory.congr_hom (g.hom.naturality t.op) _).trans ?_
    refine Eq.trans ?_ (moduleSheaf_map_comp_op_apply Λ _ _ _ _).symm
    refine congrArg
      (fun w => (geometricRepresentationRestriction B X f kbar Λ y ρ').obj.map t.op w) ?_
    have hu := congrArg (fun ψ => ψ.hom.app (op (representationCover B X _ Λ ρ)))
      ((etaleModuleInverseImageAdj.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).unit.naturality
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map φ))
    refine (ConcreteCategory.congr_hom hu
      (representationTautologicalSection B X _ Λ ρ)).symm.trans ?_
    refine Eq.trans ?_ (moduleUnitSection_map Λ _ _ Vφ _)
    exact congrArg (fun w => moduleUnitSection Λ (fieldBaseChangeProj (Over.mk f) kbar) _ w)
      (representationTautologicalSection_naturality B X _ Λ φ)
  have h3 := representationFibreEquiv_naturality B X _ Λ φ
    (geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ t)
  have h4 := (geometricGlobalSectionsEval_eq_of_coverEquiv_eq B X Λ f y _ t Vφ
    ((representingCover B X).map ((representationSetSheaf B X (y.map (fieldBaseChangeObjProj B X f
      kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map φ)) rfl hcov)
  rw [h4, h3]
  rfl

omit [IsAlgClosed kbar] in
/-- **The evaluation is additive.** Global sections of `pr⁻¹ℱ_ρ` form an additive functor of `ρ`
(it is isomorphic, by Tags 0DV6 and 0DV5, to the invariants of the restriction to `π₁(X_k̄)`;
that isomorphism is used here only to know additivity), the underlying module of `ρ` is one too,
and the evaluation is natural (`AlgebraicGeometry.geometricGlobalSectionsEval_naturality`), so it
is additive (`CategoryTheory.Functor.map_add_of_naturality`). -/
theorem geometricGlobalSectionsEval_add
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (z₁ z₂ : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ))) :
    geometricGlobalSectionsEval B X f kbar Λ y ρ (z₁ + z₂) =
      geometricGlobalSectionsEval B X f kbar Λ y ρ z₁ +
        geometricGlobalSectionsEval B X f kbar Λ y ρ z₂ := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
        y)).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have : (finiteTypeContinuousModuleInvariants Λ
      (EtaleFundamentalGroup (fieldBaseChange (Over.mk f) kbar) y)).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  have : (finiteTypeContinuousModuleι Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) ⋙
      continuousModuleToModuleCat Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  have : (representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ ⋙
      etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar) ⋙
      etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).Additive :=
    Functor.additive_of_iso (representationSheafPullbackGlobalSectionsIso B
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)) Λ y).symm
  exact Functor.map_add_of_naturality
    (representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ ⋙
      etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar) ⋙
      etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar))
    (finiteTypeContinuousModuleι Λ _ ⋙ continuousModuleToModuleCat Λ _)
    (fun ρ => geometricGlobalSectionsEval B X f kbar Λ y ρ)
    (fun φ z => geometricGlobalSectionsEval_naturality B X f kbar Λ y φ z) ρ z₁ z₂

omit [Fintype Λ] [Smooth f] [IsAlgClosed kbar] in
/-- If `π₁(X_k̄, η̄)` acts trivially on `ρ`, it acts trivially on the geometric fibre of the
representing cover of `ℱ_ρ`. -/
theorem representationFibre_geometric_trivial [Finite Λ]
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ∀ (g : EtaleFundamentalGroup (fieldBaseChange (Over.mk f) kbar) y)
      (p : finiteEtaleFiber (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
          (representationFiniteEtaleCover B X _ Λ ρ)),
      ((etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g).app
          (representationFiniteEtaleCover B X _ Λ ρ)).hom p = p := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  intro g p
  apply (representationFibreEquiv B X _ Λ ρ).injective
  rw [representationFibreEquiv_smul, hρ g]
  rfl

/-- **For `ρ` trivial on `π₁(X_k̄)`, the evaluation is bijective.** Sections of the pulled back
representing cover are its fibre points, because `π₁(X_k̄, η̄)` acts trivially on them
(`AlgebraicGeometry.bijective_finiteEtaleFiber_map_terminalCoverPoint`, Tag 0BND (1)). -/
theorem bijective_geometricGlobalSectionsEval
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1) :
    Function.Bijective (geometricGlobalSectionsEval B X f kbar Λ y ρ) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  let V := representationFiniteEtaleCover B X _ Λ ρ
  let pr := (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
  let W := (finiteEtaleBaseChange pr).obj V
  -- sections in the small étale site are sections in the finite étale covers
  let conv : (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)) ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange (fieldBaseChangeProj (Over.mk f) kbar)).obj
        (representationCover B X _ Λ ρ)) ≃ (terminalCover (fieldBaseChange (Over.mk f) kbar) ⟶ W) :=
    { toFun := fun t => MorphismProperty.Over.homMk t.left (smallEtaleBaseChange_w _ t)
      invFun := fun t => MorphismProperty.Over.homMk t.left (MorphismProperty.Over.w t)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hW : ∀ (σ : EtaleFundamentalGroup (fieldBaseChange (Over.mk f) kbar) y)
      (p : (finiteEtaleFiberFunctor y).obj W), (σ.app W).hom p = p := by
    intro σ p
    apply (finiteEtaleFiberProjectionEquiv pr y V).injective
    show finiteEtaleFiberProjection pr y V _ = finiteEtaleFiberProjection pr y V p
    rw [etaleFundamentalGroupMap_finiteEtaleFiberProjection]
    exact representationFibre_geometric_trivial B X f kbar Λ y ρ hρ σ _
  have hfp : geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ =
      (finiteEtaleFiberProjectionEquiv pr y V) ∘
        (fun t : terminalCover (fieldBaseChange (Over.mk f) kbar) ⟶ W =>
          (finiteEtaleFiberFunctor y).map t (terminalCoverPoint y)) ∘ conv := by
    funext t
    exact Subtype.ext ((congrArg (y.hom ≫ ·) (Category.id_comp _)).trans
      (Category.assoc _ _ _).symm)
  have hfpb : Function.Bijective (geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ) := by
    rw [hfp]
    exact (Equiv.bijective _).comp
      ((bijective_finiteEtaleFiber_map_terminalCoverPoint y W hW).comp (Equiv.bijective _))
  exact (Equiv.bijective _).comp (hfpb.comp (Equiv.bijective _))

/-- **The evaluation intertwines the Galois action with `ρ`.** For `γ ∈ π₁(X, x̄)` with image
`σ ∈ Aut(k̄/k)`, the action of `σ` on `Γ(X_k̄, pr⁻¹ℱ_ρ)` composes the `X`-morphism `X_k̄ ⟶ V` with
`id × Spec σ` (`Stacks.EtaleCohomology.ΓRes_selfMapTwistAction_of_moduleUnitSection`), and on the
fibre point this is `γ` (`AlgebraicGeometry.fieldBaseChangeCoverPoint_galoisBaseChange`), which
`AlgebraicGeometry.representationFibreEquiv` carries to `ρ(γ)`. -/
theorem geometricGlobalSectionsEval_galois
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricGlobalSectionsEval B X f kbar Λ y ρ
        ((fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) kbar
          (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)) _).hom z) =
      (finiteTypeContinuousModuleRepresentation Λ _ ρ) γ
        (geometricGlobalSectionsEval B X f kbar Λ y ρ z) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  set σ := geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ) with hσ
  set t := geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ z with ht
  have hz := (geometricGlobalSectionsCoverEquiv_eq_iff B X f kbar Λ y ρ z t).mp ht.symm
  let s := galoisBaseChange (Over.mk f) kbar σ
  have hs : s ≫ fieldBaseChangeProj (Over.mk f) kbar = fieldBaseChangeProj (Over.mk f) kbar :=
    galoisBaseChange_comp_fst _ _ _
  let V := representationCover B X _ Λ ρ
  let τ := t.left ≫ pullback.fst V.hom (fieldBaseChangeProj (Over.mk f) kbar)
  have hτ : τ ≫ V.hom = fieldBaseChangeProj (Over.mk f) kbar :=
    (Category.assoc _ _ _).trans ((congrArg (t.left ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (smallEtaleBaseChange_w _ t)).trans (Category.id_comp _))))
  let t' : Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)) ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange (fieldBaseChangeProj (Over.mk f) kbar)).obj V :=
    MorphismProperty.Over.homMk (pullback.lift (s ≫ τ) (𝟙 _)
      ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) hτ).trans
        (hs.trans (Category.id_comp _).symm)))) (pullback.lift_snd _ _ _)
  have ht' : t'.left ≫ pullback.fst V.hom (fieldBaseChangeProj (Over.mk f) kbar) =
      s ≫ t.left ≫ pullback.fst V.hom (fieldBaseChangeProj (Over.mk f) kbar) :=
    pullback.lift_fst _ _ _
  have haz := ΓRes_selfMapTwistAction_of_moduleUnitSection Λ
    (fieldBaseChangeProj (Over.mk f) kbar) s hs _ (representationTautologicalSection B X _ Λ ρ)
    z t t' hz ht'
  have hcov : geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ
      ((fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) kbar σ _).hom z) = t' :=
    (geometricGlobalSectionsCoverEquiv_eq_iff B X f kbar Λ y ρ _ t').mpr haz
  have hpt : geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ t' =
      fieldBaseChangeCoverPoint B X f kbar y (representationFiniteEtaleCover B X _ Λ ρ) s hs τ hτ :=
    Subtype.ext ((congrArg (y.hom ≫ ·) ((Category.id_comp _).trans ht')))
  have hgal := fieldBaseChangeCoverPoint_galoisBaseChange B X f kbar y γ
    (representationFiniteEtaleCover B X _ Λ ρ)
    (representationFibre_geometric_trivial B X f kbar Λ y ρ hρ) τ hτ
  have hL : geometricGlobalSectionsEval B X f kbar Λ y ρ
      ((fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) kbar σ _).hom z) =
      representationFibreEquiv B X _ Λ ρ (geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ
        (geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ
          ((fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) kbar σ _).hom z))) :=
    rfl
  have hR : geometricGlobalSectionsEval B X f kbar Λ y ρ z =
      representationFibreEquiv B X _ Λ ρ (geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ t) :=
    rfl
  have hfpt : geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ t =
      fieldBaseChangeCoverPoint B X f kbar y (representationFiniteEtaleCover B X _ Λ ρ) (𝟙 _)
        (Category.id_comp _) τ hτ :=
    Subtype.ext rfl
  have hsm := representationFibreEquiv_smul B X _ Λ ρ γ
    (fieldBaseChangeCoverPoint B X f kbar y (representationFiniteEtaleCover B X _ Λ ρ) (𝟙 _)
      (Category.id_comp _) τ hτ)
  rw [hL, hR, hcov, hpt, hgal, hsm, hfpt]

/-- **`Γ(X_k̄, pr⁻¹ℱ_ρ) ≅ M` for `ρ` trivial on the geometric fundamental group, canonically.**
Let `X` be a geometrically connected smooth curve over `k`, `k̄` an algebraically closed algebraic
extension, `η̄` a geometric point of `X_k̄` with image `x̄` in `X`, and `ρ` a finite `Λ`-module `M`
with a continuous action of `π₁(X, x̄)` which is trivial on the image of `π₁(X_k̄, η̄)`. Then the
global sections of the restriction of `ℱ_ρ` to `X_k̄` are `M`.

The map is evaluation at `η̄`, read in `M` through the fibre of the representing cover, and is
built with no choice of non-unique data. `ℱ_ρ` is the sheaf Tag 0DV5 attaches to `ρ`. Its
underlying sheaf of sets is represented, by the dictionary of Tag 03RV, by a finite étale cover
`V ⟶ X`, with a tautological section `ε ∈ ℱ_ρ(V)`
(`AlgebraicGeometry.representationTautologicalSection`), and the fibre of `V` at `x̄` *is* `M`
(`AlgebraicGeometry.representationFibreEquiv`: `geometricFibreSetEquiv` followed by the counit of
Tag 0DV5). On `X_k̄` every section of `pr⁻¹ℱ_ρ` is the pullback `u(ε)` of `ε`, restricted along a
unique `X`-morphism `τ : X_k̄ ⟶ V` (`Stacks.EtaleCohomology.bijective_map_moduleUnitSection`). The
equivalence sends the section to the point `τ ∘ η̄` of the fibre of `V` at `x̄`, read in `M`.

The construction picks only data determined up to unique isomorphism, and it is transported
through those isomorphisms: the inverses of equivalences of categories, the left adjoint `pr⁻¹`,
and the identification of global sections with sections over the final object. In particular it
does not use the existence-only comparison of Tag 0DV6
(`AlgebraicGeometry.representationSheafPullbackIso`, which is built on `Classical.choice` of an
isomorphism and can change by an automorphism of the restriction functor). That comparison
appears only inside the proof of additivity, a statement about the map already constructed. -/
def geometricGlobalSectionsTrivialEquiv
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1) :
    letI := connectedSpace_of_isCurve B X f
    ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))) ≃ₗ[Λ]
      ρ.obj.obj.obj.V :=
  LinearEquiv.ofBijective
    { toFun := geometricGlobalSectionsEval B X f kbar Λ y ρ
      map_add' := geometricGlobalSectionsEval_add B X f kbar Λ y ρ
      map_smul' := geometricGlobalSectionsEval_smul B X f kbar Λ y ρ }
    (bijective_geometricGlobalSectionsEval B X f kbar Λ y ρ hρ)

/-- `AlgebraicGeometry.geometricGlobalSectionsTrivialEquiv` is the evaluation
`AlgebraicGeometry.geometricGlobalSectionsEval`. -/
theorem geometricGlobalSectionsTrivialEquiv_apply
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)))) :
    geometricGlobalSectionsTrivialEquiv B X f kbar Λ y ρ hρ z =
      geometricGlobalSectionsEval B X f kbar Λ y ρ z :=
  rfl

/-- **`Γ(X_k̄, pr⁻¹ℱ_ρ) ≅ M` is Galois-equivariant.** For `γ ∈ π₁(X, x̄)` with image
`σ ∈ Aut(k̄/k)` under `AlgebraicGeometry.geometricQuotientGaloisEquiv`, the equivalence
`AlgebraicGeometry.geometricGlobalSectionsTrivialEquiv` carries the action of `σ` on global
sections (`Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction`) to `ρ(γ)`. -/
theorem geometricGlobalSectionsTrivialEquiv_galois
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricGlobalSectionsTrivialEquiv B X f kbar Λ y ρ hρ
        ((fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) kbar
          (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)) _).hom z) =
      (finiteTypeContinuousModuleRepresentation Λ _ ρ) γ
        (geometricGlobalSectionsTrivialEquiv B X f kbar Λ y ρ hρ z) := by
  rw [geometricGlobalSectionsTrivialEquiv_apply, geometricGlobalSectionsTrivialEquiv_apply]
  exact geometricGlobalSectionsEval_galois B X f kbar Λ y ρ hρ γ z

/-- **`Γ(X_k̄, pr⁻¹ℱ_ρ) ≅ M` is natural in `ρ`.** For a morphism `φ : ρ ⟶ ρ'` of representations
trivial on the geometric fundamental group, the equivalence carries `Γ(X_k̄, pr⁻¹ℱ_φ)` to the
underlying linear map of `φ`. -/
theorem geometricGlobalSectionsTrivialEquiv_naturality
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))}
    (φ : ρ ⟶ ρ')
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (hρ' : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ')
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)))) :
    letI := connectedSpace_of_isCurve B X f
    geometricGlobalSectionsTrivialEquiv B X f kbar Λ y ρ' hρ'
        ((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).map
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).map
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map φ)) z) =
      φ.hom.hom.hom.hom.hom (geometricGlobalSectionsTrivialEquiv B X f kbar Λ y ρ hρ z) := by
  rw [geometricGlobalSectionsTrivialEquiv_apply, geometricGlobalSectionsTrivialEquiv_apply]
  exact geometricGlobalSectionsEval_naturality B X f kbar Λ y φ z

end Main

end AlgebraicGeometry

end
