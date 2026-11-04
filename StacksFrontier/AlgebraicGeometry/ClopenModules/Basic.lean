module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.GenericPointCoproduct.Basic

/-!
# Modules along a decomposition into two open and closed pieces

Let `X = U ⊔ V` with `U` and `V` open and disjoint. A sheaf of modules `F` on `X` is the
biproduct of the pushforwards of its restrictions to `U` and to `V`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_clopenSplitting`: the map
  `F ⟶ j_{U*}(F|_U) ⊞ j_{V*}(F|_V)` given by the two units is an isomorphism.
* `AlgebraicGeometry.Scheme.Modules.isZero_restrict_pushforward_of_disjoint`: the pushforward of a
  module on `V` restricts to zero on an open disjoint from `V`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The pushforward of a module from an open `V` restricts to zero on an open disjoint from `V`. -/
theorem isZero_restrict_pushforward_of_disjoint {U V : X.Opens} (h : U ⊓ V = ⊥)
    (G : V.toScheme.Modules) : IsZero (((pushforward V.ι).obj G).restrict U.ι) := by
  refine Stacks.AlgebraicGeometry.GenericPointCoproduct.isZero_of_subsingleton_sections _
    fun W => ?_
  refine AddCommGrpCat.subsingleton_of_isZero (TopCat.Sheaf.isTerminalOfEqEmpty
    (⟨G.presheaf, G.isSheaf⟩ : TopCat.Sheaf Ab.{u} V.toScheme) ?_).isZero
  ext x
  simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hx
  have : (V.ι x : X) ∈ (U ⊓ V : X.Opens) := ⟨Scheme.Opens.ι_image_le U W hx, x.2⟩
  rwa [h] at this

variable (U V : X.Opens)

/-- The map `F ⟶ j_{U*}(F|_U) ⊞ j_{V*}(F|_V)` whose components are the units of the
restriction–pushforward adjunctions of the two open immersions. -/
def clopenSplitting (F : X.Modules) :
    F ⟶ (pushforward U.ι).obj (F.restrict U.ι) ⊞ (pushforward V.ι).obj (F.restrict V.ι) :=
  biprod.lift ((restrictAdjunction U.ι).unit.app F) ((restrictAdjunction V.ι).unit.app F)

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

/-- Restriction of modules along an open immersion is an additive functor. -/
instance (W : X.Opens) : (restrictFunctor W.ι).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- Restricting the unit of the restriction–pushforward adjunction of an open immersion gives an
isomorphism. -/
instance isIso_restrict_map_unit (W : X.Opens) (F : X.Modules) :
    IsIso ((restrictFunctor W.ι).map ((restrictAdjunction W.ι).unit.app F)) := by
  have : IsIso ((restrictFunctor W.ι).map ((restrictAdjunction W.ι).unit.app F) ≫
      (restrictAdjunction W.ι).counit.app ((restrictFunctor W.ι).obj F)) := by
    rw [(restrictAdjunction W.ι).left_triangle_components F]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((restrictAdjunction W.ι).counit.app _)

omit U V in
/-- In a preadditive category, `biprod.lift a b` is an isomorphism when `a` is and the target of
`b` is zero. -/
theorem isIso_biprod_lift_of_isZero_right {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {A B D : C} (a : A ⟶ B) (b : A ⟶ D) [IsIso a] (hD : IsZero D) :
    IsIso (biprod.lift a b) :=
  ⟨⟨biprod.fst ≫ inv a, by simp, biprod.hom_ext' _ _
    (biprod.hom_ext _ _ (by simp) (hD.eq_of_tgt _ _)) (hD.eq_of_src _ _)⟩⟩

omit U V in
/-- In a preadditive category, `biprod.lift a b` is an isomorphism when `b` is and the target of
`a` is zero. -/
theorem isIso_biprod_lift_of_isZero_left {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {A B D : C} (a : A ⟶ D) (b : A ⟶ B) [IsIso b] (hD : IsZero D) :
    IsIso (biprod.lift a b) :=
  ⟨⟨biprod.snd ≫ inv b, by simp, biprod.hom_ext' _ _
    (hD.eq_of_src _ _) (biprod.hom_ext _ _ (hD.eq_of_tgt _ _) (by simp))⟩⟩

variable {U V}

/-- **A module is the biproduct of the pushforwards of its restrictions to two complementary
opens**: for `U ⊓ V = ⊥` and `U ⊔ V = ⊤`, the map `F ⟶ j_{U*}(F|_U) ⊞ j_{V*}(F|_V)` given by
the two units is an isomorphism. -/
theorem isIso_clopenSplitting (hdisj : U ⊓ V = ⊥) (hcov : U ⊔ V = ⊤) (F : X.Modules) :
    IsIso (clopenSplitting U V F) := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _
    (fun b : Bool => cond b U V) (by rwa [IsOpenCover, iSup_bool_eq]) fun b => ?_
  cases b <;> dsimp only [cond] <;>
    rw [← isIso_comp_right_iff _ ((restrictFunctor _).mapBiprod _ _).hom, clopenSplitting,
      biprod.map_lift_mapBiprod]
  · exact isIso_biprod_lift_of_isZero_left _ _
      (isZero_restrict_pushforward_of_disjoint (by rw [inf_comm, hdisj]) _)
  · exact isIso_biprod_lift_of_isZero_right _ _ (isZero_restrict_pushforward_of_disjoint hdisj _)

/-- The unit `F ⟶ j_{U*}(F|_U)` is the first component of the splitting. -/
@[reassoc (attr := simp)]
theorem clopenSplitting_fst (F : X.Modules) :
    clopenSplitting U V F ≫ biprod.fst = (restrictAdjunction U.ι).unit.app F :=
  biprod.lift_fst _ _

/-- **A module vanishing on `V` is the pushforward of its restriction to the complement `U`**:
the unit `F ⟶ j_{U*}(F|_U)` is an isomorphism when `F|_V = 0`. -/
theorem isIso_restrictAdjunction_unit_app_of_isZero (hdisj : U ⊓ V = ⊥) (hcov : U ⊔ V = ⊤)
    (F : X.Modules) (hF : IsZero (F.restrict V.ι)) :
    IsIso ((restrictAdjunction U.ι).unit.app F) := by
  have := isIso_clopenSplitting hdisj hcov F
  have : IsIso (biprod.fst : (pushforward U.ι).obj (F.restrict U.ι) ⊞
      (pushforward V.ι).obj (F.restrict V.ι) ⟶ _) :=
    (isoBiprodZero (Functor.map_isZero (pushforward V.ι) hF)).isIso_inv
  rw [← clopenSplitting_fst (U := U) (V := V) F]
  infer_instance

/-- The pushforward of a module from `U` is a direct summand of `F` with retraction the unit:
`j_{U*}(F|_U) ⟶ F ⟶ j_{U*}(F|_U)` is the identity, the first map being the inclusion of the first
summand of the splitting. -/
theorem exists_comp_restrictAdjunction_unit_app_eq_id (hdisj : U ⊓ V = ⊥) (hcov : U ⊔ V = ⊤)
    (F : X.Modules) :
    ∃ s : (pushforward U.ι).obj (F.restrict U.ι) ⟶ F,
      s ≫ (restrictAdjunction U.ι).unit.app F = 𝟙 _ := by
  have := isIso_clopenSplitting hdisj hcov F
  exact ⟨biprod.inl ≫ inv (clopenSplitting U V F), by
    rw [← clopenSplitting_fst (U := U) (V := V) F, Category.assoc, IsIso.inv_hom_id_assoc,
      biprod.inl_fst]⟩

/-- A right adjoint of the pushforward from `U` kills the pushforward of any module from the
disjoint open `V`. -/
theorem isZero_rightAdjoint_obj_pushforward (hdisj : U ⊓ V = ⊥) {R : X.Modules ⥤ U.toScheme.Modules}
    (adj : pushforward U.ι ⊣ R) (G : V.toScheme.Modules) :
    IsZero (R.obj ((pushforward V.ι).obj G)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (adj.homEquiv _ _).symm.injective
  apply ((restrictAdjunction V.ι).homEquiv _ _).symm.injective
  exact (isZero_restrict_pushforward_of_disjoint (by rw [inf_comm, hdisj]) _).eq_of_src _ _

/-- **A right adjoint of the pushforward from an open and closed piece is restriction**: if
`j_{U*} ⊣ R` for `U` with complement `V`, then `R(F) ≅ F|_U`. -/
def rightAdjointObjIsoRestrict (hdisj : U ⊓ V = ⊥) (hcov : U ⊔ V = ⊤)
    {R : X.Modules ⥤ U.toScheme.Modules} (adj : pushforward U.ι ⊣ R) (F : X.Modules) :
    R.obj F ≅ F.restrict U.ι :=
  haveI := isIso_clopenSplitting hdisj hcov F
  haveI := adj.right_adjoint_additive
  R.mapIso (asIso (clopenSplitting U V F)) ≪≫ R.mapBiprod _ _ ≪≫
    (isoBiprodZero (isZero_rightAdjoint_obj_pushforward hdisj adj _)).symm ≪≫
    (asIso (adj.unit.app (F.restrict U.ι))).symm

omit U V in
/-- Generating sections of a module restrict to generating sections of its restriction to an
open. -/
def generatingSectionsRestrict {F : X.Modules} (σ : F.GeneratingSections) (W : X.Opens) :
    (F.restrict W.ι).GeneratingSections :=
  @SheafOfModules.GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _ σ (restrictFunctor W.ι)
    (restrictAdjunction W.ι).leftAdjoint_preservesColimits (restrictUnitIso W.ι).symm

end AlgebraicGeometry.Scheme.Modules
