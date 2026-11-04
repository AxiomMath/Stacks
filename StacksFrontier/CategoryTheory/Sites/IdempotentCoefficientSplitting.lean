module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Whiskering
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsSection
public import StacksFrontier.Algebra.Module.Projective.Determinant.IdempotentQuotient
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat

/-!
# Splitting a sheaf of modules along an idempotent of the coefficient ring

Let `Λ` be a commutative ring and `e` an idempotent, with `Λ₁ = Λ ⧸ (1 - e)`. The quotient map
`Λ → Λ₁` has the `Λ`-linear section `a ↦ a e`, so base change `M ↦ Λ₁ ⊗_Λ M` is both left and right
adjoint to restriction of scalars (`Stacks.ModuleCat.restrictScalarsBaseChangeAdjOfSection`). It
therefore preserves limits and acts on sheaves of modules on any site sectionwise; this is the
sheaf `e F` of the source, a sheaf of `Λ₁`-modules. A sheaf of `Λ`-modules is the biproduct of the
restrictions of scalars of `e F` and `(1 - e) F`.

Being a left adjoint of restriction of scalars, which commutes on the nose with pushforward along
a continuous functor and with sections, base change commutes with the pullback of sheaves and with
constant sheaves. So it preserves local constancy with finite projective values.

## Main definitions

* `IsIdempotentElem.sheafBaseChange`: `F ↦ Λ₁ ⊗_Λ F` on sheaves of `Λ`-modules.
* `IsIdempotentElem.sheafBinaryBicone`: `F` as the biproduct of the restrictions of scalars of
  `Λ₁ ⊗_Λ F` and of `Λ₂ ⊗_Λ F`, `Λ₂ = Λ ⧸ (e)`.

## Main results

* `IsIdempotentElem.isBilimit_sheafBinaryBicone`: it is a biproduct.
* `IsIdempotentElem.sheafPullbackBaseChangeIso`: base change commutes with pullback of sheaves.
* `IsIdempotentElem.isFiniteProjectiveLocallyConstant_sheafBaseChange`: base change preserves
  local constancy with finite projective values.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe w r t u₁ v₁ u₂ v₂

/-! ### Two general facts -/

namespace CategoryTheory

/-- **Transporting a commutation along equivalences.** If the inverses of two equivalences
intertwine `S` and `S'`, so do the functors. -/
public def Equivalence.functorCompIsoOfInverseComp {𝒜 ℬ 𝒜' ℬ' : Type*} [Category* 𝒜]
    [Category* ℬ] [Category* 𝒜'] [Category* ℬ'] (E : 𝒜 ≌ ℬ) (E' : 𝒜' ≌ ℬ') {S : 𝒜 ⥤ 𝒜'}
    {S' : ℬ ⥤ ℬ'} (e : E.inverse ⋙ S ≅ S' ⋙ E'.inverse) : E.functor ⋙ S' ≅ S ⋙ E'.functor :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ E'.counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft _ e.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight E.unitIso.symm _ ≪≫
        Functor.leftUnitor _) _

/-- **A morphism of points commutes with the comparison of fibers and a coefficient functor**
preserving filtered colimits. -/
public theorem GrothendieckTopology.Point.Hom.presheafFiber_app_comp_presheafFiberCompIso_hom
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {A B : Type*} [Category* A]
    [Category* B] [HasColimitsOfSize.{t, t} A] [HasColimitsOfSize.{t, t} B]
    [LocallySmall.{t} C] (G : A ⥤ B) [PreservesFilteredColimitsOfSize.{t, t} G]
    {Φ₁ Φ₂ : GrothendieckTopology.Point.{t} J} (f : Φ₁ ⟶ Φ₂) (P : Cᵒᵖ ⥤ A) :
    f.presheafFiber.app (P ⋙ G) ≫ (Φ₁.presheafFiberCompIso G).hom.app P =
      (Φ₂.presheafFiberCompIso G).hom.app P ≫ G.map (f.presheafFiber.app P) := by
  ext X x
  simp only [Point.Hom.presheafFiber_app, Point.toPresheafFiber_presheafFiberDesc_assoc,
    Point.toPresheafFiber_presheafFiberCompIso_hom_app,
    Point.toPresheafFiber_presheafFiberCompIso_hom_app_assoc, ← G.map_comp,
    Point.toPresheafFiber_presheafFiberDesc]

end CategoryTheory

variable {Λ : Type r} [CommRing Λ] {e : Λ} (he : IsIdempotentElem e)

namespace IsIdempotentElem

/-! ### The module-level functors -/

/-- The section `a ↦ a e` is a section of the structure map of `Λ ⧸ (1 - e)`. -/
public theorem algebraMap_quotientSection (t : Λ ⧸ Ideal.span {1 - e}) :
    algebraMap Λ (Λ ⧸ Ideal.span {1 - e}) (he.quotientSection t) = t :=
  he.mk_quotientSection t

/-- Restriction of scalars along `Λ → Λ ⧸ (1 - e)` is left adjoint to base change. -/
public def restrictScalarsBaseChangeAdj :
    ModuleCat.restrictScalars.{max w r} (algebraMap Λ (Λ ⧸ Ideal.span {1 - e})) ⊣
      Stacks.ModuleCat.baseChangeFunctor.{max w r} Λ (Λ ⧸ Ideal.span {1 - e}) :=
  Stacks.ModuleCat.restrictScalarsBaseChangeAdjOfSection he.quotientSection
    he.algebraMap_quotientSection

/-- The section `a ↦ a e` followed by the quotient map onto `Λ ⧸ (e)` is zero. -/
public theorem algebraMap_one_sub_quotientSection (t : Λ ⧸ Ideal.span {1 - e}) :
    algebraMap Λ (Λ ⧸ Ideal.span {1 - (1 - e)}) (he.quotientSection t) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [he.quotientSection_mk, map_mul, sub_sub_cancel, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e), mul_zero]

/-- The two sections add up to `1`. -/
public theorem quotientSection_one_add :
    he.quotientSection 1 + he.one_sub.quotientSection 1 = 1 := by
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - e})), ← map_one (Ideal.Quotient.mk
    (Ideal.span {1 - (1 - e)})), he.quotientSection_mk, he.one_sub.quotientSection_mk]
  ring

/-! ### Sheaves -/

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- **The sheaf `Λ₁ ⊗_Λ F`** of `Λ₁ = Λ ⧸ (1 - e)`-modules attached to a sheaf `F` of `Λ`-modules,
formed sectionwise. -/
public def sheafBaseChange :
    Sheaf J (ModuleCat.{max w r} Λ) ⥤ Sheaf J (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) :=
  haveI := (restrictScalarsBaseChangeAdj.{w} he).rightAdjoint_preservesLimits
  sheafCompose J (Stacks.ModuleCat.baseChangeFunctor.{max w r} Λ (Λ ⧸ Ideal.span {1 - e}))

public theorem sheafBaseChange_obj_obj (F : Sheaf J (ModuleCat.{max w r} Λ)) :
    ((sheafBaseChange.{w} he J).obj F).obj =
      F.obj ⋙ Stacks.ModuleCat.baseChangeFunctor.{max w r} Λ (Λ ⧸ Ideal.span {1 - e}) :=
  rfl

public theorem sheafBaseChange_map_hom {F G : Sheaf J (ModuleCat.{max w r} Λ)} (f : F ⟶ G) :
    ((sheafBaseChange.{w} he J).map f).hom =
      Functor.whiskerRight f.hom (Stacks.ModuleCat.baseChangeFunctor.{max w r} Λ
        (Λ ⧸ Ideal.span {1 - e})) :=
  rfl

/-- Restriction of scalars along `Λ → Λ ⧸ (1 - e)`, on sheaves. -/
public abbrev sheafRestrictScalars :
    Sheaf J (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) ⥤ Sheaf J (ModuleCat.{max w r} Λ) :=
  sheafCompose J (ModuleCat.restrictScalars.{max w r} (algebraMap Λ (Λ ⧸ Ideal.span {1 - e})))

/-- **Base change is left adjoint to restriction of scalars**, on sheaves. -/
public def sheafBaseChangeAdj : sheafBaseChange.{w} he J ⊣ sheafRestrictScalars.{w} J (e := e) :=
  haveI := (restrictScalarsBaseChangeAdj.{w} he).rightAdjoint_preservesLimits
  Adjunction.restrictFullyFaithful
    ((Stacks.ModuleCat.baseChangeRestrictScalarsAdj.{w} Λ (Λ ⧸ Ideal.span {1 - e})).whiskerRight
      Cᵒᵖ)
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _) (Iso.refl _) (Iso.refl _)

/-- The projection `F ⟶ Λ₁ ⊗_Λ F`, `m ↦ 1 ⊗ m`, as a morphism of sheaves of `Λ`-modules. -/
public def sheafProj (F : Sheaf J (ModuleCat.{max w r} Λ)) :
    F ⟶ (sheafRestrictScalars.{w} J (e := e)).obj ((sheafBaseChange.{w} he J).obj F) :=
  ObjectProperty.homMk (Functor.whiskerLeft F.obj
    (Stacks.ModuleCat.baseChangeRestrictScalarsAdj.{w} Λ (Λ ⧸ Ideal.span {1 - e})).unit)

/-- The inclusion `Λ₁ ⊗_Λ F ⟶ F`, `t ⊗ m ↦ s t • m`, as a morphism of sheaves of `Λ`-modules. -/
public def sheafIncl (F : Sheaf J (ModuleCat.{max w r} Λ)) :
    (sheafRestrictScalars.{w} J (e := e)).obj ((sheafBaseChange.{w} he J).obj F) ⟶ F :=
  ObjectProperty.homMk (Functor.whiskerLeft F.obj (restrictScalarsBaseChangeAdj.{w} he).counit)

public theorem sheafIncl_sheafProj (F : Sheaf J (ModuleCat.{max w r} Λ)) :
    sheafIncl.{w} he J F ≫ sheafProj.{w} he J F = 𝟙 _ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  exact Stacks.ModuleCat.sectionSMul_comp_tmulOne he.quotientSection he.algebraMap_quotientSection
    (F.obj.obj U)

/-- The section of `Λ ⧸ (e)`, `a ↦ a (1 - e)`, followed by the quotient map onto `Λ ⧸ (1 - e)`, is
zero. -/
public theorem algebraMap_quotientSection_one_sub (t : Λ ⧸ Ideal.span {1 - (1 - e)}) :
    algebraMap Λ (Λ ⧸ Ideal.span {1 - e}) (he.one_sub.quotientSection t) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [he.one_sub.quotientSection_mk, map_mul, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self (1 - e)), mul_zero]

/-- The inclusion for `e₁` followed by the projection for `e₂` vanishes if the section for `e₁`
followed by `Λ → Λ ⧸ (1 - e₂)` is zero. -/
private theorem sheafIncl_comp_sheafProj_eq_zero {e₁ e₂ : Λ} (he₁ : IsIdempotentElem e₁)
    (he₂ : IsIdempotentElem e₂) (F : Sheaf J (ModuleCat.{max w r} Λ))
    (h : ∀ t, algebraMap Λ (Λ ⧸ Ideal.span {1 - e₂}) (he₁.quotientSection t) = 0) :
    sheafIncl.{w} he₁ J F ≫ sheafProj.{w} he₂ J F = 0 := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  exact Stacks.ModuleCat.sectionSMul_comp_tmulOne_eq_zero he₁.quotientSection h (F.obj.obj U)

/-- The two summands are orthogonal. -/
public theorem sheafIncl_sheafProj_one_sub (F : Sheaf J (ModuleCat.{max w r} Λ)) :
    sheafIncl.{w} he J F ≫ sheafProj.{w} he.one_sub J F = 0 :=
  sheafIncl_comp_sheafProj_eq_zero J he he.one_sub F he.algebraMap_one_sub_quotientSection

/-- The two summands are orthogonal. -/
public theorem sheafIncl_one_sub_sheafProj (F : Sheaf J (ModuleCat.{max w r} Λ)) :
    sheafIncl.{w} he.one_sub J F ≫ sheafProj.{w} he J F = 0 :=
  sheafIncl_comp_sheafProj_eq_zero J he.one_sub he F he.algebraMap_quotientSection_one_sub

/-- **`F` is the biproduct of `Λ₁ ⊗_Λ F` and `Λ₂ ⊗_Λ F`**, `Λ₁ = Λ ⧸ (1 - e)` and `Λ₂ = Λ ⧸ (e)`,
both read as sheaves of `Λ`-modules. -/
public def sheafBinaryBicone (F : Sheaf J (ModuleCat.{max w r} Λ)) :
    BinaryBicone ((sheafRestrictScalars.{w} J (e := e)).obj ((sheafBaseChange.{w} he J).obj F))
      ((sheafRestrictScalars.{w} J (e := 1 - e)).obj
        ((sheafBaseChange.{w} he.one_sub J).obj F)) where
  pt := F
  fst := sheafProj.{w} he J F
  snd := sheafProj.{w} he.one_sub J F
  inl := sheafIncl.{w} he J F
  inr := sheafIncl.{w} he.one_sub J F
  inl_fst := sheafIncl_sheafProj he J F
  inl_snd := sheafIncl_sheafProj_one_sub he J F
  inr_fst := sheafIncl_one_sub_sheafProj he J F
  inr_snd := sheafIncl_sheafProj he.one_sub J F

public theorem sheafBinaryBicone_total (F : Sheaf J (ModuleCat.{max w r} Λ)) :
    sheafProj.{w} he J F ≫ sheafIncl.{w} he J F +
      sheafProj.{w} he.one_sub J F ≫ sheafIncl.{w} he.one_sub J F = 𝟙 F := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  show he.quotientSection 1 • m + he.one_sub.quotientSection 1 • m = m
  rw [← add_smul, he.quotientSection_one_add, one_smul]

/-- **The splitting is a biproduct.** -/
public def isBilimit_sheafBinaryBicone (F : Sheaf J (ModuleCat.{max w r} Λ)) :
    (sheafBinaryBicone.{w} he J F).IsBilimit :=
  isBinaryBilimitOfTotal _ (sheafBinaryBicone_total he J F)

/-! ### Pullback and constant sheaves -/

section Pullback

variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (φ : C ⥤ D)
  [φ.IsContinuous J K]
  [(φ.sheafPushforwardContinuous (ModuleCat.{max w r} Λ) J K).IsRightAdjoint]
  [(φ.sheafPushforwardContinuous (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) J K).IsRightAdjoint]

/-- **Base change commutes with the pullback of sheaves** along a continuous functor: both are left
adjoints, and their right adjoints, restriction of scalars and pushforward, commute on the nose. -/
public def sheafPullbackBaseChangeIso :
    φ.sheafPullback (ModuleCat.{max w r} Λ) J K ⋙ sheafBaseChange.{w} he K ≅
      sheafBaseChange.{w} he J ⋙
        φ.sheafPullback (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) J K :=
  Adjunction.leftAdjointUniq
    ((φ.sheafAdjunctionContinuous (ModuleCat.{max w r} Λ) J K).comp (sheafBaseChangeAdj.{w} he K))
    (Adjunction.ofNatIsoRight
      ((sheafBaseChangeAdj.{w} he J).comp
        (φ.sheafAdjunctionContinuous (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) J K))
      (Iso.refl _))

end Pullback

section Constant

variable [HasWeakSheafify J (ModuleCat.{max w r} Λ)]
  [HasWeakSheafify J (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e}))]

/-- **Base change commutes with constant sheaves**, on a site with a terminal object: both
composites are left adjoint to the sections over the terminal object followed by restriction of
scalars. -/
public def constantSheafBaseChangeIso {T : C} (hT : IsTerminal T) :
    constantSheaf J (ModuleCat.{max w r} Λ) ⋙ sheafBaseChange.{w} he J ≅
      Stacks.ModuleCat.baseChangeFunctor.{max w r} Λ (Λ ⧸ Ideal.span {1 - e}) ⋙
        constantSheaf J (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) :=
  Adjunction.leftAdjointUniq
    ((constantSheafAdj J (ModuleCat.{max w r} Λ) hT).comp (sheafBaseChangeAdj.{w} he J))
    (((Stacks.ModuleCat.baseChangeRestrictScalarsAdj.{w} Λ (Λ ⧸ Ideal.span {1 - e})).comp
      (constantSheafAdj J (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) hT)).ofNatIsoRight
        (Iso.refl _))

end Constant

/-- Base change commutes with restriction to a slice `J.over V`, on the nose. -/
public def overPullbackBaseChangeIso (V : C) :
    J.overPullback (ModuleCat.{max w r} Λ) V ⋙ sheafBaseChange.{w} he (J.over V) ≅
      sheafBaseChange.{w} he J ⋙ J.overPullback (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) V :=
  Iso.refl _

/-- **Base change preserves local constancy with finite projective values.** -/
public theorem isFiniteProjectiveLocallyConstant_sheafBaseChange
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{max w r} Λ)]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e}))]
    {F : Sheaf J (ModuleCat.{max w r} Λ)}
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ J F) :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant (Λ ⧸ Ideal.span {1 - e}) J
      ((sheafBaseChange.{w} he J).obj F) := by
  intro U
  obtain ⟨I, V, f, hcover, hloc⟩ := hF U
  refine ⟨I, V, f, hcover, fun i => ?_⟩
  obtain ⟨E, hfin, hproj, ⟨eE⟩⟩ := hloc i
  refine ⟨(Stacks.ModuleCat.baseChangeFunctor.{max w r} Λ (Λ ⧸ Ideal.span {1 - e})).obj E,
    ?_, ?_, ⟨?_⟩⟩
  · show Module.Finite _ ((Λ ⧸ Ideal.span {1 - e}) ⊗[Λ] E)
    infer_instance
  · show Module.Projective _ ((Λ ⧸ Ideal.span {1 - e}) ⊗[Λ] E)
    infer_instance
  · exact (constantSheafBaseChangeIso.{w} he (J.over (V i)) Over.mkIdTerminal).symm.app E ≪≫
      (sheafBaseChange.{w} he (J.over (V i))).mapIso eE ≪≫
        (overPullbackBaseChangeIso.{w} he J (V i)).app F

end IsIdempotentElem

end
