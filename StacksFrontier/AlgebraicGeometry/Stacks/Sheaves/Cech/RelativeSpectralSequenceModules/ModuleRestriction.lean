module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.Algebra.Homology.DerivedCategory.FunctorialInjectiveResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.SpectralSequence.DerivedTensor
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.TwoFibreProductEqualizers
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Subobject.CokernelComparisons
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Restriction of sheaves of modules along the relative Čech nerve

Auxiliary constructions for the relative Čech-to-cohomology spectral sequence for sheaves of
modules: the right Kan extension of presheaves and sheaves of modules along a functor, right adjoint
to restriction, and the facts that the inverse image of sheaves of modules along a faithful
1-morphism whose source has equalizers preserves injective objects and is exact.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject

namespace Stacks.RelativeCech

universe u vᵤ vₓ wᵤ wₓ a v₁ w₁ v₂ w₂ r

section ModuleRightKan

open CategoryTheory CategoryTheory.Limits Opposite
universe vC vD uC uD rR m
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{rR})
  (N : PresheafOfModules.{max uC vD m} (f.op ⋙ R))

/-- The right Kan extension of a presheaf of modules along `f.op`, whose sections are the
compatible families of `PresheafOfModules.directImageSections.{rR, m}`. -/
private def ranPresheaf : PresheafOfModules.{max uC vD m} R where
  obj x := ModuleCat.of (R.obj x) (PresheafOfModules.directImageSections.{rR, m} f R N x)
  map {x y} a := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map a).hom).obj
      (ModuleCat.of (R.obj y) (PresheafOfModules.directImageSections.{rR, m} f R N y)))
    { toFun := fun s => ⟨fun j => s.val ((StructuredArrow.map a).obj j),
        fun {_ _} g => s.property ((StructuredArrow.map a).map g)⟩
      map_add' := by intros; rfl
      map_smul' := by
        intro rR s
        apply Subtype.ext
        funext j
        change R.map (a ≫ j.hom) rR • _ = R.map j.hom (R.map a rR) • _
        rw [R.map_comp]
        rfl }
  map_id x := by
    ext s
    apply Subtype.ext
    funext j
    change s.val ((StructuredArrow.map (𝟙 x)).obj j) = s.val j
    rcases j with ⟨⟨⟨⟩⟩, j, b⟩
    change s.val (StructuredArrow.mk (𝟙 x ≫ b)) = s.val (StructuredArrow.mk b)
    rw [Category.id_comp]
  map_comp a b := by
    ext s
    apply Subtype.ext
    funext j
    change s.val ((StructuredArrow.map (a ≫ b)).obj j) =
      s.val ((StructuredArrow.map a).obj ((StructuredArrow.map b).obj j))
    rcases j with ⟨⟨⟨⟩⟩, j, c⟩
    change s.val (StructuredArrow.mk ((a ≫ b) ≫ c)) =
      s.val (StructuredArrow.mk (a ≫ b ≫ c))
    rw [Category.assoc]

variable (N : PresheafOfModules.{max uC vD m} (f.op ⋙ R))

/-- The counit of `ranPresheaf`: a compatible family over `f.op.obj x` is sent to its component at
the identity arrow. -/
private def ranCounit :
    f.op ⋙ (ranPresheaf.{vC, vD, uC, uD, rR, m} f R N).presheaf ⟶ N.presheaf where
  app x := AddCommGrpCat.ofHom
    { toFun := fun s => s.val (StructuredArrow.mk (𝟙 (f.op.obj x)))
      map_zero' := rfl
      map_add' := by intros; rfl }
  naturality {x y} a := by
    ext s
    change s.val ((StructuredArrow.map (f.op.map a)).obj
      (StructuredArrow.mk (𝟙 (f.op.obj y)))) =
      N.map a (s.val (StructuredArrow.mk (𝟙 (f.op.obj x))))
    have h := s.property (StructuredArrow.homMk a :
      StructuredArrow.mk (𝟙 (f.op.obj x)) ⟶ StructuredArrow.mk (f.op.map a))
    change N.map a (s.val (StructuredArrow.mk (𝟙 (f.op.obj x)))) =
      s.val (StructuredArrow.mk (f.op.map a)) at h
    change s.val (StructuredArrow.mk (f.op.map a ≫ 𝟙 _)) = _
    rw [Category.comp_id]
    exact h.symm

/-- The counit of `ranPresheaf` applied to the restriction of a compatible family along an indexing
arrow is the component of that family at the arrow. -/
private lemma ranCounit_apply (x : Dᵒᵖ) (j : StructuredArrow x f.op)
    (s : PresheafOfModules.directImageSections.{rR, m} f R N x) :
    (ranCounit.{vC, vD, uC, uD, rR, m} f R N).app j.right
        ((ranPresheaf.{vC, vD, uC, uD, rR, m} f R N).map j.hom s) = s.val j := by
  change s.val (StructuredArrow.mk (j.hom ≫ 𝟙 _)) = s.val j
  rw [Category.comp_id]
  rfl

/-- `ranPresheaf` together with its counit is a pointwise right Kan extension along `f.op`. -/
private def ranIsPointwiseRightKanExtension :
    (Functor.RightExtension.mk _
      (ranCounit.{vC, vD, uC, uD, rR, m} f R N)).IsPointwiseRightKanExtension := by
  intro x
  refine {
    lift := fun c => AddCommGrpCat.ofHom
      { toFun := fun s => ⟨fun j => c.π.app j s, fun {_ _} g => ?_⟩
        map_zero' := ?_
        map_add' := ?_ }
    fac := ?_
    uniq := ?_ }
  · exact congrFun (congrArg (fun k => (k.hom : _ → _)) (c.w g)) s
  · exact Subtype.ext (funext fun _ => map_zero _)
  · exact fun _ _ => Subtype.ext (funext fun _ => map_add _ _ _)
  · intro c j
    ext s
    change c.π.app (StructuredArrow.mk (j.hom ≫ 𝟙 _)) s = c.π.app j s
    rw [Category.comp_id]
    rfl
  · intro c k hk
    ext s
    apply Subtype.ext
    funext j
    exact (ranCounit_apply.{vC, vD, uC, uD, rR, m} f R N x j
      ((ConcreteCategory.hom k) s)).symm.trans (ConcreteCategory.congr_hom (hk j) s)

/-- The underlying presheaf of abelian groups of `ranPresheaf f R N` is the right Kan extension
along `f.op` of that of `N`. -/
private lemma ranIsRightKanExtension :
    (ranPresheaf.{vC, vD, uC, uD, rR, m} f R N).presheaf.IsRightKanExtension
      (ranCounit.{vC, vD, uC, uD, rR, m} f R N) :=
  (ranIsPointwiseRightKanExtension.{vC, vD, uC, uD, rR, m} f R N).isRightKanExtension

/-- The right Kan extension of a morphism of presheaves of modules: apply the morphism to each
component of a compatible family. -/
private def ranHom {N N' : PresheafOfModules.{max uC vD m} (f.op ⋙ R)} (g : N ⟶ N') :
    ranPresheaf.{vC, vD, uC, uD, rR, m} f R N ⟶ ranPresheaf.{vC, vD, uC, uD, rR, m} f R N' where
  app x := ModuleCat.ofHom
    { toFun := fun s => ⟨fun j => g.app j.right (s.val j), by
        intro j k b
        dsimp
        change N'.map b.right (g.app j.right (s.val j)) = _
        rw [← PresheafOfModules.naturality_apply]
        exact congrArg (fun z => g.app k.right z) (s.property b)⟩
      map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)
      map_smul' := by
        intro rR s
        apply Subtype.ext
        funext j
        change g.app j.right (R.map j.hom rR • (show N.obj j.right from s.val j)) =
          R.map j.hom rR • (g.app j.right (s.val j))
        exact (g.app j.right).hom.map_smul _ _ }
  naturality := by intros; rfl

/-- The right Kan extension along `f.op` as a functor between categories of presheaves of
modules. -/
private def ranFunctor : PresheafOfModules.{max uC vD m} (f.op ⋙ R) ⥤
    PresheafOfModules.{max uC vD m} R where
  obj := ranPresheaf.{vC, vD, uC, uD, rR, m} f R
  map := ranHom f R
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The unit of the restriction adjunction: a section of `M` is sent to the family of its
restrictions along the indexing arrows. -/
private def ranUnit : 𝟭 (PresheafOfModules.{max uC vD m} R) ⟶
    PresheafOfModules.pushforward₀ f R ⋙ ranFunctor.{vC, vD, uC, uD, rR, m} f R where
  app M :=
    { app x := ModuleCat.ofHom
        { toFun := fun t => ⟨fun j => M.map j.hom t, by
            intro j k g
            change M.map (f.op.map g.right) (M.map j.hom t) = M.map k.hom t
            rw [← M.map_comp_apply, StructuredArrow.w g]⟩
          map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)
          map_smul' rR t := Subtype.ext (funext fun j => M.map_smul j.hom rR t) }
      naturality := by
        intro x y b
        ext t
        apply Subtype.ext
        funext j
        exact (M.map_comp_apply b j.hom t).symm }
  naturality := by
    intro M M' g
    ext x t
    apply Subtype.ext
    funext j
    exact (PresheafOfModules.naturality_apply g j.hom t).symm

/-- The counit of the restriction adjunction: the counit of `ranPresheaf`, as a morphism of
presheaves of modules. -/
private def ranModuleCounit :
    ranFunctor.{vC, vD, uC, uD, rR, m} f R ⋙ PresheafOfModules.pushforward₀ f R ⟶
      𝟭 (PresheafOfModules.{max uC vD m} (f.op ⋙ R)) where
  app N := PresheafOfModules.homMk (ranCounit.{vC, vD, uC, uD, rR, m} f R N) (by
    intro x rR s
    change R.map (𝟙 (f.op.obj x)) rR • s.val (StructuredArrow.mk (𝟙 _)) =
      rR • s.val (StructuredArrow.mk (𝟙 _))
    rw [R.map_id]
    rfl)
  naturality := by intros; rfl

/-- Restriction of presheaves of modules along `f` is left adjoint to the right Kan extension
along `f.op`. -/
private def ranAdjunction : PresheafOfModules.pushforward₀ f R ⊣
    ranFunctor.{vC, vD, uC, uD, rR, m} f R where
  unit := ranUnit.{vC, vD, uC, uD, rR, m} f R
  counit := ranModuleCounit.{vC, vD, uC, uD, rR, m} f R
  left_triangle_components M := by
    ext x t
    change (ModuleCat.restrictScalarsId'App (R.map (𝟙 (f.op.obj x))).hom
      (by simp) (M.obj (f.op.obj x))).inv (M.map (𝟙 (f.op.obj x)) t) = t
    rw [M.map_id]
    rfl
  right_triangle_components N := by
    ext x s
    apply Subtype.ext
    funext j
    exact ranCounit_apply.{vC, vD, uC, uD, rR, m} f R N x j s

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [f.IsContinuous J K] [f.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{max uC vD m}, f.op.HasPointwiseRightKanExtension P]
  (O : Sheaf K RingCat.{rR})

/-- The right Kan extension of a sheaf of modules along a continuous and cocontinuous functor is
again a sheaf of modules. -/
private def ranSheaf
    (N : SheafOfModules.{max uC vD m}
      ((f.sheafPushforwardContinuous RingCat.{rR} J K).obj O)) :
    SheafOfModules.{max uC vD m} O where
  val := ranPresheaf.{vC, vD, uC, uD, rR, m} f O.obj N.val
  isSheaf := by
    have h2 : (f.op.ran.obj N.val.presheaf).IsRightKanExtension
        (f.op.ranCounit.app N.val.presheaf) := inferInstance
    let e := @Functor.rightKanExtensionUnique _ _ _ _ _ _
      (ranPresheaf.{vC, vD, uC, uD, rR, m} f O.obj N.val).presheaf _ _
      (ranCounit.{vC, vD, uC, uD, rR, m} f O.obj N.val)
      (ranIsRightKanExtension.{vC, vD, uC, uD, rR, m} f O.obj N.val)
      (f.op.ran.obj N.val.presheaf) (f.op.ranCounit.app N.val.presheaf) h2
    apply (Presheaf.isSheaf_of_iso_iff (J := K) e).mpr
    exact ((f.sheafPushforwardCocontinuous AddCommGrpCat.{max uC vD m} J K).obj
      ⟨N.val.presheaf, N.isSheaf⟩).property

/-- The right Kan extension along `f` as a functor between categories of sheaves of modules. -/
private def ranSheafFunctor :
    SheafOfModules.{max uC vD m} ((f.sheafPushforwardContinuous RingCat.{rR} J K).obj O) ⥤
      SheafOfModules.{max uC vD m} O where
  obj := ranSheaf.{vC, vD, uC, uD, rR, m} f J K O
  map g := ⟨ranHom f O.obj g.val⟩
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Restriction of sheaves of modules along a continuous functor `f`: objectwise restriction of the
underlying presheaf of modules. -/
private def restrictSheaf : SheafOfModules.{max uC vD m} O ⥤
    SheafOfModules.{max uC vD m} ((f.sheafPushforwardContinuous RingCat.{rR} J K).obj O) where
  obj M :=
    { val := (PresheafOfModules.pushforward₀ f O.obj).obj M.val
      isSheaf := ((f.sheafPushforwardContinuous AddCommGrpCat.{max uC vD m} J K).obj
        ⟨M.val.presheaf, M.isSheaf⟩).property }
  map g := ⟨(PresheafOfModules.pushforward₀ f O.obj).map g.val⟩

/-- Restriction of sheaves of modules along `f` is left adjoint to the right Kan extension
along `f`. -/
private def restrictSheafAdjunction :
    restrictSheaf.{vC, vD, uC, uD, rR, m} f J K O ⊣
      ranSheafFunctor.{vC, vD, uC, uD, rR, m} f J K O where
  unit :=
    { app M := ⟨(ranUnit.{vC, vD, uC, uD, rR, m} f O.obj).app M.val⟩
      naturality _ _ g :=
        SheafOfModules.hom_ext ((ranUnit.{vC, vD, uC, uD, rR, m} f O.obj).naturality g.val) }
  counit :=
    { app N := ⟨(ranModuleCounit.{vC, vD, uC, uD, rR, m} f O.obj).app N.val⟩
      naturality := by intros; rfl }
  left_triangle_components M := SheafOfModules.hom_ext
    ((ranAdjunction.{vC, vD, uC, uD, rR, m} f O.obj).left_triangle_components M.val)
  right_triangle_components N := SheafOfModules.hom_ext
    ((ranAdjunction.{vC, vD, uC, uD, rR, m} f O.obj).right_triangle_components N.val)

end ModuleRightKan

section ModuleRestriction

universe v m u' v'

variable {C : Type u} [Category.{v} C]

/-- Presheaves of modules over `R` are the sheaves of modules over `R` for the trivial topology,
for which every presheaf is a sheaf. -/
private def modulesBotEquivalence (R : Cᵒᵖ ⥤ RingCat.{r}) :
    PresheafOfModules.{m} R ≌ SheafOfModules.{m}
      (⟨R, Presheaf.isSheaf_bot R⟩ : Sheaf ⊥ RingCat.{r}) where
  functor :=
    { obj M := ⟨M, Presheaf.isSheaf_bot _⟩
      map f := ⟨f⟩ }
  inverse := SheafOfModules.forget _
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (fun M =>
    { hom := ⟨𝟙 M.val⟩
      inv := ⟨𝟙 M.val⟩ })

/-- Presheaves of modules over a presheaf of rings form a Grothendieck abelian category, in a
module universe containing the site and the structure rings. -/
private lemma presheafModulesGrothendieck (R : Cᵒᵖ ⥤ RingCat.{r}) :
    IsGrothendieckAbelian.{max u v r m} (PresheafOfModules.{max u v r m} R) := by
  have := Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u, v, r, max u v r m}
    (⟨R, Presheaf.isSheaf_bot R⟩ : Sheaf ⊥ RingCat.{r})
  exact IsGrothendieckAbelian.of_equivalence
    (modulesBotEquivalence.{u, r, v, max u v r m} R).symm

/-- Restriction of presheaves of modules along a morphism of presheaves of rings is a right
adjoint. -/
private lemma presheafPushforwardIsRightAdjoint
    {D : Type u'} [Category.{v'} D] (f : C ⥤ D)
    (R : Dᵒᵖ ⥤ RingCat.{r}) (S : Cᵒᵖ ⥤ RingCat.{r}) (φ : S ⟶ f.op ⋙ R) :
    (PresheafOfModules.pushforward.{max u v m u' v' r} φ).IsRightAdjoint := by
  have := presheafModulesGrothendieck.{u, r, v, max u v m u' v' r} S
  have := presheafModulesGrothendieck.{u', r, v', max u v m u' v' r} R
  let G := PresheafOfModules.pushforward.{max u v m u' v' r} φ
  let U := PresheafOfModules.toPresheaf.{max u v m u' v' r} S
  let : ReflectsLimitsOfSize.{max u v m u' v' r, max u v m u' v' r} U :=
    reflectsLimits_of_reflectsIsomorphisms
  let : PreservesLimitsOfSize.{max u v m u' v' r, max u v m u' v' r} G := by
    let : PreservesLimitsOfSize.{max u v m u' v' r, max u v m u' v' r} (G ⋙ U) :=
      preservesLimits_of_natIso (PresheafOfModules.pushforwardCompToPresheaf φ).symm
    exact preservesLimits_of_reflects_of_preserves G U
  exact isRightAdjoint_of_preservesLimits_of_isCoseparating.{max u v m u' v' r}
    (isCoseparator_coseparator _) G

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : Type vᵤ} [Category.{wᵤ} U] {X : Type vₓ} [Category.{wₓ} X]
  (q : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) (f : U ⥤ X) (τ : AlgebraicGeometry.SiteKind)
/-- The inverse image of an injective sheaf of modules along a faithful 1-morphism whose source has
equalizers is again injective. -/
lemma moduleRestriction_preservesInjectives
    (hq : q.IsFiberedInGroupoids) (hu : (f ⋙ q).IsFiberedInGroupoids)
    [f.Faithful] [HasEqualizers U]
    (I : SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) [Injective I] :
    Injective ((AlgebraicGeometry.Stack.modulePullback B S hS (f ⋙ q) q hu hq f rfl
        (B.baseTopology τ) (B.baseTopology_le_topology τ)).obj I) := by
  let := hu.isFibered
  let := hq.isFibered
  let hf := hq.isFibredOneMorphism (show f ⋙ q = f ⋙ q from rfl)
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).1
  let := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{vₓ, wₓ, max u vᵤ vₓ wᵤ wₓ a}
    (J := AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
  let := Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{vₓ, wₓ,
      max u vᵤ vₓ wᵤ wₓ a}
    (J := AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
  have hpresheaf : (PresheafOfModules.pushforward.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCoreHom B S hS (f ⋙ q) q f
      (B.baseTopology τ) hu hq rfl (B.baseTopology_le_topology τ)).hom).IsRightAdjoint :=
    presheafPushforwardIsRightAdjoint.{vᵤ, u, wᵤ, max u vᵤ vₓ wᵤ wₓ a, vₓ, wₓ} f _ _ _
  exact AlgebraicGeometry.Stack.injective_sheafOfModules_pushforward_obj.{u, vᵤ, vₓ, wᵤ, wₓ,
      max u vᵤ vₓ wᵤ wₓ a} B S hS (f ⋙ q) q f (B.baseTopology τ) hu hq rfl
    (B.baseTopology_le_topology τ) hpresheaf I
/-- The inverse image of sheaves of modules along a 1-morphism of categories fibred in groupoids is
exact. -/
lemma moduleRestriction_exact
    (hq : q.IsFiberedInGroupoids) (hu : (f ⋙ q).IsFiberedInGroupoids) :
    let F := AlgebraicGeometry.Stack.modulePullback.{u, vᵤ, wᵤ, max u vᵤ vₓ wᵤ wₓ a, vₓ, wₓ}
      B S hS (f ⋙ q) q hu hq f rfl (B.baseTopology τ) (B.baseTopology_le_topology τ)
    PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  let := hu.isFibered
  let := hq.isFibered
  let hf := hq.isFibredOneMorphism (show f ⋙ q = f ⋙ q from rfl)
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).1
  let := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{vₓ, wₓ, max u vᵤ vₓ wᵤ wₓ a}
    (J := AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
  let := Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{vₓ, wₓ,
      max u vᵤ vₓ wᵤ wₓ a}
    (J := AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
  let F := AlgebraicGeometry.Stack.modulePullback.{u, vᵤ, wᵤ, max u vᵤ vₓ wᵤ wₓ a, vₓ, wₓ}
    B S hS (f ⋙ q) q hu hq f rfl (B.baseTopology τ) (B.baseTopology_le_topology τ)
  let : (PresheafOfModules.pushforward.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCoreHom B S hS (f ⋙ q) q f
      (B.baseTopology τ) hu hq rfl (B.baseTopology_le_topology τ)).hom).IsRightAdjoint :=
    presheafPushforwardIsRightAdjoint.{vᵤ, u, wᵤ, max u vᵤ vₓ wᵤ wₓ a, vₓ, wₓ} f _ _ _
  let : F.IsRightAdjoint := SheafOfModules.instIsRightAdjointPushforward
    (AlgebraicGeometry.Stack.ringStructureSheafCoreHom B S hS (f ⋙ q) q f
      (B.baseTopology τ) hu hq rfl (B.baseTopology_le_topology τ))
  let : F.IsLeftAdjoint := (AlgebraicGeometry.Stack.moduleSheafFunctoriality.{u, vᵤ, wᵤ,
    max u vᵤ vₓ wᵤ wₓ a, vₓ, wₓ} B S hS (f ⋙ q) q hu hq f rfl (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).adjunction.isLeftAdjoint
  exact ⟨inferInstance, inferInstance⟩

variable {A : Type u} [Category.{v} A] [Abelian A]
  {D : Type u'} [Category.{v'} D] [Abelian D]
/-- Restriction of scalars along a ring homomorphism preserves homology. -/
lemma restrictScalars_preservesHomology
    {R : Type u} [Ring R] {S : Type u'} [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars.{m} f).PreservesHomology := by
  have h : ∀ K : ShortComplex (ModuleCat.{m} S),
      K.Exact → (K.map (ModuleCat.restrictScalars.{m} f)).Exact := by
    intro K hK
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hK ⊢
    exact hK
  have he := ((Functor.exact_tfae (ModuleCat.restrictScalars.{m} f)).out 2 4).mp h
  let := he.1
  let := he.2
  infer_instance

/-- The image of an injective resolution under an additive functor that preserves homology and
injective objects is an injective resolution. -/
def mapInjectiveResolutionOfPreservesInjectives (F : A ⥤ D) [F.Additive]
    [F.PreservesHomology] [F.PreservesInjectiveObjects]
    {M : A} (I : InjectiveResolution M) : InjectiveResolution (F.obj M) where
  cocomplex := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective n := F.injective_obj (I.cocomplex.X n)
  ι := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv.app M ≫
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι

end ModuleRestriction

end Stacks.RelativeCech

end
