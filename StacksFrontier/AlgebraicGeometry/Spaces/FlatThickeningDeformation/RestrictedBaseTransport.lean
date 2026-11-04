module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.FibreSolution
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.SolutionSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealPowerFactorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageCompAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedFirstOrderExtension
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientRealization
public import StacksFrontier.CategoryTheory.Adjunction.UniversalArrowTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint

/-!
# The extension problem of a first order thickening, read on a space isomorphic to its base

Let `Z ⊂ Y'` be a first order thickening of algebraic spaces, `ρ : Y₀ ≅ Z` an isomorphism of
algebraic spaces and `t : X ⟶ Y₀`. Besides the extension problem
`AlgebraicGeometry.Space.FlatThickeningDeformation.problem` of `t ≫ ρ : X ⟶ Z` (Stacks 08UF,
posed over the small étale ringed topos of `Z`), there is the same problem posed over the small
étale ringed topos of `Y₀`: its lower row is the inverse image along `t` of the extension
`0 → 𝒞_{Z/Y'} → ι⁻¹𝒪_{Y'} → 𝒪_Z → 0` restricted to `Y₀` along `ρ`
(`AlgebraicGeometry.Space.restrictedFirstOrderExtension`), its prescribed module is
`t^*ρ^*𝒞_{Z/Y'}` and its prescribed map is the unit of extension of scalars
(`AlgebraicGeometry.Space.FlatThickeningDeformation.restrictedProblem`). This is the problem of
the body of the proof of [Stacks Project, Tag 0D3X], where `Y₀ = Spec(R₀)` and `Z` is its range in
`Spec(lim Rₙ)`.

This file carries a solution of the second problem to a solution of the first, with the same
thickened structure sheaf, along the identification `(t ≫ ρ)⁻¹ ≅ t⁻¹ρ^*` of inverse images
(Stacks 03G8 and Stacks 03LV).

## Main definitions

* `AlgebraicGeometry.Space.FlatThickeningDeformation.restrictedProblem`: the second problem.
* `AlgebraicGeometry.Space.FlatThickeningDeformation.restrictedRingIso`:
  `(t ≫ ρ)⁻¹𝒜 ≅ t⁻¹ρ^*𝒜`.
* `AlgebraicGeometry.Space.FlatThickeningDeformation.solutionOfRestricted`: the transported
  solution.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

/-- An equation `f ≫ g = f' ≫ g'` of maps of sheaves holds sectionwise. -/
private theorem sheaf_comp_apply_eq {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {D : Type*} [Category D] {J : GrothendieckTopology D} {F G G' H : Sheaf J C}
    {f : F ⟶ G} {g : G ⟶ H} {f' : F ⟶ G'} {g' : G' ⟶ H} (h : f ≫ g = f' ≫ g') (U : Dᵒᵖ)
    (a : CC (F.obj.obj U)) : g.hom.app U (f.hom.app U a) = g'.hom.app U (f'.hom.app U a) := by
  simpa using ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app U) h) a

namespace SheafOfModules.SameSite

/-! ### Ideal lifts and restriction of scalars on a single site

The statements of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardIdealLift` with the
functor of sites the identity, stated with the target a restriction of scalars, so that no
unfolding of the identity pushforward is needed: given maps `φA : A₁ ⟶ A₀` and `φR : R₁ ⟶ R₀` of
sheaves of rings compatible with `π₁` and `π₀`, and a sectionwise map `e : I₁ → I₀` compatible
with the inclusions `ι₁` and `ι₀` into `A₁` and `A₀`, with `ι₀` injective, `e` is a map
`I₁ ⟶ φR^*I₀` of sheaves of `R₁`-modules. -/

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  {A₁ R₁ A₀ R₀ : Sheaf J RingCat.{u}} {π₁ : A₁ ⟶ R₁} {π₀ : A₀ ⟶ R₀}
  {I₁ : SheafOfModules.{u} R₁} {I₀ : SheafOfModules.{u} R₀}
  {ι₁ : (restrictScalars π₁).obj I₁ ⟶ unit A₁} {ι₀ : (restrictScalars π₀).obj I₀ ⟶ unit A₀}
  {φA : A₁ ⟶ A₀} (φR : R₁ ⟶ R₀) {e : ∀ U : Cᵒᵖ, I₁.val.obj U → I₀.val.obj U}
  (he : ∀ (U : Cᵒᵖ) (m : I₁.val.obj U),
    (show A₀.obj.obj U from ι₀.val.app U (e U m)) =
      φA.hom.app U (show A₁.obj.obj U from ι₁.val.app U m))
  (hinj : ∀ V : Cᵒᵖ, Function.Injective (ι₀.val.app V))
  (comm : π₁ ≫ φR = φA ≫ π₀)

include he hinj

/-- The sectionwise map `e` commutes with the restriction maps of `I₁` and `I₀`. -/
theorem lift_naturality {U U' : Cᵒᵖ} (p : U ⟶ U') (m : I₁.val.obj U) :
    e U' (I₁.val.map p m) = I₀.val.map p (e U m) := by
  apply hinj
  have n1 : (show A₁.obj.obj U' from ι₁.val.app U' (I₁.val.map p m)) =
      A₁.obj.map p (show A₁.obj.obj U from ι₁.val.app U m) :=
    PresheafOfModules.naturality_apply ι₁.val p m
  have n0 : (show A₀.obj.obj U' from ι₀.val.app U' (I₀.val.map p (e U m))) =
      A₀.obj.map p (show A₀.obj.obj U from ι₀.val.app U (e U m)) :=
    PresheafOfModules.naturality_apply ι₀.val p (e U m)
  have nA : φA.hom.app U' (A₁.obj.map p (show A₁.obj.obj U from ι₁.val.app U m)) =
      A₀.obj.map p (φA.hom.app U (show A₁.obj.obj U from ι₁.val.app U m)) :=
    ConcreteCategory.congr_hom (φA.hom.naturality p) _
  show (show A₀.obj.obj U' from ι₀.val.app U' (e U' (I₁.val.map p m))) =
    (show A₀.obj.obj U' from ι₀.val.app U' (I₀.val.map p (e U m)))
  rw [he U' (I₁.val.map p m), n1, nA, n0, he U m]

include comm in
/-- The sectionwise map `e` is semilinear: `e (π₁ a • m) = φR (π₁ a) • e m`. -/
theorem lift_map_smul (U : Cᵒᵖ) (a : A₁.obj.obj U) (m : I₁.val.obj U) :
    e U (π₁.hom.app U a • m) = (show R₀.obj.obj U from φR.hom.app U (π₁.hom.app U a)) • e U m := by
  apply hinj
  have hc := sheaf_comp_apply_eq comm U a
  have s1 : (show A₁.obj.obj U from ι₁.val.app U (π₁.hom.app U a • m)) =
      a * (show A₁.obj.obj U from ι₁.val.app U m) :=
    (ι₁.val.app U).hom.map_smul a m
  have s0 : (show A₀.obj.obj U from ι₀.val.app U (π₀.hom.app U (φA.hom.app U a) • e U m)) =
      (show A₀.obj.obj U from φA.hom.app U a) *
        (show A₀.obj.obj U from ι₀.val.app U (e U m)) :=
    (ι₀.val.app U).hom.map_smul (φA.hom.app U a) (e U m)
  show (show A₀.obj.obj U from ι₀.val.app U (e U (π₁.hom.app U a • m))) =
    (show A₀.obj.obj U from ι₀.val.app U
      ((show R₀.obj.obj U from φR.hom.app U (π₁.hom.app U a)) • e U m))
  rw [hc, he U (π₁.hom.app U a • m), s0, s1, _root_.map_mul, he U m]

include comm in
/-- If `φA` and `φR` are isomorphisms, `ι₁` is injective, `ι₀` lands in the kernel of `π₀` and
every section of `A₁` killed by `π₁` lies in the image of `ι₁`, then each `e U` is bijective. -/
theorem lift_bijective [IsIso φA] [IsIso φR]
    (hinj₁ : ∀ U : Cᵒᵖ, Function.Injective (ι₁.val.app U))
    (hzero : ∀ (V : Cᵒᵖ) (n : I₀.val.obj V),
      π₀.hom.app V (show A₀.obj.obj V from ι₀.val.app V n) = 0)
    (huniv : ∀ (U : Cᵒᵖ) (a : A₁.obj.obj U), π₁.hom.app U a = 0 →
      ∃ m : I₁.val.obj U, (show A₁.obj.obj U from ι₁.val.app U m) = a)
    (U : Cᵒᵖ) : Function.Bijective (e U) := by
  refine ⟨fun m m' h => ?_, fun n => ?_⟩
  · apply hinj₁ U
    apply (SheafOfModules.bijective_hom_app_of_isIso φA U).1
    show φA.hom.app U (show A₁.obj.obj U from ι₁.val.app U m) =
      φA.hom.app U (show A₁.obj.obj U from ι₁.val.app U m')
    rw [← he U m, ← he U m', h]
  · obtain ⟨a, ha⟩ := (SheafOfModules.bijective_hom_app_of_isIso φA U).2
      (show A₀.obj.obj U from ι₀.val.app U n)
    have hc := sheaf_comp_apply_eq comm U a
    have h0 : π₁.hom.app U a = 0 := by
      apply (SheafOfModules.bijective_hom_app_of_isIso φR U).1
      show (show R₀.obj.obj U from φR.hom.app U (π₁.hom.app U a)) =
        (show R₀.obj.obj U from φR.hom.app U 0)
      rw [hc, _root_.map_zero, ha]
      exact hzero _ n
    obtain ⟨m, hm⟩ := huniv U a h0
    refine ⟨m, hinj _ ?_⟩
    show (show A₀.obj.obj U from ι₀.val.app U (e U m)) =
      (show A₀.obj.obj U from ι₀.val.app U n)
    rw [he U m, hm, ha]

variable (hls : Presheaf.IsLocallySurjective J π₁.hom)

/-- **The lift `I₁ ⟶ φR^*I₀` of a compatible map of ambient sheaves of rings**, sectionwise `e`. -/
def lift : I₁ ⟶ (restrictScalars φR).obj I₀ :=
  haveI := hls
  ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective (J := J) (α := π₁.hom)
      ((restrictScalars φR).obj I₀).isSheaf).symm
    (PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk' (e U) fun m m' => by
          apply hinj
          have a1 : (show A₁.obj.obj U from ι₁.val.app U (m + m')) =
              (show A₁.obj.obj U from ι₁.val.app U m) +
                (show A₁.obj.obj U from ι₁.val.app U m') :=
            (ι₁.val.app U).hom.map_add m m'
          have a0 : (show A₀.obj.obj U from ι₀.val.app U (e U m + e U m')) =
              (show A₀.obj.obj U from ι₀.val.app U (e U m)) +
                (show A₀.obj.obj U from ι₀.val.app U (e U m')) :=
            (ι₀.val.app U).hom.map_add (e U m) (e U m')
          change (show A₀.obj.obj U from ι₀.val.app U (e U (m + m'))) =
            (show A₀.obj.obj U from ι₀.val.app U (e U m + e U m'))
          rw [he U (m + m'), a0, he U m, he U m', a1]
          exact _root_.map_add _ _ _)
        naturality U U' p := by
          ext m
          exact lift_naturality he hinj p m }
      (fun U a m => lift_map_smul φR he hinj comm U a m))⟩

/-- On sections, `lift` is `e`. -/
theorem lift_val_app (U : Cᵒᵖ) (m : I₁.val.obj U) :
    (lift φR he hinj comm hls).val.app U m =
      (show ((restrictScalars φR).obj I₀).val.obj U from e U m) :=
  rfl

end SheafOfModules.SameSite

namespace SheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R₁ R₀ O : Sheaf J RingCat.{u}}

/-- **A universal arrow transported along a ring isomorphism.** If `c : I₀ ⟶ a^*G` is universal,
`σ` is an isomorphism, `b = σ ≫ a` and `d : I₁ ⟶ b^*G` is, on sections, `c` after an isomorphism
`I₁ ≅ σ^*I₀`, then `d` is universal. -/
theorem bijective_comp_map_of_val_app_eq (σ : R₁ ⟶ R₀) [IsIso σ] (a : R₀ ⟶ O) (b : R₁ ⟶ O)
    (h : b = σ ≫ a) {I₁ : SheafOfModules.{u} R₁} {I₀ : SheafOfModules.{u} R₀}
    {G : SheafOfModules.{u} O} (c : I₀ ⟶ (restrictScalars.{u} a).obj G)
    (hc : ∀ M : SheafOfModules.{u} O,
      Function.Bijective fun k : G ⟶ M => c ≫ (restrictScalars.{u} a).map k)
    (e : I₁ ≅ (restrictScalars.{u} σ).obj I₀) (d : I₁ ⟶ (restrictScalars.{u} b).obj G)
    (hd : ∀ (U : Cᵒᵖ) (x : I₁.val.obj U),
      d.val.app U x = c.val.app U (e.hom.val.app U x))
    (M : SheafOfModules.{u} O) :
    Function.Bijective fun k : G ⟶ M => d ≫ (restrictScalars.{u} b).map k := by
  subst h
  have hd' : d = e.hom ≫ (restrictScalars.{u} σ).map c :=
    SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => by ext x; exact hd U x)
  subst hd'
  have hΨ : (restrictScalars.{u} σ).FullyFaithful :=
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso (asIso σ).symm).fullyFaithfulFunctor
  have he : (fun k : G ⟶ M => ((e.hom ≫ (restrictScalars.{u} σ).map c) ≫
      (restrictScalars.{u} (σ ≫ a)).map k : I₁ ⟶
        (restrictScalars.{u} σ).obj ((restrictScalars.{u} a).obj M))) =
      ((fun y => e.hom ≫ y) ∘ (restrictScalars.{u} σ).map) ∘
        fun k : G ⟶ M => c ≫ (restrictScalars.{u} a).map k := by
    funext k
    simp only [Function.comp_apply, Functor.map_comp]
    rfl
  show Function.Bijective (fun k : G ⟶ M => ((e.hom ≫ (restrictScalars.{u} σ).map c) ≫
      (restrictScalars.{u} (σ ≫ a)).map k : I₁ ⟶
        (restrictScalars.{u} σ).obj ((restrictScalars.{u} a).obj M)))
  rw [he]
  refine Function.Bijective.comp (Function.Bijective.comp ?_ (hΨ.map_bijective _ _)) (hc M)
  exact Function.bijective_iff_has_inverse.2 ⟨fun y => e.inv ≫ y, fun y => by simp,
    fun y => by simp⟩

end SheafOfModules

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1)
  {Y₀ X : AlgebraicSpaces B S hS} (ρ : Y₀ ≅ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (t : X ⟶ Y₀)

/-- **The extension problem of `t` over the restriction of the thickening `Z ⊂ Y'` to `Y₀`**:
the lower row is the inverse image along `t` of the restricted extension
`0 → ρ^*𝒞_{Z/Y'} → ρ^*ι⁻¹𝒪_{Y'} → 𝒪_{Y₀} → 0`, the prescribed module is `t^*ρ^*𝒞_{Z/Y'}`, and the
prescribed map is the unit of extension of scalars along `t^♯`. -/
def restrictedProblem :
    Deformation.ToposThickening.RingedToposExtensionProblem (smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedTopos B S hS Y₀) :=
  Deformation.ToposThickening.RingedToposExtensionProblem.ofBaseAlgebraExtension
    (X := smallEtaleRingedTopos B S hS X) (D := smallEtaleRingedTopos B S hS Y₀)
    (smallEtaleRingedToposHom B S hS t)
    (restrictedFirstOrderExtension B S hS Z hZ ρ (𝟙 Y'))
    ((modulePullback B S hS t).obj (restrictedConormalModule B S hS Z ρ))
    ((extendScalarsFSharpAdjunction B S hS t).unit.app _)

/-- Postcomposition with `ρ` is continuous (Stacks 03LP), stated at the two small étale sites for
instance search. -/
theorem restrictedPostcomp_isContinuous :
    (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).IsContinuous
      (SmallEtale.topology B S hS Y₀.1)
      (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) :=
  smallEtalePostcomp_isContinuous B S hS _ _

attribute [local instance] restrictedPostcomp_isContinuous

/-- Restriction along `ρ` of sheaves of commutative rings on the small étale site of `Z`. -/
abbrev restrictedRingRes :=
  Deformation.AlgebraExtension.ringRes
    (J := SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
    (SmallEtale.topology B S hS Y₀.1)
    (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))

/-- The inverse image along the étale `ρ` is restriction along `ρ` (Stacks 03LV). -/
def restrictionRingIso
    (A : Sheaf (SmallEtale.topology B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) CommRingCat.{u}) :
    (smallEtaleInverseImageRing B S hS ρ.hom).obj A ≅ (restrictedRingRes ρ).obj A :=
  inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS Y₀.1)
    (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
    (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
    (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom
    (smallToposMorphismTypeU_inverseImageIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)) A

/-- `restrictionRingIso ρ` is natural in the sheaf of commutative rings. -/
theorem restrictionRingIso_naturality
    {A A' : Sheaf (SmallEtale.topology B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) CommRingCat.{u}} (m : A ⟶ A') :
    (smallEtaleInverseImageRing B S hS ρ.hom).map m ≫ (restrictionRingIso ρ A').hom =
      (restrictionRingIso ρ A).hom ≫ (restrictedRingRes ρ).map m :=
  inverseImageCommRingRestrictionIso_naturality (SmallEtale.topology B S hS Y₀.1)
    (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
    (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
    (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom
    (smallToposMorphismTypeU_inverseImageIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)) m

/-- **`(t ≫ ρ)⁻¹𝒜 ≅ t⁻¹ρ^*𝒜`**, the composition law of Stacks 03G8 followed by `t⁻¹` of the
identification of the inverse image along the étale `ρ` with restriction (Stacks 03LV). -/
def restrictedRingIso
    (A : Sheaf (SmallEtale.topology B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) CommRingCat.{u}) :
    (smallEtaleInverseImageRing B S hS (t ≫ ρ.hom)).obj A ≅
      (smallEtaleInverseImageRing B S hS t).obj ((restrictedRingRes ρ).obj A) :=
  ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS t ρ.hom).app A).symm ≪≫
    (smallEtaleInverseImageRing B S hS t).mapIso (restrictionRingIso ρ A)

/-- `restrictedRingIso ρ t` is natural in the sheaf of commutative rings. -/
theorem restrictedRingIso_naturality
    {A A' : Sheaf (SmallEtale.topology B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) CommRingCat.{u}} (m : A ⟶ A') :
    (smallEtaleInverseImageRing B S hS (t ≫ ρ.hom)).map m ≫ (restrictedRingIso ρ t A').hom =
      (restrictedRingIso ρ t A).hom ≫
        (smallEtaleInverseImageRing B S hS t).map ((restrictedRingRes ρ).map m) := by
  have hc := (smallEtaleRingedToposHom_compInverseImageRingIso B S hS t ρ.hom).inv.naturality m
  have hn := congrArg (smallEtaleInverseImageRing B S hS t).map (restrictionRingIso_naturality ρ m)
  simp only [Functor.map_comp] at hn
  simp only [restrictedRingIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.comp_map] at hc ⊢
  rw [← Category.assoc, hc, Category.assoc, hn, Category.assoc]

/-- **`(t ≫ ρ)⁻¹𝒪_Z ≅ t⁻¹𝒪_{Y₀}`**: the composition law of Stacks 03G8 followed by `t⁻¹ρ^♯`, the
structure map of the étale `ρ` being invertible (Stacks 03LV). -/
def restrictedReducedIso :
    (smallEtaleInverseImageRing B S hS (t ≫ ρ.hom)).obj (smallEtaleRingedTopos B S hS _).O ≅
      (smallEtaleInverseImageRing B S hS t).obj (smallEtaleRingedTopos B S hS Y₀).O :=
  ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS t ρ.hom).app _).symm ≪≫
    (smallEtaleInverseImageRing B S hS t).mapIso
      (etaleInverseImageStructureSheafIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))

/-- The structure map of `t ≫ ρ` is `(t ≫ ρ)⁻¹𝒪_Z ≅ t⁻¹𝒪_{Y₀}` followed by that of `t`. -/
theorem fSharp_comp_eq :
    (smallEtaleRingedToposHom B S hS (t ≫ ρ.hom)).fSharpInverseImage =
      (restrictedReducedIso ρ t).hom ≫ (smallEtaleRingedToposHom B S hS t).fSharpInverseImage := by
  have h := smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS t ρ.hom
  calc (smallEtaleRingedToposHom B S hS (t ≫ ρ.hom)).fSharpInverseImage
      = (smallEtaleRingedToposHom_compInverseImageRingIso B S hS t ρ.hom).inv.app _ ≫
          (smallEtaleRingedToposHom_compInverseImageRingIso B S hS t ρ.hom).hom.app _ ≫
          (smallEtaleRingedToposHom B S hS (t ≫ ρ.hom)).fSharpInverseImage :=
        (Iso.inv_hom_id_app_assoc _ _ _).symm
    _ = (smallEtaleRingedToposHom_compInverseImageRingIso B S hS t ρ.hom).inv.app _ ≫
          (smallEtaleInverseImageRing B S hS t).map
            (smallEtaleRingedToposHom B S hS ρ.hom).fSharpInverseImage ≫
          (smallEtaleRingedToposHom B S hS t).fSharpInverseImage := by rw [h]
    _ = _ := (Category.assoc _ _ _).symm

/-! ### The thickened bases of the two problems -/

/-- `(t ≫ ρ)⁻¹(ι⁻¹𝒪_{Y'}) ≅ t⁻¹ρ^*(ι⁻¹𝒪_{Y'})`, in the spelling of the two problems. -/
def restrictedTheta :
    (inverseImageCommRingFunctor (restrictedProblem hZ ρ t).f.toToposHom).obj
        (restrictedProblem hZ ρ t).baseExtension ≅
      (inverseImageCommRingFunctor (problem (t ≫ ρ.hom) hZ).f.toToposHom).obj
        (problem (t ≫ ρ.hom) hZ).baseExtension :=
  (restrictedRingIso ρ t (baseExtension hZ).extension).symm

/-- The identification of the thickened bases is compatible with the reductions to the reduced
bases, `(t ≫ ρ)⁻¹𝒪_Z ≅ t⁻¹𝒪_{Y₀}` on the latter. -/
theorem restrictedRingIso_comm :
    (smallEtaleInverseImageRing B S hS (t ≫ ρ.hom)).map (baseExtension hZ).reduction ≫
        (restrictedReducedIso ρ t).hom =
      (restrictedRingIso ρ t (baseExtension hZ).extension).hom ≫
        (smallEtaleInverseImageRing B S hS t).map
          (restrictedFirstOrderExtension B S hS Z hZ ρ (𝟙 Y')).reduction := by
  have hn := restrictedRingIso_naturality ρ t (baseExtension hZ).reduction
  have hω : (restrictionRingIso ρ (smallEtaleRingedTopos B S hS _).O).hom ≫
      (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)
        (subspaceInclusion B S hS Y' Z)).ω.inv =
      (smallEtaleRingedToposHom B S hS ρ.hom).fSharpInverseImage :=
    Iso.hom_inv_id_assoc _ _
  calc (smallEtaleInverseImageRing B S hS (t ≫ ρ.hom)).map (baseExtension hZ).reduction ≫
        (restrictedReducedIso ρ t).hom
      = (smallEtaleInverseImageRing B S hS (t ≫ ρ.hom)).map (baseExtension hZ).reduction ≫
          (restrictedRingIso ρ t (smallEtaleRingedTopos B S hS _).O).hom ≫
          (smallEtaleInverseImageRing B S hS t).map
            (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)
              (subspaceInclusion B S hS Y' Z)).ω.inv := by
        congr 1
        refine (congrArg (_ ≫ ·) ((congrArg (smallEtaleInverseImageRing B S hS t).map hω.symm).trans
          ((smallEtaleInverseImageRing B S hS t).map_comp _ _))).trans ?_
        exact (Category.assoc _ _ _).symm
    _ = (restrictedRingIso ρ t (baseExtension hZ).extension).hom ≫
          (smallEtaleInverseImageRing B S hS t).map ((restrictedRingRes ρ).map
            (baseExtension hZ).reduction) ≫
          (smallEtaleInverseImageRing B S hS t).map
            (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)
              (subspaceInclusion B S hS Y' Z)).ω.inv := by
        rw [← Category.assoc, hn, Category.assoc]
    _ = _ := congrArg (_ ≫ ·) ((smallEtaleInverseImageRing B S hS t).map_comp _ _).symm

/-- `restrictedTheta` commutes with the reductions of the thickened bases followed by the
structure maps of the two problems. -/
theorem restrictedTheta_comp :
    (restrictedTheta hZ ρ t).hom ≫
        (inverseImageCommRingFunctor (problem (t ≫ ρ.hom) hZ).f.toToposHom).map
          (problem (t ≫ ρ.hom) hZ).baseReduction ≫
        (problem (t ≫ ρ.hom) hZ).f.fSharpInverseImage =
      (inverseImageCommRingFunctor (restrictedProblem hZ ρ t).f.toToposHom).map
          (restrictedProblem hZ ρ t).baseReduction ≫
        (restrictedProblem hZ ρ t).f.fSharpInverseImage := by
  show (restrictedRingIso ρ t (baseExtension hZ).extension).inv ≫
      (smallEtaleInverseImageRing B S hS (t ≫ ρ.hom)).map (baseExtension hZ).reduction ≫
        (smallEtaleRingedToposHom B S hS (t ≫ ρ.hom)).fSharpInverseImage = _
  rw [fSharp_comp_eq, ← Category.assoc ((smallEtaleInverseImageRing B S hS _).map _),
    restrictedRingIso_comm, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-! ### The base ideals of the two problems -/

/-- The reduction of the thickened base of the restricted problem kills the image of a section
of the base ideal of `problem (t ≫ ρ)` under `(t ≫ ρ)⁻¹ ≅ t⁻¹ρ^*`. -/
theorem restrictedIdeal_reduction (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (problem (t ≫ ρ.hom) hZ).I.val.obj U) :
    ((inverseImageCommRingFunctor (restrictedProblem hZ ρ t).f.toToposHom).map
        (restrictedProblem hZ ρ t).baseReduction).hom.app U
      ((restrictedRingIso ρ t (baseExtension hZ).extension).hom.hom.app U
        ((problem (t ≫ ρ.hom) hZ).idealInclusion.val.app U x)) = 0 := by
  have hc := sheaf_comp_apply_eq (restrictedRingIso_comm hZ ρ t) U
    ((problem (t ≫ ρ.hom) hZ).idealInclusion.val.app U x)
  refine hc.symm.trans ?_
  show (restrictedReducedIso ρ t).hom.hom.app U
    (((smallEtaleInverseImageRing B S hS (t ≫ ρ.hom)).map (baseExtension hZ).reduction).hom.app U
      ((problem (t ≫ ρ.hom) hZ).idealInclusion.val.app U x)) = 0
  rw [show ((smallEtaleInverseImageRing B S hS (t ≫ ρ.hom)).map
      (baseExtension hZ).reduction).hom.app U
      ((problem (t ≫ ρ.hom) hZ).idealInclusion.val.app U x) = 0 from
        (problem (t ≫ ρ.hom) hZ).idealZero U x, map_zero]

/-- The section of the base ideal of the restricted problem with the same image as a section of
the base ideal of `problem (t ≫ ρ)`. -/
def restrictedIdealApp (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (problem (t ≫ ρ.hom) hZ).I.val.obj U) : (restrictedProblem hZ ρ t).I.val.obj U :=
  ((restrictedProblem hZ ρ t).idealUniversal U _
    (restrictedIdeal_reduction hZ ρ t U x)).exists.choose

/-- The image of `restrictedIdealApp x` in the thickened base of the restricted problem is the
image of `x` under `(t ≫ ρ)⁻¹ ≅ t⁻¹ρ^*`. -/
theorem incl_restrictedIdealApp (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (problem (t ≫ ρ.hom) hZ).I.val.obj U) :
    (show ((inverseImageCommRingFunctor (restrictedProblem hZ ρ t).f.toToposHom).obj
        (restrictedProblem hZ ρ t).baseExtension).obj.obj U from
      (restrictedProblem hZ ρ t).idealInclusion.val.app U (restrictedIdealApp hZ ρ t U x)) =
      (restrictedRingIso ρ t (baseExtension hZ).extension).hom.hom.app U
        ((problem (t ≫ ρ.hom) hZ).idealInclusion.val.app U x) :=
  ((restrictedProblem hZ ρ t).idealUniversal U _
    (restrictedIdeal_reduction hZ ρ t U x)).exists.choose_spec

/-- `(t ≫ ρ)⁻¹𝒪_Z ≅ t⁻¹𝒪_{Y₀}` as an isomorphism of sheaves of rings. -/
abbrev restrictedReducedRingIso :=
  (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
    (restrictedReducedIso ρ t)

/-- Restriction of scalars along `(t ≫ ρ)⁻¹𝒪_Z ≅ t⁻¹𝒪_{Y₀}`. -/
abbrev restrictedScalarRes :=
  SheafOfModules.restrictScalars.{u} (restrictedReducedRingIso ρ t).hom

/-- Restriction of scalars along an isomorphism is fully faithful. -/
def restrictedScalarResFullyFaithful : (restrictedScalarRes ρ t).FullyFaithful :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (restrictedReducedRingIso ρ t).symm).fullyFaithfulFunctor

/-- `restrictedRingIso_comm` as an equality of maps of sheaves of rings. -/
theorem restrictedMaps_comm' :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((inverseImageCommRingFunctor (problem (t ≫ ρ.hom) hZ).f.toToposHom).map
          (problem (t ≫ ρ.hom) hZ).baseReduction) ≫ (restrictedReducedRingIso ρ t).hom =
      (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (restrictedRingIso ρ t (baseExtension hZ).extension).hom ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
          ((inverseImageCommRingFunctor (restrictedProblem hZ ρ t).f.toToposHom).map
            (restrictedProblem hZ ρ t).baseReduction) := by
  have h := congrArg
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
    (restrictedRingIso_comm hZ ρ t)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

/-- The inclusion of the base ideal of the restricted problem into its thickened base is
injective on sections. -/
theorem injective_restrictedIdealInclusion (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Injective ((restrictedProblem hZ ρ t).idealInclusion.val.app V) := fun a _ h =>
  ((restrictedProblem hZ ρ t).idealUniversal V _
    ((restrictedProblem hZ ρ t).idealZero V a)).unique rfl h.symm

/-- The inverse image of the reduction of the thickened base of `problem (t ≫ ρ)` is locally
surjective. -/
instance isLocallySurjective_problem_comp_baseReduction :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (problem (t ≫ ρ.hom) hZ).baseReductionInverseImagePresheafHom :=
  isLocallySurjective_forget_inverseImage_baseReduction hZ (t ≫ ρ.hom)

/-- The inverse image of the reduction of the thickened base of `problem (t ≫ ρ)`, as a map of
sheaves of rings, is locally surjective. -/
theorem isLocallySurjective_restrictedBaseReduction :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((sheafCompose (smallEtaleRingedTopos B S hS X).J (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((inverseImageCommRingFunctor (problem (t ≫ ρ.hom) hZ).f.toToposHom).map
          (problem (t ≫ ρ.hom) hZ).baseReduction)).hom :=
  isLocallySurjective_forget_inverseImage_baseReduction hZ (t ≫ ρ.hom)

/-- **The base ideal of `problem (t ≫ ρ)` is the base ideal of the restricted problem**, as
modules over `(t ≫ ρ)⁻¹𝒪_Z ≅ t⁻¹𝒪_{Y₀}`: sectionwise `restrictedIdealApp`, which is linear
because it is semilinear over the thickened bases and their reductions are locally surjective. -/
def restrictedIdealLift :
    (problem (t ≫ ρ.hom) hZ).I ⟶ (restrictedScalarRes ρ t).obj (restrictedProblem hZ ρ t).I :=
  SheafOfModules.SameSite.lift (φA := (sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        (restrictedRingIso ρ t (baseExtension hZ).extension).hom)
      (restrictedReducedRingIso ρ t).hom
    (incl_restrictedIdealApp hZ ρ t) (injective_restrictedIdealInclusion hZ ρ t)
    (restrictedMaps_comm' hZ ρ t) (isLocallySurjective_restrictedBaseReduction hZ ρ t)

/-- On sections, `restrictedIdealLift` is `restrictedIdealApp`. -/
theorem restrictedIdealLift_val_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (problem (t ≫ ρ.hom) hZ).I.val.obj U) :
    (restrictedIdealLift hZ ρ t).val.app U x = restrictedIdealApp hZ ρ t U x :=
  rfl

/-- `restrictedIdealLift` is an isomorphism. -/
theorem isIso_restrictedIdealLift : IsIso (restrictedIdealLift hZ ρ t) :=
  have : IsIso ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        (restrictedRingIso ρ t (baseExtension hZ).extension).hom) :=
    inferInstanceAs (IsIso ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
        (restrictedRingIso ρ t (baseExtension hZ).extension)).hom)
  Stacks.SheafOfModules.isIso_of_bijective_val_app _ fun U =>
    SheafOfModules.SameSite.lift_bijective (φA := (sheafCompose (SmallEtale.topology B S hS X.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
        (restrictedRingIso ρ t (baseExtension hZ).extension).hom)
      (restrictedReducedRingIso ρ t).hom
      (incl_restrictedIdealApp hZ ρ t) (injective_restrictedIdealInclusion hZ ρ t)
      (restrictedMaps_comm' hZ ρ t) (injective_fibreIdealInclusion hZ (t ≫ ρ.hom))
      (restrictedProblem hZ ρ t).idealZero
      (fun U a ha => ((problem (t ≫ ρ.hom) hZ).idealUniversal U a ha).exists) U

/-- `restrictedIdealLift` as an isomorphism. -/
def restrictedIdealIso :
    (problem (t ≫ ρ.hom) hZ).I ≅ (restrictedScalarRes ρ t).obj (restrictedProblem hZ ρ t).I :=
  @asIso _ _ _ _ (restrictedIdealLift hZ ρ t) (isIso_restrictedIdealLift hZ ρ t)

/-! ### The transported solution -/

variable (P : (restrictedProblem hZ ρ t).CompatibleFirstOrderThickening)

/-- A solution of the restricted problem, as an extension of `t⁻¹ρ^*ι⁻¹𝒪_{Y'}`-algebras. -/
abbrev restrictedQ :=
  (restrictedProblem hZ ρ t).toAlgebraExtension (Iso.refl _) (Category.id_comp _) P

/-- The map `(t ≫ ρ)⁻¹𝒞_{Z/Y'} ⟶ t^*ρ^*𝒞_{Z/Y'}` by which a solution of the restricted problem
carries the base ideal of `problem (t ≫ ρ)`. -/
abbrev restrictedIdealMap :=
  (problem (t ≫ ρ.hom) hZ).idealMap (restrictedTheta hZ ρ t) (restrictedTheta_comp hZ ρ t)
    (restrictedQ hZ ρ t P)

/-- The structure map of `problem (t ≫ ρ)`, as a map of sheaves of rings, is
`(t ≫ ρ)⁻¹𝒪_Z ≅ t⁻¹𝒪_{Y₀}` followed by that of the restricted problem. -/
theorem forget_fSharp_comp_eq :
    (sheafCompose (smallEtaleRingedTopos B S hS X).J (forget₂ CommRingCat.{u} RingCat.{u})).map
        (problem (t ≫ ρ.hom) hZ).f.fSharpInverseImage =
      (restrictedReducedRingIso ρ t).hom ≫
        (sheafCompose (smallEtaleRingedTopos B S hS X).J (forget₂ CommRingCat.{u} RingCat.{u})).map
          (restrictedProblem hZ ρ t).f.fSharpInverseImage :=
  (congrArg (sheafCompose (smallEtaleRingedTopos B S hS X).J
    (forget₂ CommRingCat.{u} RingCat.{u})).map (fSharp_comp_eq ρ t)).trans
    ((sheafCompose (smallEtaleRingedTopos B S hS X).J
      (forget₂ CommRingCat.{u} RingCat.{u})).map_comp _ _)

/-- On sections, `restrictedIdealMap` is `restrictedIdealIso` followed by the prescribed map of
the restricted problem. -/
theorem restrictedIdealMap_val_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (problem (t ≫ ρ.hom) hZ).I.val.obj U) :
    (restrictedIdealMap hZ ρ t P).val.app U x =
      (restrictedProblem hZ ρ t).c.val.app U ((restrictedIdealIso hZ ρ t).hom.val.app U x) := by
  apply (restrictedQ hZ ρ t P).incl_injective
  refine ((problem (t ≫ ρ.hom) hZ).incl_idealMap _ _ (restrictedQ hZ ρ t P) U x).trans ?_
  have hc := (restrictedProblem hZ ρ t).isCompatible_toAlgebraExtension (Iso.refl _)
    (Category.id_comp _) P U (restrictedIdealApp hZ ρ t U x)
  refine Eq.trans ?_ hc
  show (restrictedQ hZ ρ t P).algebraMap.hom.app U
      ((restrictedRingIso ρ t (baseExtension hZ).extension).hom.hom.app U
        ((problem (t ≫ ρ.hom) hZ).idealInclusion.val.app U x)) =
    (restrictedQ hZ ρ t P).algebraMap.hom.app U
        ((restrictedProblem hZ ρ t).idealInclusion.val.app U (restrictedIdealApp hZ ρ t U x))
  exact congrArg (fun y => (restrictedQ hZ ρ t P).algebraMap.hom.app U y)
    (incl_restrictedIdealApp hZ ρ t U x).symm

/-- `restrictedIdealMap` is universal: for every module `M`, composition with it is a bijection
from maps `t^*ρ^*𝒞_{Z/Y'} ⟶ M` to maps out of the base ideal of `problem (t ≫ ρ)`. -/
theorem bijective_restrictedIdealMap
    (M : SheafOfModules.{u} ((sheafCompose (smallEtaleRingedTopos B S hS X).J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)) :
    Function.Bijective fun k : (restrictedProblem hZ ρ t).G ⟶ M =>
      restrictedIdealMap hZ ρ t P ≫ (SheafOfModules.restrictScalars
        ((sheafCompose (smallEtaleRingedTopos B S hS X).J (forget₂ CommRingCat.{u} RingCat.{u})).map
          (problem (t ≫ ρ.hom) hZ).f.fSharpInverseImage)).map k :=
  SheafOfModules.bijective_comp_map_of_val_app_eq (restrictedReducedRingIso ρ t).hom
    ((sheafCompose (smallEtaleRingedTopos B S hS X).J (forget₂ CommRingCat.{u} RingCat.{u})).map
      (restrictedProblem hZ ρ t).f.fSharpInverseImage)
    ((sheafCompose (smallEtaleRingedTopos B S hS X).J (forget₂ CommRingCat.{u} RingCat.{u})).map
      (problem (t ≫ ρ.hom) hZ).f.fSharpInverseImage) (forget_fSharp_comp_eq hZ ρ t)
    (restrictedProblem hZ ρ t).c
    ((extendScalarsFSharpAdjunction B S hS t).bijective_comp_map_unit _)
    (restrictedIdealIso hZ ρ t) (restrictedIdealMap hZ ρ t P)
    (restrictedIdealMap_val_app hZ ρ t P) M

/-- **The kernel identification** `(t ≫ ρ)^*𝒞_{Z/Y'} ⟶ t^*ρ^*𝒞_{Z/Y'}`, the adjoint of the map on
base ideals. -/
def restrictedKernelMap : (problem (t ≫ ρ.hom) hZ).G ⟶ (restrictedProblem hZ ρ t).G :=
  ((extendScalarsFSharpAdjunction B S hS (t ≫ ρ.hom)).homEquiv _ _).symm
    (restrictedIdealMap hZ ρ t P)

/-- `restrictedKernelMap` is an isomorphism. -/
instance isIso_restrictedKernelMap : IsIso (restrictedKernelMap hZ ρ t P) :=
  (extendScalarsFSharpAdjunction B S hS (t ≫ ρ.hom)).isIso_homEquiv_symm_of_bijective _
    (bijective_restrictedIdealMap hZ ρ t P)

/-- The prescribed map of `problem (t ≫ ρ)` followed by `restrictedKernelMap` is
`restrictedIdealMap`. -/
theorem problem_c_comp_restrictedKernelMap :
    (problem (t ≫ ρ.hom) hZ).c ≫ (SheafOfModules.restrictScalars
      ((sheafCompose (smallEtaleRingedTopos B S hS X).J (forget₂ CommRingCat.{u} RingCat.{u})).map
        (problem (t ≫ ρ.hom) hZ).f.fSharpInverseImage)).map (restrictedKernelMap hZ ρ t P) =
      restrictedIdealMap hZ ρ t P :=
  ((extendScalarsFSharpAdjunction B S hS (t ≫ ρ.hom)).homEquiv_unit _ _ _).symm.trans
    (((extendScalarsFSharpAdjunction B S hS (t ≫ ρ.hom)).homEquiv _ _).apply_symm_apply _)

/-- The solution, as an extension of `t⁻¹ρ^*ι⁻¹𝒪_{Y'}`-algebras with kernel `(t ≫ ρ)^*𝒞_{Z/Y'}`. -/
abbrev restrictedExtension :=
  (restrictedQ hZ ρ t P).transportKernel (asIso (restrictedKernelMap hZ ρ t P)).symm

/-- `restrictedExtension` is compatible with `restrictedTheta` and the prescribed map of
`problem (t ≫ ρ)`. -/
theorem isCompatible_restrictedExtension :
    (problem (t ≫ ρ.hom) hZ).IsCompatible (restrictedTheta hZ ρ t) (problem (t ≫ ρ.hom) hZ).c
      (restrictedExtension hZ ρ t P) := fun U x => by
  have h1 := (problem (t ≫ ρ.hom) hZ).incl_idealMap (restrictedTheta hZ ρ t)
    (restrictedTheta_comp hZ ρ t) (restrictedQ hZ ρ t P) U x
  have h3 : restrictedIdealMap hZ ρ t P = (problem (t ≫ ρ.hom) hZ).c ≫
      (SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (problem (t ≫ ρ.hom) hZ).f.fSharpInverseImage)).map
          (asIso (restrictedKernelMap hZ ρ t P)).symm.inv :=
    (problem_c_comp_restrictedKernelMap hZ ρ t P).symm
  have h4 := congrArg (fun d => d.val.app U x) h3
  have h5 := transportKernel_incl_restrictScalars (restrictedQ hZ ρ t P)
    (asIso (restrictedKernelMap hZ ρ t P)).symm (problem (t ≫ ρ.hom) hZ).c U x
  exact h1.symm.trans ((SheafOfModules.congr_restrictScalars_val _ _
    (restrictedQ hZ ρ t P).incl h4).trans h5.symm)

/-- **A solution of the restricted problem as a solution of `problem (t ≫ ρ)`**, with the same
thickened structure sheaf and reduction. -/
def solutionOfRestricted : (problem (t ≫ ρ.hom) hZ).CompatibleFirstOrderThickening :=
  (problem (t ≫ ρ.hom) hZ).ofAlgebraExtension (restrictedTheta hZ ρ t)
    (restrictedTheta_comp hZ ρ t) (restrictedExtension hZ ρ t P)
    (isCompatible_restrictedExtension hZ ρ t P)

/-! ### Realizations -/

/-- The canonical comparison of inverse images along `i ≫ g = f` is the composition law of
Stacks 03G8 read through `f = i ≫ g`. -/
theorem canonicalBaseComparison_hom_eq {X₁ Y₁ Z₁ : AlgebraicSpaces B S hS} (i : X₁ ⟶ Z₁)
    (g : Z₁ ⟶ Y₁) (f : X₁ ⟶ Y₁) (h : i ≫ g = f) :
    (canonicalBaseComparison B S hS i g f h).hom =
      eqToHom (congrArg (fun φ ↦ (smallEtaleRingedToposHom B S hS φ).toToposHom.inverseImageRing.obj
          (smallEtaleRingedTopos B S hS Y₁).O) h.symm) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS i g).inv.app
          (smallEtaleRingedTopos B S hS Y₁).O := by
  subst h
  rfl

/-- **A realization of a square-zero extension, in the form
`AlgebraicGeometry.Space.SquareZeroExtension.ToposRealization`, realizes any other square-zero
extension with the same sheaf, reduction and algebra structure**, over an equal morphism, in the
form `AlgebraicGeometry.Space.SquareZeroExtension.Realization`: the data are kept, and the
comparison of inverse images of the base is the canonical one. -/
def realizationOfEq {X₁ Y₁ : AlgebraicSpaces B S hS} {f₁ f₂ : X₁ ⟶ Y₁} (h : f₁ = f₂)
    {E₁ : SquareZeroExtension B S hS f₁} {E₂ : SquareZeroExtension B S hS f₂} (hA : E₁.A = E₂.A)
    (hπ : E₁.π = eqToHom hA ≫ E₂.π)
    (hb : E₁.toBase ≫ eqToHom hA =
      eqToHom (congrArg (inverseImageStructureCommRingSheaf B S hS) h) ≫ E₂.toBase)
    (R : SquareZeroExtension.ToposRealization E₁) :
    SquareZeroExtension.Realization B S hS E₂ where
  ambient := R.ambient
  closed := R.closed
  firstOrder := R.firstOrder
  closedIso := R.closedIso
  immersion := R.immersion
  immersion_eq := R.immersion_eq
  toBase := R.toBase
  over_base := R.over_base.trans h
  sheafIso := R.sheafIso ≪≫ eqToIso hA
  quotient_compatibility :=
    (Category.assoc _ _ _).trans ((congrArg (R.sheafIso.hom ≫ ·) hπ.symm).trans
      R.quotient_compatibility)
  baseComparison := canonicalBaseComparison B S hS R.immersion R.toBase f₂ (R.over_base.trans h)
  baseComparison_canonical := rfl
  algebra_compatibility := by
    have h1 := R.algebra_compatibility
    subst h
    rw [eqToHom_refl, Category.id_comp] at hb
    rw [← hb, h1, canonicalBaseComparison_hom_eq]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _))))).trans (Category.assoc _ _ _).symm

/-- **The two identifications of the inverse image of `𝒪_{Y'}` with `t⁻¹ρ^*ι⁻¹𝒪_{Y'}` agree**:
through `(t ≫ j)⁻¹ ≅ t⁻¹j⁻¹` and `j = ρ ≫ ι`, and through `((t ≫ ρ) ≫ ι)⁻¹ ≅ (t ≫ ρ)⁻¹ι⁻¹` and
`restrictedRingIso`. This is the associativity of the composition law of Stacks 03G8. -/
theorem restrictedBase_coherence (j : Y₀ ⟶ Y') (hj : ρ.hom ≫ subspaceInclusion B S hS Y' Z = j) :
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS t j).inv.app
        (smallEtaleRingedTopos B S hS Y').O ≫
      (smallEtaleInverseImageRing B S hS t).map
        (eqToHom (congrArg (inverseImageStructureSheaf B S hS) hj.symm) ≫
          (restrictedFirstOrderExtensionIso B S hS Z hZ ρ (𝟙 Y')).hom) =
    eqToHom (congrArg (fun φ => (smallEtaleInverseImageRing B S hS (t ≫ φ)).obj
        (smallEtaleRingedTopos B S hS Y').O) hj.symm) ≫
      (smallEtaleRingedToposHom_compInverseImageRingIso B S hS (t ≫ ρ.hom)
        (subspaceInclusion B S hS Y' Z)).inv.app (smallEtaleRingedTopos B S hS Y').O ≫
      (restrictedRingIso ρ t (baseExtension hZ).extension).hom := by
  subst hj
  have ha := smallEtaleRingedToposHom_compInverseImageRingIso_inv_assoc B S hS t ρ.hom
    (subspaceInclusion B S hS Y' Z) (smallEtaleRingedTopos B S hS Y').O
  simp only [eqToHom_refl, Category.id_comp]
  show _ ≫ (smallEtaleInverseImageRing B S hS t).map
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS ρ.hom
        (subspaceInclusion B S hS Y' Z)).inv.app _ ≫ (restrictionRingIso ρ _).hom) =
    _ ≫ (smallEtaleRingedToposHom_compInverseImageRingIso B S hS t ρ.hom).inv.app _ ≫
      (smallEtaleInverseImageRing B S hS t).map (restrictionRingIso ρ _).hom
  exact (congrArg (_ ≫ ·) ((smallEtaleInverseImageRing B S hS t).map_comp _ _)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ha.symm).trans (Category.assoc _ _ _)))

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
