module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.EtaleLocalAffineColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite

/-!
# The Čech nerve of a morphism of algebraic spaces, and coequalizers

Let `p : Y ⟶ X'` be a morphism of algebraic spaces over `S`. Its Čech nerve, the simplicial
object `[n] ↦ Y ×_{X'} ⋯ ×_{X'} Y` (`n + 1` factors), is a diagram of algebraic spaces with a
cocone to `X'`. This file shows that if that cocone is a colimit, among algebraic spaces over the
final algebraic space `S`, then `p` is a coequalizer of the two projections of the kernel pair
of any `g = p ≫ ν` which `p` equalizes. This is the form in which Stacks 0GHL, applied to the
truncated Čech nerve of the proper surjective morphism `Y ⟶ X'`, gives the coequalizer property
in the proof of Stacks 0AGG: the source applies Stacks 0GHL to the diagram `R ⇉ Y`, whose
étale-site condition is a descent condition only once the diagram is extended by `R ×_Y R`.

## Main definitions

* `AlgebraicGeometry.Space.cechNerveSpace`: the Čech nerve of `p`, as a simplicial algebraic
  space. Its terms are the presheaf wide fibre products, which are algebraic spaces because the
  inclusion of algebraic spaces into presheaves preserves finite limits
  (`AlgebraicGeometry.Space.preservesFiniteLimits_algebraicSpacesι`).
* `AlgebraicGeometry.Space.cechDiagram` and `AlgebraicGeometry.Space.cechCocone`: the Čech nerve
  as a diagram of algebraic spaces over the final algebraic space, and its cocone with vertex
  `X'`.

## Main results

* `AlgebraicGeometry.Space.isColimitCofork_of_isColimit_cechCoconeSpace`: if the Čech cocone of
  `p` is a colimit among algebraic spaces and `p` coequalizes the kernel pair of `g = p ≫ ν`,
  then `p` is a coequalizer of that kernel pair.

## References

* [Stacks Project, Tag 0GHL](https://stacks.math.columbia.edu/tag/0GHL)
* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inclusion of algebraic spaces into presheaves preserves finite limits -/

/-- The inclusion of algebraic spaces into presheaves preserves the final object: the final
algebraic space is the presheaf represented by the base, which is final among presheaves. -/
instance preservesLimit_empty_algebraicSpacesι :
    PreservesLimit (Functor.empty.{0} (AlgebraicSpaces B S hS))
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) :=
  preservesLimit_of_preserves_limit_cone (terminalSpace_isTerminal B S hS)
    ((isLimitMapConeEmptyConeEquiv _ _).symm (baseTerminal_yonedaIsTerminal B S hS))

/-- The inclusion of algebraic spaces into presheaves preserves fibre products, which are
computed in presheaves. -/
instance preservesLimit_cospan_algebraicSpacesι {F G H : AlgebraicSpaces B S hS}
    (f : F ⟶ H) (g : G ⟶ H) :
    PreservesLimit (cospan f g)
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) :=
  preservesLimit_of_preserves_limit_cone (pullbackIsPullback f g)
    ((isLimitMapConePullbackConeEquiv _ pullback.condition).symm
      (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g)).isLimit)

/-- The inclusion of algebraic spaces into presheaves preserves finite limits. -/
instance preservesFiniteLimits_algebraicSpacesι :
    PreservesFiniteLimits
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) := by
  have : PreservesLimitsOfShape (Discrete.{0} PEmpty)
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  have : PreservesLimitsOfShape WalkingCospan
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) :=
    ⟨fun {K} => preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm⟩
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-! ### The Čech nerve -/

variable {B S hS}

/-- Algebraic spaces have finite limits, having a final object and fibre products. -/
instance : HasFiniteLimits (AlgebraicSpaces B S hS) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- A presheaf wide fibre product of finitely many copies of an algebraic space over another is
an algebraic space: it is the image of the wide fibre product of algebraic spaces under the
inclusion into presheaves, which preserves finite limits. -/
theorem isAlgebraicSpace_widePullback {X Y : AlgebraicSpaces B S hS} (p : Y ⟶ X) (n : ℕ) :
    IsAlgebraicSpace B S hS
      (widePullback X.obj (fun _ : Fin (n + 1) => Y.obj) fun _ => p.hom) := by
  let K := WidePullbackShape.wideCospan X (fun _ : Fin (n + 1) => Y) fun _ => p
  let ι := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
    IsAlgebraicSpace B S hS F)
  let e : widePullback X.obj (fun _ : Fin (n + 1) => Y.obj) (fun _ => p.hom) ≅
      ι.obj (widePullback X (fun _ : Fin (n + 1) => Y) fun _ => p) :=
    (HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan (K ⋙ ι)).symm) ≪≫
      (preservesLimitIso ι K).symm
  exact isAlgebraicSpace_of_iso B S hS e.symm (widePullback X (fun _ : Fin (n + 1) => Y) _).property

variable {X Y : AlgebraicSpaces B S hS} (p : Y ⟶ X)

/-- **The Čech nerve of `p : Y ⟶ X'`**, as a simplicial algebraic space: its term in degree
`n` is the presheaf wide fibre product of `n + 1` copies of `Y` over `X'`. -/
def cechNerveSpace : SimplicialObject (AlgebraicSpaces B S hS) :=
  ObjectProperty.lift _ (Arrow.mk p.hom).cechNerve fun n =>
    isAlgebraicSpace_widePullback p n.unop.len

/-- The structure morphism of a term of the Čech nerve to `X'`. -/
def cechBase (n : SimplexCategoryᵒᵖ) : (cechNerveSpace p).obj n ⟶ X :=
  ObjectProperty.homMk (WidePullback.base _)

/-- The face and degeneracy maps of the Čech nerve commute with the structure morphisms to
`X'`. -/
@[reassoc (attr := simp)]
theorem cechNerveSpace_map_cechBase {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    (cechNerveSpace p).map θ ≫ cechBase p m = cechBase p n :=
  ObjectProperty.hom_ext _ (WidePullback.lift_base _ _ _ _)

section Base

variable {B₀ : AlgebraicSpaces B S hS} (ν : X ⟶ B₀)

/-- The Čech nerve of `p`, as a diagram of algebraic spaces over `B₀` through `ν : X' ⟶ B₀`. -/
def cechDiagram : SimplexCategoryᵒᵖ ⥤ Over B₀ :=
  (cechNerveSpace p).toOver B₀ (fun n => cechBase p n ≫ ν)
    (fun θ => cechNerveSpace_map_cechBase_assoc p θ ν)

/-- **The Čech cocone of `p`**: the Čech nerve over its target `X'`, over `B₀`. -/
def cechCocone : Cocone (cechDiagram p ν) where
  pt := Over.mk ν
  ι :=
    { app := fun n => Over.homMk (cechBase p n) rfl
      naturality := fun _ _ θ => Over.OverMorphism.ext
        ((cechNerveSpace_map_cechBase p θ).trans (Category.comp_id _).symm) }

/-- The Čech cocone of `p`, among all algebraic spaces. -/
def cechCoconeSpace : Cocone (cechNerveSpace p) where
  pt := X
  ι :=
    { app := fun n => cechBase p n
      naturality := fun _ _ θ => (cechNerveSpace_map_cechBase p θ).trans
        (Category.comp_id _).symm }

/-- Algebraic spaces have binary products, having a final object and fibre products. -/
instance : HasBinaryProducts (AlgebraicSpaces B S hS) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

/-- If the Čech cocone of `p` is a colimit among algebraic spaces over `B₀`, it is a colimit
among all algebraic spaces: the forgetful functor from algebraic spaces over `B₀` is a left
adjoint. -/
def isColimitCechCoconeSpace (h : IsColimit (cechCocone p ν)) : IsColimit (cechCoconeSpace p) :=
  haveI := (Over.forgetAdjStar B₀).leftAdjoint_preservesColimits
  isColimitOfPreserves (Over.forget B₀) h

end Base

/-- The `i`-th projection of a term of the Čech nerve to `Y`. -/
def cechProj {n : SimplexCategoryᵒᵖ} (i : Fin (n.unop.len + 1)) :
    (cechNerveSpace p).obj n ⟶ Y :=
  ObjectProperty.homMk (WidePullback.π _ i)

/-- Each projection of a term of the Čech nerve to `Y`, followed by `p`, is the structure
morphism to `X'`. -/
@[reassoc (attr := simp)]
theorem cechProj_comp {n : SimplexCategoryᵒᵖ} (i : Fin (n.unop.len + 1)) :
    cechProj p i ≫ p = cechBase p n :=
  ObjectProperty.hom_ext _ (WidePullback.π_arrow _ i)

/-- A map of the Čech nerve followed by the `i`-th projection is the projection indexed by the
image of `i` under the underlying map of finite ordinals. -/
@[reassoc (attr := simp)]
theorem cechNerveSpace_map_cechProj {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (i : Fin (m.unop.len + 1)) :
    (cechNerveSpace p).map θ ≫ cechProj p i = cechProj p (θ.unop.toOrderHom i) :=
  ObjectProperty.hom_ext _ (WidePullback.lift_π _ _ _ _ _)

/-- The section `Y ⟶ Y ×_{X'} ⋯` of the degree-zero term of the Čech nerve. -/
def cechZeroSection : Y ⟶ (cechNerveSpace p).obj (op ⦋0⦌) :=
  ObjectProperty.homMk (WidePullback.lift p.hom (fun _ => 𝟙 _) (fun _ => Category.id_comp _))

/-- The section of the degree-zero term is a section of its projection to `Y`. -/
@[reassoc (attr := simp)]
theorem cechZeroSection_cechProj (i : Fin 1) :
    cechZeroSection p ≫ cechProj p (n := op ⦋0⦌) i = 𝟙 Y :=
  ObjectProperty.hom_ext _ (WidePullback.lift_π _ _ _ _ _)

/-- The section of the degree-zero term followed by its structure morphism to `X'` is `p`. -/
@[reassoc (attr := simp)]
theorem cechZeroSection_cechBase :
    cechZeroSection p ≫ cechBase p (op ⦋0⦌) = p :=
  ObjectProperty.hom_ext _ (WidePullback.lift_base _ _ _ _)

/-! ### From the Čech cocone to a coequalizer -/

variable {X₀ : AlgebraicSpaces B S hS} {g : Y ⟶ X₀} {ν₀ : X ⟶ X₀} (hpν : p ≫ ν₀ = g)

include hpν in
/-- A morphism out of `Y` which coequalizes the kernel pair of `g = p ≫ ν` identifies any two
morphisms to `Y` with the same composite to `X'`. -/
theorem comp_eq_comp_of_comp_p_eq {T : AlgebraicSpaces B S hS} (φ : Y ⟶ T)
    (hφ : pullback.fst g g ≫ φ = pullback.snd g g ≫ φ) {A : AlgebraicSpaces B S hS}
    {a b : A ⟶ Y} (hab : a ≫ p = b ≫ p) : a ≫ φ = b ≫ φ := by
  have h : a ≫ g = b ≫ g := by rw [← hpν, ← Category.assoc, hab, Category.assoc]
  rw [← pullback.lift_fst a b h, Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]

/-- The cocone on the Čech nerve attached to a morphism out of `Y` coequalizing the kernel
pair of `g`. -/
def cechCoconeOfCofork {T : AlgebraicSpaces B S hS} (φ : Y ⟶ T)
    (hφ : pullback.fst g g ≫ φ = pullback.snd g g ≫ φ) : Cocone (cechNerveSpace p) where
  pt := T
  ι :=
    { app := fun n => cechProj p 0 ≫ φ
      naturality := fun n m θ => by
        change (cechNerveSpace p).map θ ≫ cechProj p 0 ≫ φ = (cechProj p 0 ≫ φ) ≫ 𝟙 _
        rw [Category.comp_id, cechNerveSpace_map_cechProj_assoc]
        exact comp_eq_comp_of_comp_p_eq p hpν φ hφ (by simp) }

/-- **The Čech cocone gives a coequalizer.** If the Čech cocone of `p : Y ⟶ X'` is a colimit
among algebraic spaces, and `p` coequalizes the kernel pair of `g = p ≫ ν`, then `p` is a
coequalizer of that kernel pair. -/
def isColimitCofork_of_isColimit_cechCoconeSpace (h : IsColimit (cechCoconeSpace p))
    (hp : pullback.fst g g ≫ p = pullback.snd g g ≫ p) :
    IsColimit (Cofork.ofπ p hp) :=
  Cofork.IsColimit.mk _
    (fun s => h.desc (cechCoconeOfCofork p hpν s.π s.condition))
    (fun s => by
      have hfac := h.fac (cechCoconeOfCofork p hpν s.π s.condition) (op ⦋0⦌)
      change cechBase p (op ⦋0⦌) ≫ _ = cechProj p 0 ≫ s.π at hfac
      change p ≫ _ = s.π
      exact (congrArg (· ≫ _) (cechZeroSection_cechBase p).symm).trans
        ((Category.assoc _ _ _).trans ((congrArg (cechZeroSection p ≫ ·) hfac).trans
          (cechZeroSection_cechProj_assoc p 0 s.π))))
    (fun s m hm => h.uniq (cechCoconeOfCofork p hpν s.π s.condition) m (fun n => by
      change cechBase p n ≫ m = cechProj p 0 ≫ s.π
      rw [← cechProj_comp p 0, Category.assoc]
      exact congrArg (cechProj p 0 ≫ ·) hm))

end AlgebraicGeometry.Space

end
