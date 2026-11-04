module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalClassRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSections
public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPushout
public import StacksFrontier.Deformation.ToposThickening.SolutionPairSeparation
public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroAlgebraExtensionClass

/-!
# Extensions with the same class are isomorphic

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. This file
proves that two extensions `0 ⟶ 𝒢 ⟶ 𝒪'ᵢ ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras with the same class in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` are isomorphic: the class map of **Stacks 0GPZ** is injective.

The argument is Steps 1 to 3 of the proof of **Stacks 08U8**, as used in the proof of
**Stacks 08UC**. Present `𝒪_X` by the sheaf of sets `ℰ = 𝒪'₁ ×_{𝒪_X} 𝒪'₂`, which lifts to both
extensions. The classes of the two extensions are then the classes of two homomorphisms
`δᵢ : 𝒥/𝒥² ⟶ 𝒢` on one conormal sheaf, and their equality says that `δ₁ - δ₂` factors as
`θ ∘ d` through the degree `0` term `Ω` of `𝖭𝖫(α)`. Then `D = θ ∘ d` is an `f⁻¹𝒪_S`-derivation of
`f⁻¹𝒪_S[ℰ]` with values in `𝒢`, and `x ↦ φ₂(x) + D(x)` is a homomorphism of sheaves of rings
`f⁻¹𝒪_S[ℰ] ⟶ 𝒪'₂` killing the kernel of `φ₁ : f⁻¹𝒪_S[ℰ] ⟶ 𝒪'₁`; it descends along the locally
surjective `φ₁` to a morphism of extensions `𝒪'₁ ⟶ 𝒪'₂`, which is an isomorphism. The descent
is `CategoryTheory.Sheaf.descendRingHom`.

## Main definitions

* `SquareZeroAlgebraExtension.pairGenerators`: the sheaf of sets `𝒪'₁ ×_{𝒪_X} 𝒪'₂`.
* `SquareZeroAlgebraExtension.presentedFst` and `presentedSnd`: the two extensions presented
  over it.

* `SquareZeroAlgebraExtension.derivation` and `twist`: the derivation `θ ∘ d` and the twisted
  homomorphism `φ₂ + θ ∘ d`; `homOfFactorization` the resulting morphism of extensions.

## Main results

* `SquareZeroAlgebraExtension.classMap_injective`: the class map is injective.
* `SquareZeroAlgebraExtension.nonempty_hom_of_extClass_eq`: two extensions with the same class
  have a morphism of extensions, hence are isomorphic.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  freeAlgebraSheafVariable freeAlgebraSheafCoefficientMap)

universe u

attribute [local instance 5000] _root_.SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-! ### The fibre product of two extensions -/

section Pair

variable (P Q : SquareZeroAlgebraExtension f G)

/-- The sheaf of sets `𝒪'₁ ×_{𝒪_X} 𝒪'₂` underlying the fibre product of two extensions. -/
def pairGenerators : (Opens X.carrier)ᵒᵖ ⥤ Type u where
  obj U := {x : P.sheaf.obj.obj U × Q.sheaf.obj.obj U //
    P.reduction.hom.app U x.1 = Q.reduction.hom.app U x.2}
  map {U V} g := TypeCat.ofHom fun x ↦ ⟨(P.sheaf.obj.map g x.1.1, Q.sheaf.obj.map g x.1.2),
    by rw [NatTrans.naturality_apply, NatTrans.naturality_apply, x.2]⟩
  map_id U := by
    ext x
    · exact CategoryTheory.congr_fun (P.sheaf.obj.map_id U) x.1.1
    · exact CategoryTheory.congr_fun (Q.sheaf.obj.map_id U) x.1.2
  map_comp f g := by
    ext x
    · exact CategoryTheory.congr_fun (P.sheaf.obj.map_comp f g) x.1.1
    · exact CategoryTheory.congr_fun (Q.sheaf.obj.map_comp f g) x.1.2

/-- The first projection `𝒪'₁ ×_{𝒪_X} 𝒪'₂ ⟶ 𝒪'₁`. -/
def pairFst : pairGenerators P Q ⟶ P.generators where
  app U := TypeCat.ofHom fun x ↦ x.1.1

/-- The second projection `𝒪'₁ ×_{𝒪_X} 𝒪'₂ ⟶ 𝒪'₂`. -/
def pairSnd : pairGenerators P Q ⟶ Q.generators where
  app U := TypeCat.ofHom fun x ↦ x.1.2

/-- The family of generators `𝒪'₁ ×_{𝒪_X} 𝒪'₂ ⟶ 𝒪_X`. -/
abbrev pairMap : pairGenerators P Q ⟶
    underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf :=
  pairFst P Q ≫ P.generatorsMap

/-- The two projections of `𝒪'₁ ×_{𝒪_X} 𝒪'₂` agree after reduction to `𝒪_X`. -/
theorem pairSnd_comp_generatorsMap : pairSnd P Q ≫ Q.generatorsMap = pairMap P Q := by
  ext U x
  exact x.2.symm

/-- The first projection `𝒪'₁ ×_{𝒪_X} 𝒪'₂ ⟶ 𝒪'₁` is locally surjective. -/
instance isLocallySurjective_pairFst :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) (pairFst P Q) where
  imageSieve_mem {U} y := by
    refine (Opens.grothendieckTopology X.carrier).superset_covering (fun V g hg ↦ ?_)
      (Presheaf.imageSieve_mem _ Q.reduction.hom (P.reduction.hom.app (op U) y))
    obtain ⟨z, hz⟩ := hg
    refine ⟨⟨(P.sheaf.obj.map g.op y, z), ?_⟩, rfl⟩
    rw [NatTrans.naturality_apply]
    exact hz.symm

/-- The reduction `𝒪' ⟶ 𝒪_X` of an extension is locally surjective as a map of presheaves of
sets. -/
instance isLocallySurjective_generatorsMap :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) P.generatorsMap :=
  (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mp P.reduction_surjective

/-- The presentation `f⁻¹𝒪_S[𝒪'₁ ×_{𝒪_X} 𝒪'₂] ⟶ 𝒪_X` is locally surjective. -/
instance isLocallySurjective_pairPresentation :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation f (pairGenerators P Q) (pairMap P Q)).hom :=
  Stacks.SheafOfModules.isLocallySurjective_presentation_of_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    (pairGenerators P Q) (pairMap P Q)

/-- The first extension, presented over `𝒪'₁ ×_{𝒪_X} 𝒪'₂` by the first projection. -/
def presentedFst : PresentedSquareZeroExtension f G (pairGenerators P Q) (pairMap P Q) where
  sheaf := P.sheaf
  base := P.base
  reduction := P.reduction
  base_comp_reduction := P.base_comp_reduction
  liftGen := pairFst P Q
  liftGen_comp := rfl
  ideal := P.ideal

/-- The second extension, presented over `𝒪'₁ ×_{𝒪_X} 𝒪'₂` by the second projection. -/
def presentedSnd : PresentedSquareZeroExtension f G (pairGenerators P Q) (pairMap P Q) where
  sheaf := Q.sheaf
  base := Q.base
  reduction := Q.reduction
  base_comp_reduction := Q.base_comp_reduction
  liftGen := pairSnd P Q
  liftGen_comp := pairSnd_comp_generatorsMap P Q
  ideal := Q.ideal

/-- The first presented extension has the class of the first extension. -/
theorem extClass_presentedFst : (presentedFst P Q).extClass = P.extClass :=
  PresentedSquareZeroExtension.extClass_eq_of_hom (presentedFst P Q) P.toPresented
    (pairFst P Q) rfl (𝟙 _) (Category.id_comp _) (Category.comp_id _) rfl (fun _ _ ↦ rfl)

/-- The second presented extension has the class of the second extension. -/
theorem extClass_presentedSnd : (presentedSnd P Q).extClass = Q.extClass :=
  PresentedSquareZeroExtension.extClass_eq_of_hom (presentedSnd P Q) Q.toPresented
    (pairSnd P Q) (pairSnd_comp_generatorsMap P Q) (𝟙 _) (Category.id_comp _)
    (Category.comp_id _) rfl (fun _ _ ↦ rfl)

end Pair

/-! ### The derivation `θ ∘ d` and the twisted homomorphism -/

section Twist

variable (P Q : SquareZeroAlgebraExtension f G)

/-- `f⁻¹𝒪_S[ℰ]` for `ℰ = 𝒪'₁ ×_{𝒪_X} 𝒪'₂`. -/
abbrev pairRing : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} :=
  freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
    (pairGenerators P Q)

/-- The presentation `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`. -/
abbrev pairPresentation : pairRing P Q ⟶ X.sheaf :=
  generatorsPresentation f (pairGenerators P Q) (pairMap P Q)

/-- The structure morphism `f⁻¹𝒪_S ⟶ f⁻¹𝒪_S[ℰ]`. -/
abbrev pairCoefficient : inverseImageBaseRing f ⟶ pairRing P Q :=
  freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) (pairGenerators P Q)

/-- The local section `1 ⊗ d x` of the degree `0` term of `𝖭𝖫(α)`. -/
abbrev pairDifferential (U : (Opens X.carrier)ᵒᵖ) (x : (pairRing P Q).obj.obj U) :=
  Stacks.Sites.Conormal.tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) (pairRing P Q) X.sheaf (pairCoefficient P Q)
    (pairPresentation P Q) U x

/-- `φ₁ : f⁻¹𝒪_S[ℰ] ⟶ 𝒪'₁`, sending a variable to its first component. -/
abbrev liftFst : pairRing P Q ⟶ P.sheaf := (presentedFst P Q).lift

/-- `φ₂ : f⁻¹𝒪_S[ℰ] ⟶ 𝒪'₂`, sending a variable to its second component. -/
abbrev liftSnd : pairRing P Q ⟶ Q.sheaf := (presentedSnd P Q).lift

/-- The second presented extension lifts the presentation: `φ₂` followed by the reduction is
`f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`, read on sections. -/
theorem reduction_liftSnd (U : (Opens X.carrier)ᵒᵖ) (x : (pairRing P Q).obj.obj U) :
    (Q.reduction.hom.app U).hom (((liftSnd P Q).hom.app U).hom x) =
      ((pairPresentation P Q).hom.app U).hom x :=
  congrArg (fun t : pairRing P Q ⟶ X.sheaf ↦ (t.hom.app U).hom x)
    (presentedSnd P Q).lift_comp_reduction

/-- `φ₁` followed by the reduction is `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`, read on sections. -/
theorem reduction_liftFst (U : (Opens X.carrier)ᵒᵖ) (x : (pairRing P Q).obj.obj U) :
    (P.reduction.hom.app U).hom (((liftFst P Q).hom.app U).hom x) =
      ((pairPresentation P Q).hom.app U).hom x :=
  congrArg (fun t : pairRing P Q ⟶ X.sheaf ↦ (t.hom.app U).hom x)
    (presentedFst P Q).lift_comp_reduction

/-- `φ₁ : f⁻¹𝒪_S[ℰ] ⟶ 𝒪'₁` is locally surjective. -/
instance isLocallySurjective_liftFst :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) (liftFst P Q).hom :=
  (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    (Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) P.sheaf
        (pairGenerators P Q) P.base (pairFst P Q)))

/-- A section of `f⁻¹𝒪_S[ℰ]` with `φ₁(x)` in the kernel of `𝒪'₁ ⟶ 𝒪_X` lies in the kernel
of the presentation. -/
private theorem mem_kernelIdeal_pairPresentation (U : (Opens X.carrier)ᵒᵖ)
    (x : (pairRing P Q).obj.obj U)
    (hx : ((liftFst P Q).hom.app U).hom x ∈ kernelIdeal P.reduction.hom U) :
    x ∈ kernelIdeal (pairPresentation P Q).hom U := by
  change ((pairPresentation P Q).hom.app U).hom x = 0
  rw [← reduction_liftFst]
  exact hx

variable {P Q} (θ : (PresentedSquareZeroExtension.twoTerm f (pairGenerators P Q)
  (pairMap P Q)).base ⟶ G)

/-- The derivation `D = θ ∘ d : f⁻¹𝒪_S[ℰ] ⟶ 𝒢`, on sections. -/
def derivation (U : (Opens X.carrier)ᵒᵖ) (x : (pairRing P Q).obj.obj U) : G.val.obj U :=
  θ.val.app U (pairDifferential P Q U x)

/-- The derivation `D` is additive. -/
theorem derivation_add (U : (Opens X.carrier)ᵒᵖ) (x y : (pairRing P Q).obj.obj U) :
    derivation θ U (x + y) = derivation θ U x + derivation θ U y :=
  (congrArg (θ.val.app U) (Stacks.Sites.Conormal.tensorDifferential_add.{u, u, u, u} _ _ _ _ _
    _ U x y)).trans (map_add _ _ _)

/-- The Leibniz rule for `D`, with `f⁻¹𝒪_S[ℰ]` acting on `𝒢` through `𝒪_X`. -/
theorem derivation_mul (U : (Opens X.carrier)ᵒᵖ) (x y : (pairRing P Q).obj.obj U) :
    derivation θ U (x * y) =
      Stacks.Sites.Conormal.presentationScalar (pairPresentation P Q) U x • derivation θ U y +
        Stacks.Sites.Conormal.presentationScalar (pairPresentation P Q) U y •
          derivation θ U x :=
  (congrArg (θ.val.app U) (Stacks.Sites.Conormal.tensorDifferential_mul.{u, u, u, u} _ _ _ _ _
    _ U x y)).trans ((map_add _ _ _).trans (congrArg₂ (· + ·)
      ((θ.val.app U).hom.map_smul _ _) ((θ.val.app U).hom.map_smul _ _)))

/-- The derivation `D` vanishes on the image of `f⁻¹𝒪_S`. -/
theorem derivation_coefficient (U : (Opens X.carrier)ᵒᵖ)
    (a : (inverseImageBaseRing f).obj.obj U) :
    derivation θ U (((pairCoefficient P Q).hom.app U).hom a) = 0 :=
  (congrArg (θ.val.app U) (Stacks.Sites.Conormal.tensorDifferential_coefficient.{u, u, u, u}
    _ _ _ _ _ _ U a)).trans (map_zero _)

/-- The derivation `D` vanishes on `1`. -/
theorem derivation_one (U : (Opens X.carrier)ᵒᵖ) : derivation θ U 1 = 0 :=
  (congrArg (derivation θ U) (map_one ((pairCoefficient P Q).hom.app U).hom).symm).trans
    (derivation_coefficient θ U 1)

/-- The derivation `D` commutes with restriction of sections. -/
theorem derivation_map {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V)
    (x : (pairRing P Q).obj.obj U) :
    derivation θ V ((pairRing P Q).obj.map i x) = G.val.map i (derivation θ U x) :=
  (congrArg (θ.val.app V) (Stacks.Sites.Conormal.tensorDifferential_map.{u, u, u, u} _ _ _ _ _
    _ i x)).trans (PresheafOfModules.naturality_apply θ.val i _)

/-- The Leibniz rule for `D` in `𝒪'₂`, with `f⁻¹𝒪_S[ℰ]` acting through `φ₂`. -/
theorem incl_derivation_mul (U : (Opens X.carrier)ᵒᵖ) (x y : (pairRing P Q).obj.obj U) :
    Q.incl U (derivation θ U (x * y)) =
      ((liftSnd P Q).hom.app U).hom x * Q.incl U (derivation θ U y) +
        ((liftSnd P Q).hom.app U).hom y * Q.incl U (derivation θ U x) := by
  rw [derivation_mul, Q.incl_add, ← Q.incl_smul, ← Q.incl_smul]
  congr 3
  · exact (reduction_liftSnd P Q U x).symm
  · exact (reduction_liftSnd P Q U y).symm

/-- The twisted homomorphism `x ↦ φ₂(x) + D(x)` on sections. -/
def twistApp (U : (Opens X.carrier)ᵒᵖ) : (pairRing P Q).obj.obj U →+* Q.sheaf.obj.obj U where
  toFun x := ((liftSnd P Q).hom.app U).hom x + Q.incl U (derivation θ U x)
  map_one' := by
    rw [map_one, derivation_one, Q.incl_zero, add_zero]
  map_mul' x y := by
    rw [map_mul, incl_derivation_mul]
    have h := Q.incl_mul_incl U (derivation θ U x) (derivation θ U y)
    linear_combination (-1 : Q.sheaf.obj.obj U) * h
  map_zero' := by
    rw [map_zero, show derivation θ U 0 = 0 from by
      have h := derivation_add θ U 0 0
      rw [add_zero] at h
      exact (add_eq_left.mp h.symm), Q.incl_zero, add_zero]
  map_add' x y := by
    rw [map_add, derivation_add, Q.incl_add]
    ring

/-- The twisted homomorphism commutes with restriction of sections. -/
theorem twistApp_naturality {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V)
    (x : (pairRing P Q).obj.obj U) :
    twistApp θ V ((pairRing P Q).obj.map i x) = Q.sheaf.obj.map i (twistApp θ U x) := by
  show ((liftSnd P Q).hom.app V).hom ((pairRing P Q).obj.map i x) +
      Q.incl V (derivation θ V ((pairRing P Q).obj.map i x)) =
    (Q.sheaf.obj.map i).hom (((liftSnd P Q).hom.app U).hom x +
      Q.incl U (derivation θ U x))
  rw [map_add, derivation_map, ← Q.incl_map]
  congr 1
  exact NatTrans.naturality_apply (liftSnd P Q).hom i x

/-- **The twisted homomorphism** `x ↦ φ₂(x) + D(x) : f⁻¹𝒪_S[ℰ] ⟶ 𝒪'₂` of sheaves of rings. -/
def twist : pairRing P Q ⟶ Q.sheaf :=
  ⟨{ app U := CommRingCat.ofHom (twistApp θ U)
     naturality {U V} i := by
       ext x
       exact twistApp_naturality θ i x }⟩

/-- The twisted homomorphism sends a section `x` to `φ₂(x) + D(x)`. -/
theorem twist_app (U : (Opens X.carrier)ᵒᵖ) (x : (pairRing P Q).obj.obj U) :
    ((twist θ).hom.app U).hom x =
      ((liftSnd P Q).hom.app U).hom x + Q.incl U (derivation θ U x) :=
  rfl

variable (hθ : (PresentedSquareZeroExtension.twoTerm f (pairGenerators P Q) (pairMap P Q)).d ≫ θ =
  PresentedSquareZeroExtension.obstruction (presentedFst P Q) (presentedSnd P Q))

include hθ in
/-- On the kernel `𝒥` of `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` the derivation `D = θ ∘ d` is the difference of the
two restriction data. -/
theorem derivation_of_mem (U : (Opens X.carrier)ᵒᵖ)
    (x : kernelIdeal (pairPresentation P Q).hom U) :
    derivation θ U x.1 = (presentedFst P Q).idealRestriction.app U x -
      (presentedSnd P Q).idealRestriction.app U x := by
  refine (congrArg (θ.val.app U) (Stacks.Sites.Conormal.conormalSequence_f_class.{u, u, u, u}
    _ _ _ _ _ _ U x).symm).trans ?_
  refine (congrArg (fun t ↦ t.val.app U (Stacks.Sites.Conormal.conormalClass.{u, u, u, u}
    _ _ _ _ (pairCoefficient P Q) (pairPresentation P Q) U x)) hθ).trans ?_
  exact Stacks.Sites.Conormal.conormalDifference_toAssociatedModule.{u, u, u, u} _ G _ _ U x

include hθ in
/-- **The twisted homomorphism kills the kernel of `φ₁`.** -/
theorem twist_eq_zero (U : (Opens X.carrier)ᵒᵖ) (x : (pairRing P Q).obj.obj U)
    (hx : ((liftFst P Q).hom.app U).hom x = 0) : ((twist θ).hom.app U).hom x = 0 := by
  have hx' := mem_kernelIdeal_pairPresentation P Q U x (RingHom.mem_ker.2 (by rw [hx, map_zero]))
  have h1 : (presentedFst P Q).idealRestriction.app U ⟨x, hx'⟩ = 0 := by
    rw [PresentedSquareZeroExtension.idealRestriction_app]
    exact (congrArg (P.ideal.app U) (Subtype.ext hx)).trans (map_zero _)
  rw [twist_app, derivation_of_mem θ hθ U ⟨x, hx'⟩, h1, zero_sub,
    PresentedSquareZeroExtension.idealRestriction_app]
  exact (congrArg (_ + ·) ((Q.incl_neg U _).trans
    (congrArg Neg.neg (Q.incl_ideal U ⟨_, _⟩)))).trans (add_neg_cancel _)

/-- **The morphism `𝒪'₁ ⟶ 𝒪'₂`**: the descent of the twisted homomorphism along the locally
surjective `φ₁`. -/
def descendedTwist : P.sheaf ⟶ Q.sheaf :=
  Sheaf.descendRingHom.{u, u, u} (liftFst P Q) (twist θ) (twist_eq_zero θ hθ)

/-- The morphism `𝒪'₁ ⟶ 𝒪'₂` composed with `φ₁` is the twisted homomorphism. -/
theorem liftFst_comp_descendedTwist : liftFst P Q ≫ descendedTwist θ hθ = twist θ :=
  Sheaf.descendRingHom_comp.{u, u, u} (liftFst P Q) (twist θ) (twist_eq_zero θ hθ)

/-- The morphism `𝒪'₁ ⟶ 𝒪'₂` sends `φ₁(x)` to `φ₂(x) + D(x)`. -/
theorem descendedTwist_app (U : (Opens X.carrier)ᵒᵖ) (x : (pairRing P Q).obj.obj U) :
    ((descendedTwist θ hθ).hom.app U).hom (((liftFst P Q).hom.app U).hom x) =
      ((liftSnd P Q).hom.app U).hom x + Q.incl U (derivation θ U x) :=
  congrArg (fun t : pairRing P Q ⟶ Q.sheaf ↦ (t.hom.app U).hom x)
    (liftFst_comp_descendedTwist θ hθ)

/-- The twisted homomorphism followed by the reduction of `𝒪'₂` is the presentation
`f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`. -/
theorem twist_comp_reduction : twist θ ≫ Q.reduction = pairPresentation P Q := by
  apply Sheaf.hom_ext
  ext U x
  show (Q.reduction.hom.app U).hom (((twist θ).hom.app U).hom x) = _
  rw [twist_app, map_add, Q.reduction_incl, add_zero, reduction_liftSnd]

/-- The morphism `𝒪'₁ ⟶ 𝒪'₂` commutes with the reductions to `𝒪_X`. -/
theorem descendedTwist_comp_reduction : descendedTwist θ hθ ≫ Q.reduction = P.reduction :=
  Sheaf.hom_ext_of_isLocallySurjective.{u, u, u} (liftFst P Q) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Q.reduction) (liftFst_comp_descendedTwist θ hθ)).trans
      ((twist_comp_reduction θ).trans (presentedFst P Q).lift_comp_reduction.symm)))

/-- The morphism `𝒪'₁ ⟶ 𝒪'₂` commutes with the structure maps from `f⁻¹𝒪_S`. -/
theorem base_comp_descendedTwist : P.base ≫ descendedTwist θ hθ = Q.base := by
  have hP : pairCoefficient P Q ≫ liftFst P Q = P.base :=
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) P.sheaf
      (pairGenerators P Q) P.base (pairFst P Q)
  have hQ : pairCoefficient P Q ≫ liftSnd P Q = Q.base :=
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) Q.sheaf
      (pairGenerators P Q) Q.base (pairSnd P Q)
  have ht : pairCoefficient P Q ≫ twist θ = Q.base := by
    refine Eq.trans ?_ hQ
    apply Sheaf.hom_ext
    ext U a
    show ((twist θ).hom.app U).hom (((pairCoefficient P Q).hom.app U).hom a) = _
    rw [twist_app, derivation_coefficient, Q.incl_zero, add_zero]
    rfl
  exact (congrArg (· ≫ descendedTwist θ hθ) hP).symm.trans ((Category.assoc _ _ _).trans
    ((congrArg (pairCoefficient P Q ≫ ·) (liftFst_comp_descendedTwist θ hθ)).trans ht))

/-- On a local section `φ₁(x)` of the square-zero ideal of `𝒪'₁` the morphism is the identity of
`𝒢`. -/
theorem ideal_descendedTwist_lift (U : (Opens X.carrier)ᵒᵖ) (x : (pairRing P Q).obj.obj U)
    (hx : ((liftFst P Q).hom.app U).hom x ∈ kernelIdeal P.reduction.hom U) :
    Q.ideal.app U ⟨((descendedTwist θ hθ).hom.app U).hom (((liftFst P Q).hom.app U).hom x),
      map_mem_kernelIdeal _ (descendedTwist_comp_reduction θ hθ) U ⟨_, hx⟩⟩ =
      P.ideal.app U ⟨_, hx⟩ := by
  have hx' := mem_kernelIdeal_pairPresentation P Q U x hx
  have h2 : ((liftSnd P Q).hom.app U).hom x ∈ kernelIdeal Q.reduction.hom U := by
    show (Q.reduction.hom.app U).hom _ = 0
    rw [reduction_liftSnd]
    exact hx'
  have hsplit : (⟨((descendedTwist θ hθ).hom.app U).hom (((liftFst P Q).hom.app U).hom x),
      map_mem_kernelIdeal _ (descendedTwist_comp_reduction θ hθ) U ⟨_, hx⟩⟩ :
        kernelIdeal Q.reduction.hom U) =
      ⟨_, h2⟩ + ⟨Q.incl U (derivation θ U x), Q.incl_mem U _⟩ :=
    Subtype.ext (descendedTwist_app θ hθ U x)
  rw [hsplit, map_add, Q.ideal_incl, derivation_of_mem θ hθ U ⟨x, hx'⟩,
    PresentedSquareZeroExtension.idealRestriction_app,
    PresentedSquareZeroExtension.idealRestriction_app]
  exact add_sub_cancel _ _

/-- **The morphism `𝒪'₁ ⟶ 𝒪'₂` is the identity on `𝒢`.** Locally a section of the square-zero
ideal of `𝒪'₁` is `φ₁(x)`, where this is `ideal_descendedTwist_lift`. -/
theorem ideal_descendedTwist (U : (Opens X.carrier)ᵒᵖ) (y : kernelIdeal P.reduction.hom U) :
    Q.ideal.app U ⟨((descendedTwist θ hθ).hom.app U).hom y.1,
      map_mem_kernelIdeal _ (descendedTwist_comp_reduction θ hθ) U y⟩ = P.ideal.app U y := by
  refine Stacks.Sites.SqZeroPushout.eq_of_locally_eq (Stacks.SheafOfModules.isSheaf_forget G)
    (Presheaf.imageSieve_mem _ (liftFst P Q).hom y.1) _ _ fun V g hg ↦ ?_
  obtain ⟨x, hx⟩ := hg
  have hxk : ((liftFst P Q).hom.app (op V)).hom x ∈ kernelIdeal P.reduction.hom (op V) := by
    rw [show ((liftFst P Q).hom.app (op V)).hom x = (P.sheaf.obj.map g.op).hom y.1 from hx]
    exact Stacks.Sites.Conormal.map_kernel P.reduction.hom g.op y.2
  show G.val.map g.op _ = G.val.map g.op _
  rw [← Q.ideal.app_map, ← P.ideal.app_map]
  refine Eq.trans ?_ ((ideal_descendedTwist_lift θ hθ (op V) x hxk).trans
    (congrArg (P.ideal.app (op V)) (Subtype.ext hx)))
  refine congrArg (Q.ideal.app (op V)) (Subtype.ext ?_)
  refine (NatTrans.naturality_apply (descendedTwist θ hθ).hom g.op y.1).symm.trans ?_
  exact congrArg ((descendedTwist θ hθ).hom.app (op V)).hom hx.symm

/-- The morphism of extensions `𝒪'₁ ⟶ 𝒪'₂` built from a factorization `θ` of the difference of
the two conormal homomorphisms. -/
def homOfFactorization : P ⟶ Q where
  hom := descendedTwist θ hθ
  hom_reduction := descendedTwist_comp_reduction θ hθ
  base_hom := base_comp_descendedTwist θ hθ
  ideal_hom := ideal_descendedTwist θ hθ

end Twist

/-- **Two extensions with the same class are isomorphic.** Their classes are those of the two
homomorphisms `𝒥/𝒥² ⟶ 𝒢` of the presentation by `𝒪'₁ ×_{𝒪_X} 𝒪'₂`, so the difference of these
factors through the degree `0` term of `𝖭𝖫(α)` as `θ ∘ d`; twisting `φ₂` by `θ ∘ d` and
descending along `φ₁` gives a morphism of extensions. -/
theorem nonempty_hom_of_extClass_eq {P Q : SquareZeroAlgebraExtension f G}
    (h : P.extClass = Q.extClass) : Nonempty (P ⟶ Q) := by
  have h12 : (presentedFst P Q).extClass = (presentedSnd P Q).extClass :=
    (extClass_presentedFst P Q).trans (h.trans (extClass_presentedSnd P Q).symm)
  obtain ⟨θ, hθ⟩ := ((PresentedSquareZeroExtension.twoTerm f (pairGenerators P Q)
    (pairMap P Q)).conormalExtClass_eq_zero_iff G _).1
      ((PresentedSquareZeroExtension.extClass_eq_extClass_iff _ _).1 h12)
  exact ⟨homOfFactorization θ hθ⟩

/-- **The class map of Stacks 0GPZ is injective.** -/
theorem classMap_injective : Function.Injective (classMap f G) := by
  rintro ⟨P⟩ ⟨Q⟩ h
  obtain ⟨φ⟩ := nonempty_hom_of_extClass_eq h
  exact Quotient.sound ⟨isoOfHom φ⟩

end AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

end
