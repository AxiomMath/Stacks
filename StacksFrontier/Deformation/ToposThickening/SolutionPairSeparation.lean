module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalClassRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClassVanishing
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSections
public import StacksFrontier.CategoryTheory.Sites.RingSheafHomDescent
public import StacksFrontier.Deformation.ToposThickening.SolutionAutomorphisms
public import StacksFrontier.Deformation.ToposThickening.SolutionPairObstruction

/-!
# The obstruction class of two solutions vanishes exactly when they are isomorphic

Let `S` be the square-zero extension problem of ringed topoi of [Stacks Project, Tag 08UF] and
let `𝒪'₁`, `𝒪'₂` be two solutions. Their obstruction class `o(𝒪'₁, 𝒪'₂)`, built in
`StacksFrontier/Deformation/ToposThickening/SolutionPairObstruction.lean` from the difference map
`D̄₁₂ : ℐ/ℐ² ⟶ G` of a family of generators, vanishes exactly when there is a morphism of
solutions `𝒪'₁ ⟶ 𝒪'₂`, which is then an isomorphism. This is the assertion of
[Stacks Project, Tag 08UK] that the class "is the obstruction to the existence of an isomorphism,
hence separates the isomorphism classes".

* If `h : 𝒪'₁ ⟶ 𝒪'₂` is a morphism of solutions, the family of generators `ℰ = 𝒪'₁` with
  `β₁ = id` and `β₂ = h` has `φ₂ = h ∘ φ₁`, so its difference map vanishes, and so does the class
  (`PairDatum.ofHom_obstruction`).
* Conversely, if the class vanishes then, by the vanishing criterion
  `Stacks.SheafOfModules.presentationConormalExtClass_eq_zero_iff`, `D̄₁₂ = θ ∘ d` for a map `θ`
  out of the degree `0` term `Ω_{A[ℰ]/A} ⊗ 𝒪` of `NL(α)`. Then `D = θ ∘ d` is an
  `A`-derivation of `A[ℰ]` with values in `G` agreeing with `φ₂ − φ₁` on `ℐ'`, and
  `x ↦ φ₂(x) − D(x)` is a homomorphism `A'[ℰ] ⟶ 𝒪'₂` killing the kernel of the locally
  surjective `φ₁ : A'[ℰ] ⟶ 𝒪'₁`; it descends to the required morphism of solutions
  (`PairDatum.homOfTrivialization`).

## Main results

* `...CompatibleFirstOrderThickening.pairDatumObstruction_eq_zero_iff`: `o(𝒪'₁, 𝒪'₂) = 0` if and
  only if there is a morphism of solutions `𝒪'₁ ⟶ 𝒪'₂`.
* `...CompatibleFirstOrderThickening.pairObstruction_eq_zero_iff` and
  `...CompatibleFirstOrderThickening.pairObstruction_eq_zero_iff_isomorphic`: the same for the
  class in `Ext¹_𝒪(NL_f, G)`, and in terms of isomorphism of solutions.

## References

* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u w v' u' w' z

/-! ### Presentations by locally surjective families of generators -/

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (E : Functor Cᵒᵖ (Type w))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)

/-- The presentation of a locally surjective family of generators is locally surjective. -/
theorem isLocallySurjective_presentation_of_isLocallySurjective
    [Presheaf.IsLocallySurjective J α] :
    Presheaf.IsLocallySurjective J (presentation J A B a E α).hom :=
  (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
    (Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc J A B E a α))

end Stacks.SheafOfModules

/-! ### Restriction data that vanish -/

namespace Stacks.Sites.Conormal.IdealRestriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A₁ A₂ B : Sheaf J CommRingCat.{w}} {ψ : A₁ ⟶ A₂} {φ : A₂ ⟶ B}
  {G : SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
  [Presheaf.IsLocallySurjective J ψ.hom]
  (ρ : IdealRestriction (ψ ≫ φ) G)
  (hρ : ∀ (U : Cᵒᵖ) (k : kernelIdeal (ψ ≫ φ).hom U), ψ.hom.app U k = 0 → ρ.app U k = 0)

/-- A restriction datum that vanishes descends to the vanishing restriction datum. -/
theorem descend_app_eq_zero (h0 : ∀ (U : Cᵒᵖ) (k : kernelIdeal (ψ ≫ φ).hom U), ρ.app U k = 0)
    {U : Cᵒᵖ} (p : kernelIdeal φ.hom U) : (descend ρ hρ).app U p = 0 :=
  descendApp_eq ρ hρ p 0 _ (Presheaf.imageSieve_mem J ψ.hom (U := U) (p : A₂.obj.obj U))
    fun _Y f hf ↦ ⟨⟨hf.choose, lift_mem_kernelIdeal p f _ hf.choose_spec⟩, hf.choose_spec,
      (map_zero (G.val.map f.op).hom).trans (h0 _ _).symm⟩

end Stacks.Sites.Conormal.IdealRestriction

namespace Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  freeAlgebraSheafCoefficientMap freeAlgebraSheafVariable baseChange)
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal)

variable {X : RingedTopos.{v, u, max u v w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B} {Q₁ Q₂ : S.CompatibleFirstOrderThickening}

attribute [local instance] CategoryTheory.Sheaf.wEqualsLocallyBijective_commRingCat

/-! ### A morphism of solutions kills the obstruction class -/

namespace PairDatum

/-- The pair datum of a morphism of solutions `h : 𝒪'₁ ⟶ 𝒪'₂`: the generators are the local
sections of `𝒪'₁`, sent to themselves and to their images under `h`. -/
noncomputable def ofHom (h : CompatibleFirstOrderThickening.Hom Q₁ Q₂) : PairDatum Q₁ Q₂ where
  E := underlyingPresheaf X.J Q₁.extension
  α := Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w})
  β₁ := 𝟙 _
  β₂ := Functor.whiskerRight h.hom.hom (forget CommRingCat.{max u v w})
  comm₁ := Category.id_comp _
  comm₂ := by
    rw [← Functor.whiskerRight_comp]
    exact congrArg (fun k : Q₁.extension ⟶ X.O ↦
      Functor.whiskerRight k.hom (forget CommRingCat.{max u v w})) h.reduction_comm
  isLocallySurjective :=
    haveI : Presheaf.IsLocallySurjective X.J
        (Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w})) :=
      (Presheaf.isLocallySurjective_iff_whisker_forget X.J Q₁.reduction.hom).mp
        Q₁.locallySurjective
    Stacks.SheafOfModules.isLocallySurjective_presentation_of_isLocallySurjective X.J _ X.O _ _ _

/-- For the pair datum of a morphism of solutions, the second lift is the first followed by the
morphism. -/
theorem ofHom_lift₂ (h : CompatibleFirstOrderThickening.Hom Q₁ Q₂) :
    (ofHom h).lift₂ = (ofHom h).lift₁ ≫ h.hom := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext X.J _ Q₂.extension _ ?_ ?_
  · rw [Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc, ← Category.assoc,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc, h.baseMap_comm]
  · rw [Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc, Functor.map_comp,
      Functor.whiskerRight_comp, ← Category.assoc,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc]
    exact (Category.id_comp _).symm

/-- The difference datum of the pair datum of a morphism of solutions vanishes. -/
theorem ofHom_difference_app (h : CompatibleFirstOrderThickening.Hom Q₁ Q₂) {U : X.Cᵒᵖ}
    (p : kernelIdeal (ofHom h).restrictedPresentation.hom U) :
    (ofHom h).difference.app U p = 0 := by
  let g := liftSection Q₁ (ofHom h).generatorsMap (ofHom h).β₁ (ofHom h).β₁_comp_reduction p
  have h₁ : Q₁.incl g = (ofHom h).lift₁.hom.app U p := incl_liftSection _ _ _ _ p
  refine ((ofHom h).difference_app_eq p g g h₁ ?_).trans (sub_self g)
  refine (h.kernel_comm U g).symm.trans ?_
  rw [h₁, ofHom_lift₂]
  rfl

/-- The difference map of the pair datum of a morphism of solutions vanishes. -/
theorem ofHom_conormalMap (h : CompatibleFirstOrderThickening.Hom Q₁ Q₂) :
    (ofHom h).conormalMap = 0 := by
  refine Stacks.Sites.Conormal.conormal_hom_ext (ofHom h).presentation (targetG S)
    fun U x ↦ ?_
  refine (Stacks.Sites.Conormal.conormalDesc_conormalClass (ofHom h).presentation (targetG S)
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
    (freeAlgebraSheafCoefficientMap X.J _ (ofHom h).E) (ofHom h).descendedDifference U
    x).trans ?_
  exact (Stacks.Sites.Conormal.IdealRestriction.descend_app_eq_zero (ofHom h).difference _
    (fun _ k ↦ ofHom_difference_app h k) x).trans rfl

variable [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)]

/-- The obstruction class of the pair datum of a morphism of solutions vanishes. -/
theorem ofHom_obstruction (h : CompatibleFirstOrderThickening.Hom Q₁ Q₂) :
    (ofHom h).obstruction = 0 := by
  have hc : (ofHom h).extClass = 0 :=
    (Stacks.SheafOfModules.presentationConormalExtClass_eq_zero_iff X.J _ X.O _ _ _ _ _).2
      ⟨0, by rw [Limits.comp_zero, ofHom_conormalMap]⟩
  rw [obstruction, hc, Limits.comp_zero]

/-! ### A trivialization of the class gives a morphism of solutions -/

section Realization

variable (d : PairDatum Q₁ Q₂)
  (θ : (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max u v w, w} X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage d.E
      d.generatorsMap).X₂ ⟶ targetG S)

/-- The `f⁻¹𝒪_B`-derivation `f⁻¹𝒪_B[ℰ] ⟶ G` of a homomorphism `θ` out of the degree `0` term of
`NL(α)`: `y ↦ θ(1 ⊗ dy)`. -/
noncomputable def thetaDerivation {U : X.Cᵒᵖ}
    (y : (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
      d.E).obj.obj U) : (targetG S).val.obj U :=
  θ.val.app U (Stacks.Sites.Conormal.tensorDifferential.{v, u, max u v w, w} X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
    (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) d.E) X.O
    (freeAlgebraSheafCoefficientMap X.J _ d.E) d.presentation U y)

omit [HasDerivedCategory (Sheaf.targetModules X.J X.O)] in
/-- The derivation of `θ` is additive. -/
theorem thetaDerivation_add {U : X.Cᵒᵖ}
    (x y : (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
      d.E).obj.obj U) :
    thetaDerivation d θ (x + y) = thetaDerivation d θ x + thetaDerivation d θ y := by
  rw [thetaDerivation, Stacks.Sites.Conormal.tensorDifferential_add, map_add]
  rfl

/-- The derivation of `θ` vanishes at `0`. -/
theorem thetaDerivation_map_zero {U : X.Cᵒᵖ} :
    thetaDerivation d θ (0 : (freeAlgebraSheaf X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) d.E).obj.obj U) = 0 := by
  have h := thetaDerivation_add d θ (U := U) 0 0
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

omit [HasDerivedCategory (Sheaf.targetModules X.J X.O)] in
/-- The derivation of `θ` vanishes on the coefficients `f⁻¹𝒪_B`. -/
theorem thetaDerivation_coefficient {U : X.Cᵒᵖ}
    (r : ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O).obj.obj U) :
    thetaDerivation d θ ((freeAlgebraSheafCoefficientMap X.J _ d.E).hom.app U r) = 0 := by
  rw [thetaDerivation, Stacks.Sites.Conormal.tensorDifferential_coefficient, map_zero]

omit [HasDerivedCategory (Sheaf.targetModules X.J X.O)] in
/-- The derivation of `θ` satisfies the Leibniz rule, with scalars acting through the
presentation. -/
theorem thetaDerivation_mul {U : X.Cᵒᵖ}
    (x y : (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
      d.E).obj.obj U) :
    thetaDerivation d θ (x * y) =
      toRingSection X.J ((d.presentation.hom.app U).hom x) • thetaDerivation d θ y +
        toRingSection X.J ((d.presentation.hom.app U).hom y) • thetaDerivation d θ x := by
  rw [thetaDerivation, Stacks.Sites.Conormal.tensorDifferential_mul, map_add, map_smul,
    map_smul]
  rfl

omit [HasDerivedCategory (Sheaf.targetModules X.J X.O)] in
/-- The derivation of `θ` commutes with the restriction maps of the site. -/
theorem thetaDerivation_map {U V : X.Cᵒᵖ} (g : U ⟶ V)
    (y : (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
      d.E).obj.obj U) :
    thetaDerivation d θ ((freeAlgebraSheaf X.J _ d.E).obj.map g y) =
      S.G.val.map g (thetaDerivation d θ y) := by
  rw [thetaDerivation, Stacks.Sites.Conormal.tensorDifferential_map]
  exact PresheafOfModules.naturality_apply θ.val g _

variable {d θ}
  (hθ : (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max u v w, w} X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage d.E
      d.generatorsMap).f ≫ θ = d.conormalMap)

omit [HasDerivedCategory (Sheaf.targetModules X.J X.O)] in
include hθ in
/-- **On `ℐ'` the derivation of a trivialization `θ` of `D̄₁₂` is the difference of the two
lifts**: if `φ₁(p)` and `φ₂(p)` are the inclusions of `g₁` and `g₂`, the derivation takes the
value `g₂ - g₁` on the image of `p` in `f⁻¹𝒪_B[ℰ]`. -/
theorem thetaDerivation_baseChange {U : X.Cᵒᵖ}
    (p : kernelIdeal d.restrictedPresentation.hom U) (g₁ g₂ : S.G.val.obj U)
    (h₁ : Q₁.incl g₁ = d.lift₁.hom.app U p) (h₂ : Q₂.incl g₂ = d.lift₂.hom.app U p) :
    thetaDerivation d θ ((baseChange X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app U p) =
      g₂ - g₁ := by
  have h := d.conormalMap_conormalClass p g₁ g₂ h₁ h₂
  have hf := Stacks.Sites.Conormal.conormalSequence_f_class.{v, u, max u v w, w} X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
    (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) d.E) X.O
    (freeAlgebraSheafCoefficientMap X.J _ d.E) d.presentation U
    ⟨(baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction)
      d.E).hom.app U p, p.2⟩
  exact (congrArg (θ.val.app U) hf.symm).trans
    ((congrArg (fun m : (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max u v w, w}
      X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage d.E
        d.generatorsMap).X₁ ⟶ targetG S ↦ m.val.app U _) hθ).trans h)

omit [HasDerivedCategory (Sheaf.targetModules X.J X.O)] in
variable (d θ) in
/-- The second lift followed by the reduction is the presentation, read on sections. -/
theorem reduction_lift₂_apply {U : X.Cᵒᵖ}
    (x : (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj
      S.baseExtension) d.E).obj.obj U) :
    Q₂.reduction.hom.app U (d.lift₂.hom.app U x) =
      d.presentation.hom.app U ((baseChange X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app U x) :=
  congrArg (fun t : freeAlgebraSheaf X.J _ d.E ⟶ X.O ↦ t.hom.app U x)
    (desc_comp_reduction Q₂ d.generatorsMap d.β₂ d.β₂_comp_reduction)

variable (d θ) in
/-- The homomorphism `f⁻¹𝒪_{B'}[ℰ] ⟶ 𝒪'₂`, `x ↦ φ₂(x) − D(x)`, where `D` is the derivation of
`θ` read on the image of `x` in `f⁻¹𝒪_B[ℰ]`. -/
noncomputable def thetaLift :
    freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) d.E ⟶
      Q₂.extension :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom
        { toFun x := d.lift₂.hom.app U x - Q₂.incl (thetaDerivation d θ ((baseChange X.J
            ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app U x))
          map_one' := by
            have h1 : (baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map
                S.baseReduction) d.E).hom.app U 1 =
                (freeAlgebraSheafCoefficientMap X.J _ d.E).hom.app U 1 := by
              rw [map_one, map_one]
            rw [h1, thetaDerivation_coefficient, Q₂.incl_zero, sub_zero, map_one]
          map_mul' x y := by
            have hx : d.lift₂.hom.app U x * Q₂.incl (thetaDerivation d θ ((baseChange X.J
                ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app
                  U y)) = Q₂.incl (toRingSection X.J (d.presentation.hom.app U ((baseChange X.J
                ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app
                  U x)) • thetaDerivation d θ ((baseChange X.J
                ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app
                  U y)) :=
              (Q₂.mul_incl _ _).trans (congrArg (fun s : X.O.obj.obj U ↦ Q₂.incl
                ((show ((sheafCompose X.J (forget₂ CommRingCat.{max u v w}
                  RingCat.{max u v w})).obj X.O).obj.obj U from s) •
                  (show S.G.val.obj U from thetaDerivation d θ ((baseChange X.J
                    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction)
                      d.E).hom.app U y)))) (reduction_lift₂_apply d x))
            have hy : d.lift₂.hom.app U y * Q₂.incl (thetaDerivation d θ ((baseChange X.J
                ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app
                  U x)) = Q₂.incl (toRingSection X.J (d.presentation.hom.app U ((baseChange X.J
                ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app
                  U y)) • thetaDerivation d θ ((baseChange X.J
                ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app
                  U x)) :=
              (Q₂.mul_incl _ _).trans (congrArg (fun s : X.O.obj.obj U ↦ Q₂.incl
                ((show ((sheafCompose X.J (forget₂ CommRingCat.{max u v w}
                  RingCat.{max u v w})).obj X.O).obj.obj U from s) •
                  (show S.G.val.obj U from thetaDerivation d θ ((baseChange X.J
                    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction)
                      d.E).hom.app U x)))) (reduction_lift₂_apply d y))
            have h0 := Q₂.incl_mul_incl (thetaDerivation d θ ((baseChange X.J
                ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app
                  U x)) (thetaDerivation d θ ((baseChange X.J
                ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app
                  U y))
            rw [map_mul, map_mul, thetaDerivation_mul, Q₂.incl_add, ← hx, ← hy]
            linear_combination -h0
          map_zero' := by rw [map_zero, map_zero, thetaDerivation_map_zero, Q₂.incl_zero, sub_zero]
          map_add' x y := by
            rw [map_add, map_add, thetaDerivation_add, Q₂.incl_add]
            abel }
      naturality {U V} g := by
        refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
        change d.lift₂.hom.app V ((freeAlgebraSheaf X.J _ d.E).obj.map g x) -
            Q₂.incl (thetaDerivation d θ ((baseChange X.J
            ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app V
              ((freeAlgebraSheaf X.J _ d.E).obj.map g x))) =
          Q₂.extension.obj.map g (d.lift₂.hom.app U x - Q₂.incl (thetaDerivation d θ
            ((baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map
              S.baseReduction) d.E).hom.app U x)))
        rw [map_sub, sheafHom_naturality_apply X.J d.lift₂, sheafHom_naturality_apply X.J,
          thetaDerivation_map, Q₂.incl_naturality] }

variable (d θ) in
/-- The homomorphism `x ↦ φ₂(x) − D(x)` lies over the presentation. -/
theorem thetaLift_comp_reduction : thetaLift d θ ≫ Q₂.reduction = d.restrictedPresentation := by
  refine sheafHom_ext X.J fun U x ↦ ?_
  change Q₂.reduction.hom.app U (d.lift₂.hom.app U x - Q₂.incl _) = _
  rw [map_sub, Q₂.reduction_incl, sub_zero, reduction_lift₂_apply]
  rfl

omit [HasDerivedCategory (Sheaf.targetModules X.J X.O)] in
variable (d) in
/-- A local section of `f⁻¹𝒪_{B'}[ℰ]` whose first lift is killed by the reduction lies in
`ℐ'`. -/
theorem mem_kernelIdeal_of_reduction_lift₁ {U : X.Cᵒᵖ}
    (x : (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj
      S.baseExtension) d.E).obj.obj U)
    (hx : Q₁.reduction.hom.app U (d.lift₁.hom.app U x) = 0) :
    x ∈ kernelIdeal d.restrictedPresentation.hom U :=
  (congrArg (fun t : freeAlgebraSheaf X.J _ d.E ⟶ X.O ↦ t.hom.app U x)
    (desc_comp_reduction Q₁ d.generatorsMap d.β₁ d.β₁_comp_reduction)).symm.trans hx

include hθ in
/-- **On `ℐ'` the homomorphism `x ↦ φ₂(x) − D(x)` is the first lift, read in `G`**: if `φ₁(p)` is
the inclusion of `g₁`, then `p` goes to the inclusion of `g₁` in `𝒪'₂`. -/
theorem thetaLift_app_eq_incl {U : X.Cᵒᵖ} (p : kernelIdeal d.restrictedPresentation.hom U)
    (g₁ : S.G.val.obj U) (h₁ : Q₁.incl g₁ = d.lift₁.hom.app U p) :
    (thetaLift d θ).hom.app U p = Q₂.incl g₁ := by
  let g₂ := liftSection Q₂ d.generatorsMap d.β₂ d.β₂_comp_reduction p
  have h₂ : Q₂.incl g₂ = d.lift₂.hom.app U p := incl_liftSection _ _ _ _ p
  change d.lift₂.hom.app U p - Q₂.incl (thetaDerivation d θ _) = Q₂.incl g₁
  rw [thetaDerivation_baseChange hθ p g₁ g₂ h₁ h₂, ← h₂]
  have h := Q₂.incl_add (g₂ - g₁) g₁
  rw [sub_add_cancel] at h
  rw [h]
  abel

include hθ in
/-- The homomorphism `x ↦ φ₂(x) − D(x)` kills the kernel of the first lift. -/
theorem thetaLift_app_eq_zero (U : X.Cᵒᵖ)
    (x : (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj
      S.baseExtension) d.E).obj.obj U)
    (hx : d.lift₁.hom.app U x = 0) : (thetaLift d θ).hom.app U x = 0 := by
  have hmem := mem_kernelIdeal_of_reduction_lift₁ d x (by rw [hx, map_zero])
  exact (thetaLift_app_eq_incl hθ ⟨x, hmem⟩ 0 (Q₁.incl_zero.trans hx.symm)).trans Q₂.incl_zero

variable [Presheaf.IsLocallySurjective X.J d.lift₁.hom]

/-- **The morphism of solutions attached to a trivialization `θ` of the class of `D̄₁₂`**: the
homomorphism `x ↦ φ₂(x) − D(x)` descends along the locally surjective first lift. -/
noncomputable def homOfTrivialization : CompatibleFirstOrderThickening.Hom Q₁ Q₂ where
  hom := Sheaf.descendRingHom d.lift₁ (thetaLift d θ) (thetaLift_app_eq_zero hθ)
  reduction_comm := by
    refine Sheaf.hom_ext_of_isLocallySurjective d.lift₁ ?_
    rw [← Category.assoc, Sheaf.descendRingHom_comp, thetaLift_comp_reduction,
      desc_comp_reduction Q₁ d.generatorsMap d.β₁ d.β₁_comp_reduction]
  baseMap_comm := by
    rw [← Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc X.J _ Q₁.extension
      d.E Q₁.baseMap d.β₁, Category.assoc, Sheaf.descendRingHom_comp]
    refine sheafHom_ext X.J fun U a ↦ ?_
    change d.lift₂.hom.app U ((freeAlgebraSheafCoefficientMap X.J _ d.E).hom.app U a) -
      Q₂.incl (thetaDerivation d θ ((baseChange X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E).hom.app U
          ((freeAlgebraSheafCoefficientMap X.J _ d.E).hom.app U a))) = Q₂.baseMap.hom.app U a
    have hc := congrArg (fun t ↦ t.hom.app U a)
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_baseChange X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E)
    have hb := congrArg (fun t ↦ t.hom.app U a)
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc X.J _ Q₂.extension
        d.E Q₂.baseMap d.β₂)
    change (baseChange X.J _ d.E).hom.app U ((freeAlgebraSheafCoefficientMap X.J _ d.E).hom.app
      U a) = (freeAlgebraSheafCoefficientMap X.J _ d.E).hom.app U
        (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U a) at hc
    change d.lift₂.hom.app U ((freeAlgebraSheafCoefficientMap X.J _ d.E).hom.app U a) =
      Q₂.baseMap.hom.app U a at hb
    rw [hc, thetaDerivation_coefficient, Q₂.incl_zero, sub_zero, hb]
  kernel_comm U g := by
    have hsep := (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose X.J (forget CommRingCat.{max u v w})).obj Q₂.extension).property
    refine (hsep _ (Presheaf.imageSieve_mem X.J d.lift₁.hom (U := U)
      (Q₁.incl g))).isSeparatedFor.ext fun Y f hf ↦ ?_
    obtain ⟨p₀, hp₀⟩ := hf
    have h₁ : Q₁.incl (show S.G.val.obj (op Y) from S.G.val.map f.op g) =
        d.lift₁.hom.app (op Y) p₀ :=
      (Q₁.incl_naturality f.op g).trans hp₀.symm
    have hmem := mem_kernelIdeal_of_reduction_lift₁ d p₀ (by rw [← h₁, Q₁.reduction_incl])
    change Q₂.extension.obj.map f.op ((Sheaf.descendRingHom d.lift₁ (thetaLift d θ)
        (thetaLift_app_eq_zero hθ)).hom.app U (Q₁.incl g)) =
      Q₂.extension.obj.map f.op (Q₂.incl g)
    rw [← sheafHom_naturality_apply X.J, ← Q₁.incl_naturality, h₁, Sheaf.descendRingHom_apply,
      thetaLift_app_eq_incl hθ ⟨p₀, hmem⟩ _ h₁, Q₂.incl_naturality]

end Realization

end PairDatum

/-! ### The obstruction class separates the solutions -/

/-- The first projection `𝒪'₁ ×_𝒪 𝒪'₂ ⟶ 𝒪'₁` is locally surjective, the second reduction being
so. -/
instance isLocallySurjective_pairFst : Presheaf.IsLocallySurjective X.J (pairFst Q₁ Q₂) where
  imageSieve_mem {U} q := by
    have h₂ := (Presheaf.isLocallySurjective_iff_whisker_forget X.J Q₂.reduction.hom).mp
      Q₂.locallySurjective
    refine X.J.superset_covering ?_ (Presheaf.imageSieve_mem X.J
      (Functor.whiskerRight Q₂.reduction.hom (forget CommRingCat.{max u v w}))
        (Q₁.reduction.hom.app (op U) q))
    rintro V f ⟨q₂, hq₂⟩
    exact ⟨⟨(Q₁.extension.obj.map f.op q, q₂),
      (NatTrans.naturality_apply Q₁.reduction.hom f.op q).trans hq₂.symm⟩, rfl⟩

/-- The first lift of the canonical pair datum is locally surjective. -/
instance isLocallySurjective_pairDatum_lift₁ :
    Presheaf.IsLocallySurjective X.J (pairDatum Q₁ Q₂).lift₁.hom :=
  haveI : Presheaf.IsLocallySurjective X.J (pairDatum Q₁ Q₂).β₁ :=
    isLocallySurjective_pairFst
  (Presheaf.isLocallySurjective_iff_whisker_forget X.J _).mpr
    (Presheaf.isLocallySurjective_of_isLocallySurjective_fac X.J
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc X.J _ Q₁.extension
        (pairDatum Q₁ Q₂).E Q₁.baseMap (pairDatum Q₁ Q₂).β₁))

variable [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)]

variable (Q₁ Q₂) in
/-- **The obstruction class of two solutions vanishes exactly when there is a morphism of
solutions between them**, which is then an isomorphism (`Hom.isIso`). This is the assertion of
[Stacks Project, Tag 08UK] that the class of Step 1 of the proof of
[Stacks Project, Tag 08UG] obstructs the existence of a morphism `𝒪'₁ ⟶ 𝒪'₂` fitting into the
diagram. -/
theorem pairDatumObstruction_eq_zero_iff :
    pairDatumObstruction Q₁ Q₂ = 0 ↔ Nonempty (CompatibleFirstOrderThickening.Hom Q₁ Q₂) := by
  constructor
  · intro h0
    have hc : (pairDatum Q₁ Q₂).extClass = 0 := by
      rw [← PairDatum.Q_map_comparison_comp_obstruction,
        PairDatum.obstruction_eq_pairDatumObstruction, h0, Limits.comp_zero]
    obtain ⟨θ, hθ⟩ :=
      (Stacks.SheafOfModules.presentationConormalExtClass_eq_zero_iff X.J _ X.O _ _ _ _ _).1 hc
    exact ⟨PairDatum.homOfTrivialization hθ⟩
  · rintro ⟨h⟩
    exact (PairDatum.obstruction_eq_pairDatumObstruction (PairDatum.ofHom h)).symm.trans
      (PairDatum.ofHom_obstruction h)

end Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening

namespace Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening

open AlgebraicGeometry (RingedTopos RingedToposHom)

variable {X : RingedTopos.{v, u, max u v}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B}
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, u} X.J X.O)]

/-- **The obstruction class `o(𝒪'₁, 𝒪'₂) ∈ Ext¹_𝒪(NL_f, G)` vanishes exactly when there is a
morphism of solutions `𝒪'₁ ⟶ 𝒪'₂`**, which is then an isomorphism (`Hom.isIso`): the class
obstructs the existence of an isomorphism of solutions, as asserted in
[Stacks Project, Tag 08UK]. -/
theorem pairObstruction_eq_zero_iff (Q₁ Q₂ : S.CompatibleFirstOrderThickening) :
    pairObstruction Q₁ Q₂ = 0 ↔ Nonempty (CompatibleFirstOrderThickening.Hom Q₁ Q₂) :=
  pairDatumObstruction_eq_zero_iff Q₁ Q₂

/-- **The obstruction class separates the isomorphism classes of solutions**: two solutions are
isomorphic exactly when `o(𝒪'₁, 𝒪'₂) = 0`. -/
theorem pairObstruction_eq_zero_iff_isomorphic [X.J.HasSheafCompose (forget CommRingCat.{max u v})]
    [(forget CommRingCat.{max u v}).ReflectsIsomorphisms]
    (Q₁ Q₂ : S.CompatibleFirstOrderThickening) :
    pairObstruction Q₁ Q₂ = 0 ↔ Isomorphic Q₁ Q₂ :=
  (pairObstruction_eq_zero_iff Q₁ Q₂).trans (isomorphic_iff_nonempty_hom Q₁ Q₂).symm

end Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening
