module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialCechComplex
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseRing
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapCommutesWithDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage

/-!
# Base change of the Čech complexes of differential forms, compatibly with `d`

Let `X ⟶ Spec A` be separated with a finite covering `U` by affine opens, and let
`X' = X ×_{Spec A} Spec A'` be its base change along `A ⟶ A'`, covered by the preimages `U'`.
The alternating Čech complex of `Ω^p_{X'/A'}` for `U'` is the base change of the alternating Čech
complex of `Ω^p_{X/A}` for `U` ([Stacks, Tag 0FL5] and the base change of Čech complexes of
quasi-coherent modules), and under this identification the de Rham differential of `X'` is the
base change of that of `X`: the pullback of forms commutes with `d`.

## Main definitions

* `Stacks.Cech.formsCechBaseChangeIso`: the identification.

## Main results

* `Stacks.Cech.formsCechBaseChangeIso_comm`: compatibility with the de Rham differentials.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.Cech

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') {X X' : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (g : X' ⟶ X)
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  {I : Type u} [Finite I] [IsSeparated f] (U : I → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i))

/-- **The alternating Čech complex of `Ω^p_{X'/A'}` is the base change of that of `Ω^p_{X/A}`.** -/
def formsCechBaseChangeIso (p : ℕ) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))) ≅
      alternatingCechModuleComplex f' (fun i => g ⁻¹ᵁ U i)
        (f'.relativeDifferentialForms (p : ℤ)) :=
  haveI := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  haveI := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback g f f'
    (Spec.map (CommRingCat.ofHom φ)) hsq (p : ℤ)
  alternatingCechModuleComplexBaseChangeIso g U (fun i => g ⁻¹ᵁ U i) (Equiv.refl I)
      (f.relativeDifferentialForms (p : ℤ)) (fun _ => rfl) φ f f'
      (baseRingHom_comp_app φ f f' g hsq) hsq hUaff ≪≫
    alternatingCechModuleComplexMapIso f' (fun i => g ⁻¹ᵁ U i)
      (asIso (Scheme.Hom.relativeDifferentialFormsMap g f f' (Spec.map (CommRingCat.ofHom φ))
        hsq.w (p : ℤ)))


/-- **`formsCechBaseChangeIso` on the generators `1 ⊗ t`**: tuplewise, it pulls the form back,
restricts it to the intersection of the preimages, and applies the comparison of Tag 0FL5. -/
theorem formsCechBaseChangeIso_hom_one_tmul (p n : ℕ)
    (t : alternatingCechModuleObj f U (f.relativeDifferentialForms (p : ℤ)) n)
    (i : Fin (n + 1) → I) :
    (((formsCechBaseChangeIso φ f f' g hsq U hUaff p).hom.f n) ((1 : A') ⊗ₜ[A] t)).1 i =
      (Scheme.Hom.relativeDifferentialFormsMap g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w
          (p : ℤ)).app (CechCochains.inter (fun i => g ⁻¹ᵁ U i) i)
        (CechCochains.restr ((Scheme.Modules.pullback g).obj
            (f.relativeDifferentialForms (p : ℤ))).presheaf
          (inter_eq_preimage g U (fun i => g ⁻¹ᵁ U i) (Equiv.refl I) (fun _ => rfl) i).le
          (pullbackSections g (f.relativeDifferentialForms (p : ℤ)) (CechCochains.inter U i)
            (t.1 i))) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback g f f'
    (Spec.map (CommRingCat.ofHom φ)) hsq (p : ℤ)
  have hbc := alternatingCechModuleObjBaseChangeIso_hom_one_tmul g U (fun i => g ⁻¹ᵁ U i)
    (Equiv.refl I) (f.relativeDifferentialForms (p : ℤ)) (fun _ => rfl) φ f f'
    (baseRingHom_comp_app φ f f' g hsq) hsq hUaff n t
  show ((alternatingCechModuleObjMap f' (fun i => g ⁻¹ᵁ U i)
      (Scheme.Hom.relativeDifferentialFormsMap g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w
        (p : ℤ)) n)
      ((alternatingCechModuleObjBaseChangeIso g U (fun i => g ⁻¹ᵁ U i) (Equiv.refl I)
        (f.relativeDifferentialForms (p : ℤ)) (fun _ => rfl) φ f f'
        (baseRingHom_comp_app φ f f' g hsq) hsq hUaff n).hom ((1 : A') ⊗ₜ[A] t))).1 i = _
  rw [hbc]
  rfl

omit [IsSeparated f] in
include hsq in
/-- **Pulling back a form, restricting and applying the comparison of Tag 0FL5 commutes with the
de Rham differential**: the tuplewise content of `formsCechBaseChangeIso_comm`. -/
theorem relativeDifferentialFormsMap_restr_pullbackSections_d (p : ℕ) {V : X.Opens}
    {W' : X'.Opens} (hW : W' ≤ g ⁻¹ᵁ V) (x : Γ(f.relativeDifferentialForms (p : ℤ), V)) :
    (Scheme.Hom.relativeDifferentialFormsMap g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w
        ((p + 1 : ℕ) : ℤ)).app W'
      (CechCochains.restr ((Scheme.Modules.pullback g).obj
          (f.relativeDifferentialForms ((p + 1 : ℕ) : ℤ))).presheaf hW
        (pullbackSections g (f.relativeDifferentialForms ((p + 1 : ℕ) : ℤ)) V
          ((Scheme.Hom.deRhamPresheafD f p).app (op V) x))) =
      (Scheme.Hom.deRhamPresheafD f' p).app (op W')
        ((Scheme.Hom.relativeDifferentialFormsMap g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w
            (p : ℤ)).app W'
          (CechCochains.restr ((Scheme.Modules.pullback g).obj
              (f.relativeDifferentialForms (p : ℤ))).presheaf hW
            (pullbackSections g (f.relativeDifferentialForms (p : ℤ)) V x))) := by
  have h := fun (q : ℤ) (y : Γ(f.relativeDifferentialForms q, V)) =>
    (Stacks.Cohomology.CechOne.restr_app (Scheme.Modules.Hom.mapPresheaf
      (Scheme.Hom.relativeDifferentialFormsMap g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w q))
        hW (pullbackSections g (f.relativeDifferentialForms q) V y)).symm
  have h3 := Stacks.Cohomology.CechOne.restr_app (Scheme.Hom.deRhamPresheafD f' p) hW
    (Scheme.Hom.relativeDifferentialFormsPullback g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w
      (p : ℤ) V x)
  have h4 := Scheme.Hom.deRhamComplex_d_relativeDifferentialFormsPullback g f f'
    (Spec.map (CommRingCat.ofHom φ)) hsq.w p V x
  refine (h _ _).trans (Eq.trans ?_ (congrArg ((Scheme.Hom.deRhamPresheafD f' p).app (op W'))
    (h p x)).symm)
  refine Eq.trans ?_ h3
  exact congrArg _ h4.symm

include hUaff in
/-- **The identification of `formsCechBaseChangeIso` intertwines the de Rham differentials**: the
de Rham differential of `X'` on the Čech complex of `U'` is the base change of that of `X` on the
Čech complex of `U`. -/
theorem formsCechBaseChangeIso_comm (p : ℕ) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (alternatingCechModulePush f U (Scheme.Hom.deRhamPresheafD f p)
          (Scheme.Hom.deRhamPresheafD_app_smul f p)) ≫
      (formsCechBaseChangeIso φ f f' g hsq U hUaff (p + 1)).hom =
    (formsCechBaseChangeIso φ f f' g hsq U hUaff p).hom ≫
      alternatingCechModulePush f' (fun i => g ⁻¹ᵁ U i) (Scheme.Hom.deRhamPresheafD f' p)
        (Scheme.Hom.deRhamPresheafD_app_smul f' p) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f (p + 1)
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.ExtendScalars.hom_ext fun s => ?_
  refine Subtype.ext (funext fun i => ?_)
  have hL := formsCechBaseChangeIso_hom_one_tmul φ f f' g hsq U hUaff (p + 1) n
    ((alternatingCechModulePush f U (Scheme.Hom.deRhamPresheafD f p)
      (Scheme.Hom.deRhamPresheafD_app_smul f p)).f n s) i
  have hR := formsCechBaseChangeIso_hom_one_tmul φ f f' g hsq U hUaff p n s i
  show (((formsCechBaseChangeIso φ f f' g hsq U hUaff (p + 1)).hom.f n)
      ((1 : A') ⊗ₜ[A] ((alternatingCechModulePush f U (Scheme.Hom.deRhamPresheafD f p)
        (Scheme.Hom.deRhamPresheafD_app_smul f p)).f n s))).1 i =
    (Scheme.Hom.deRhamPresheafD f' p).app (op (CechCochains.inter (fun i => g ⁻¹ᵁ U i) i))
      ((((formsCechBaseChangeIso φ f f' g hsq U hUaff p).hom.f n) ((1 : A') ⊗ₜ[A] s)).1 i)
  rw [hL, hR]
  exact relativeDifferentialFormsMap_restr_pullbackSections_d φ f f' g hsq p _ (s.1 i)

end Stacks.Cech

