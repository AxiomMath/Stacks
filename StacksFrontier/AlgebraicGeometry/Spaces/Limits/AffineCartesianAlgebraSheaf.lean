module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotient
public import StacksFrontier.RingTheory.SymmetricAlgebra.BaseChangeBijective

/-!
# Sheafifying a presheaf of algebras which is cartesian on affine charts

Let `X` be an algebraic space and `P` a presheaf of commutative `𝒪_X`-algebras on its small étale
site.  Call `P` *cartesian on affine charts* when for every morphism `V ⟶ U` of étale charts with
affine underlying schemes the comparison `𝒪(V) ⊗_{𝒪(U)} P(U) ⟶ P(V)` is bijective.  Then:

* the restriction of `P` to the affine étale charts is a sheaf (flat descent of modules);
* sheafification does not change the sections of `P` over affine charts;
* the sheafification of `P` is a quasi-coherent algebra sheaf.

## Main definitions

* `AlgebraicGeometry.Space.AffineCartesian.IsAffineCartesian`: the cartesian condition.
* `AlgebraicGeometry.Space.AffineCartesian.algebra`: the sheafification of `P`, as an algebra
  sheaf.

## Main results

* `AlgebraicGeometry.Space.AffineCartesian.isIso_toSheafify_app`: the sheafification unit is an
  isomorphism over affine charts.
* `AlgebraicGeometry.Space.AffineCartesian.isQuasicoherent_algebra`: the sheafification is
  quasi-coherent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct Stacks.PresheafOfModules
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

namespace AffineCartesian

variable (P : (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u}) (α : structurePresheaf B S hS F ⟶ P)

/-- `P`, with its algebra structure `α`, read as a presheaf of modules over the structure
presheaf. -/
noncomputable abbrev sectionsModule :=
  algModule (structurePresheaf B S hS F) P α

/-- **`P` is cartesian on affine charts**: for every morphism `V ⟶ U` of étale charts with affine
underlying schemes, the comparison `𝒪(V) ⊗_{𝒪(U)} P(U) ⟶ P(V)` is bijective. -/
def IsAffineCartesian : Prop :=
  ∀ (U V : SmallEtale B S hS F), IsAffine (smallEtaleScheme B S hS F U) →
    IsAffine (smallEtaleScheme B S hS F V) → ∀ f : V ⟶ U,
      Function.Bijective (restrictionBaseChange.{u + 1, u, u, u} (sectionsModule P α) f.op)

variable {P α}

/-- The restriction of `P` to the affine charts, as a presheaf of modules over the chart rings. -/
noncomputable abbrev affineModule :=
  algModule (affineEtaleChartRings B S hS F) ((AffineEtale.inclusion B S hS F).op ⋙ P)
    ((AffineEtale.inclusion B S hS F).op.whiskerLeft α)

/-- If `P` is cartesian on affine charts, then for every morphism `f` of affine étale charts the
comparison map `restrictionBaseChange` of `affineModule` along `f` is an isomorphism. -/
theorem isIso_restrictionBaseChange_affineModule (h : IsAffineCartesian P α)
    {Z W : (AffineEtale B S hS F)ᵒᵖ} (f : Z ⟶ W) :
    IsIso (restrictionBaseChange.{u + 1, u, u, u} (affineModule (α := α)) f) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (h Z.unop.obj W.unop.obj Z.unop.property W.unop.property
      ((AffineEtale.inclusion B S hS F).map f.unop))

/-- **A presheaf of algebras cartesian on affine charts is a sheaf on the affine étale site.** -/
theorem isSheaf_affine (h : IsAffineCartesian P α) :
    Presheaf.IsSheaf (AffineEtale.topology B S hS F) ((AffineEtale.inclusion B S hS F).op ⋙ P) := by
  have hcart : ∀ {Z W : (AffineEtale B S hS F)ᵒᵖ} (f : Z ⟶ W),
      IsIso (restrictionBaseChange.{u + 1, u, u, u + 1}
        ((affineModule (α := α)).uliftSections.{u + 1}) f) := by
    intro Z W f
    exact isIso_restrictionBaseChange_uliftSections.{u + 1, u + 1, u, u, u} _ f
      (isIso_restrictionBaseChange_affineModule h f)
  have hsheaf := isSheaf_of_cartesian_affineEtaleChart.{u, u} B S hS F
    ((affineModule (α := α)).uliftSections.{u + 1}) hcart
  rw [Presheaf.isSheaf_iff_isSheaf_comp (AffineEtale.topology B S hS F) _
    (CategoryTheory.forget AddCommGrpCat.{u + 1})] at hsheaf
  replace hsheaf := (isSheaf_iff_isSheaf_of_type _ _).1 hsheaf
  have e : ((affineModule (α := α)).uliftSections.{u + 1}).presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1} ≅
      (((AffineEtale.inclusion B S hS F).op ⋙ P) ⋙
        CategoryTheory.forget CommRingCat.{u}) ⋙ CategoryTheory.uliftFunctor.{u + 1, u} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  refine Presheaf.isSheaf_of_isSheaf_forget_commRingCat _ _ ?_
  exact (Presieve.isSheaf_comp_uliftFunctor_iff (J := AffineEtale.topology B S hS F)).mp
    (Presieve.isSheaf_iso _ e hsheaf)

/-- **Sheafification does not change the sections of `P` over an affine chart.** -/
theorem isIso_toSheafify_app (hF : IsAlgebraicSpace B S hS F) (h : IsAffineCartesian P α)
    (U : SmallEtale B S hS F) (hU : IsAffine (smallEtaleScheme B S hS F U)) :
    IsIso ((toSheafify (SmallEtale.topology B S hS F) P).app (op U)) :=
  isIso_toSheafify_app_of_isAffine B S hS F hF P (isSheaf_affine h) U hU

/-- Over an affine chart `U`, the component at `U` of the sheafification unit of a presheaf of
algebras cartesian on affine charts is bijective. -/
theorem bijective_toSheafify_app (hF : IsAlgebraicSpace B S hS F) (h : IsAffineCartesian P α)
    (U : SmallEtale B S hS F) (hU : IsAffine (smallEtaleScheme B S hS F U)) :
    Function.Bijective ((toSheafify (SmallEtale.topology B S hS F) P).app (op U)) :=
  have := isIso_toSheafify_app hF h U hU
  ConcreteCategory.bijective_of_isIso _

variable (hF : IsAlgebraicSpace B S hS F) (P α)

/-- **The sheafification of `P`, as an algebra sheaf.** -/
noncomputable def algebra : AlgebraSheaf.{u, u} B S hS F hF :=
  AlgebraSheaf.ofHom (⟨α ≫ toSheafify _ P⟩ :
    structureSheaf B S hS F hF ⟶ (presheafToSheaf (SmallEtale.topology B S hS F) _).obj P)

/-- The structure map of `algebra P α hF` at `U` sends `r` to the image of `α r` under the
sheafification unit. -/
theorem algebra_algebraMap (U : (SmallEtale B S hS F)ᵒᵖ)
    (r : (structurePresheaf B S hS F).obj U) :
    (algebra P α hF).algebraMap U r = (toSheafify _ P).app U (α.app U r) :=
  rfl

variable {P α}

/-- **The sheafification of a presheaf of algebras cartesian on affine charts is cartesian on
affine charts.** -/
theorem bijective_restrictionBaseChange_algebra (h : IsAffineCartesian P α)
    {U V : SmallEtale B S hS F} (hU : IsAffine (smallEtaleScheme B S hS F U))
    (hV : IsAffine (smallEtaleScheme B S hS F V)) (f : V ⟶ U) :
    Function.Bijective (restrictionBaseChange.{u + 1, u, u, u}
      (R := structurePresheaf B S hS F) (AlgebraSheaf.underlyingModule (algebra P α hF)).val
        f.op) := by
  let R := structurePresheaf B S hS F ⋙ forget₂ CommRingCat.{u} RingCat.{u}
  let : Algebra (R.obj (op U)) (R.obj (op V)) := (R.map f.op).hom.toAlgebra
  have hUb := bijective_toSheafify_app hF h U hU
  have hVb := bijective_toSheafify_app hF h V hV
  let uU := (toSheafify (SmallEtale.topology B S hS F) P).app (op U)
  let uV := (toSheafify (SmallEtale.topology B S hS F) P).app (op V)
  let Q : PresheafOfModules.{u} R := (AlgebraSheaf.underlyingModule (algebra P α hF)).val
  let e : (sectionsModule P α).obj (op U) ≃ₗ[R.obj (op U)] Q.obj (op U) :=
    LinearEquiv.ofBijective
      ({ toFun := fun x => uU x
         map_add' := fun x y => map_add uU.hom x y
         map_smul' := by
           intro r (x : P.obj (op U))
           change uU (α.app (op U) r * x) =
             (toSheafify (SmallEtale.topology B S hS F) P).app (op U) (α.app (op U) r) * uU x
           exact map_mul uU.hom _ x } :
        (sectionsModule P α).obj (op U) →ₗ[R.obj (op U)] Q.obj (op U))
      hUb
  let e' : (sectionsModule P α).obj (op V) ≃+ Q.obj (op V) :=
    AddEquiv.ofBijective uV.hom.toAddMonoidHom hVb
  refine TensorProduct.bijective_of_bijective_of_equiv (R' := R.obj (op V)) e e'
    (restrictionBaseChange.{u + 1, u, u, u} (sectionsModule P α) f.op).hom.toAddMonoidHom
    (h U V hU hV f)
    (restrictionBaseChange.{u + 1, u, u, u} (R := structurePresheaf B S hS F) Q
      f.op).hom.toAddMonoidHom
    fun b p => ?_
  have h1 := restrictionBaseChange_tmul.{u + 1, u, u, u} (R := structurePresheaf B S hS F) Q
    f.op b (e p)
  have h2 := restrictionBaseChange_tmul.{u + 1, u, u, u} (sectionsModule P α) f.op b p
  refine h1.trans (Eq.trans ?_ (congrArg uV h2).symm)
  change uV (α.app (op V) b) *
      ((presheafToSheaf (SmallEtale.topology B S hS F) _).obj P).obj.map f.op (uU p) =
    uV (α.app (op V) b * P.map f.op p)
  rw [map_mul]
  congr 1
  exact (ConcreteCategory.congr_hom
    ((toSheafify (SmallEtale.topology B S hS F) P).naturality f.op) p).symm

/-- **The sheafification of a presheaf of algebras cartesian on affine charts is
quasi-coherent.** -/
theorem isQuasicoherent_algebra (h : IsAffineCartesian P α) :
    (algebra P α hF).IsQuasicoherent := by
  refine (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS F hF _).mpr ?_
  intro U V hU hV f
  have hb := bijective_restrictionBaseChange_algebra hF h hU hV f
  have _ := chartAlgebra (hF := hF) f
  have _ := chartSectionsModule (AlgebraSheaf.underlyingModule (algebra P α hF)) f
  have key : ∀ z, sectionsBaseChange (AlgebraSheaf.underlyingModule (algebra P α hF)) f z =
      restrictionBaseChange.{u + 1, u, u, u} (R := structurePresheaf B S hS F)
        (AlgebraSheaf.underlyingModule (algebra P α hF)).val f.op z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      exact ((map_add _ x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add _ x y).symm
    | tmul b x =>
      refine (chartBaseChange_tmul _ f b x).trans ?_
      exact (restrictionBaseChange_tmul _ f.op b x).symm
  rw [show (sectionsBaseChange (AlgebraSheaf.underlyingModule (algebra P α hF)) f : _ → _) = _
    from funext key]
  exact hb

/-! ### Morphisms out of the sheafification -/

section Hom

variable {𝒜 : AlgebraSheaf.{u, u} B S hS F hF}

/-- The morphism of algebra sheaves out of the sheafification of `P` induced by a morphism of
presheaves of rings `η : P ⟶ 𝒜` compatible with the structure maps. -/
noncomputable def lift (η : P ⟶ 𝒜.right.obj) (hη : α ≫ η = 𝒜.hom.hom) :
    algebra P α hF ⟶ 𝒜 where
  right := ⟨sheafifyLift (SmallEtale.topology B S hS F) η 𝒜.right.property⟩
  comm U r :=
    (ConcreteCategory.congr_hom (congrArg (fun k => k.app U)
      (toSheafify_sheafifyLift (SmallEtale.topology B S hS F) η 𝒜.right.property)) _).trans
      (ConcreteCategory.congr_hom (congrArg (fun k => k.app U) hη) r)

/-- The morphism `lift hF η hη` sends the image of a section `x` of `P` under the sheafification
unit to `η x`. -/
theorem lift_app_toSheafify (η : P ⟶ 𝒜.right.obj) (hη : α ≫ η = 𝒜.hom.hom)
    (U : (SmallEtale B S hS F)ᵒᵖ) (x : P.obj U) :
    (lift hF η hη).right.hom.app U ((toSheafify (SmallEtale.topology B S hS F) P).app U x) =
      η.app U x :=
  ConcreteCategory.congr_hom (congrArg (fun k => k.app U)
    (toSheafify_sheafifyLift (SmallEtale.topology B S hS F) η 𝒜.right.property)) x

/-- Morphisms out of the sheafification of `P` agree as soon as they agree on the image of `P`. -/
theorem hom_ext {g g' : algebra P α hF ⟶ 𝒜}
    (h : ∀ (U : (SmallEtale B S hS F)ᵒᵖ) (x : P.obj U),
      g.right.hom.app U ((toSheafify (SmallEtale.topology B S hS F) P).app U x) =
        g'.right.hom.app U ((toSheafify (SmallEtale.topology B S hS F) P).app U x)) :
    g = g' := by
  refine AlgebraSheaf.Hom.ext (Sheaf.hom_ext ?_)
  refine sheafify_hom_ext _ _ _ 𝒜.right.property ?_
  exact NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext fun x => h U x))

variable {P' : (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u}} {α' : structurePresheaf B S hS F ⟶ P'}

/-- The morphism of sheafifications induced by a morphism of presheaves of algebras. -/
noncomputable def map (η : P ⟶ P') (hη : α ≫ η = α') : algebra P α hF ⟶ algebra P' α' hF :=
  lift hF (η ≫ toSheafify (SmallEtale.topology B S hS F) P')
    (by
      change α ≫ η ≫ toSheafify (SmallEtale.topology B S hS F) P' =
        α' ≫ toSheafify (SmallEtale.topology B S hS F) P'
      rw [← Category.assoc, hη])

/-- The morphism `map hF η hη` sends the image of a section `x` of `P` under the sheafification
unit to the image of `η x` under the sheafification unit of `P'`. -/
theorem map_app_toSheafify (η : P ⟶ P') (hη : α ≫ η = α') (U : (SmallEtale B S hS F)ᵒᵖ)
    (x : P.obj U) :
    (map hF η hη).right.hom.app U ((toSheafify (SmallEtale.topology B S hS F) P).app U x) =
      (toSheafify (SmallEtale.topology B S hS F) P').app U (η.app U x) :=
  lift_app_toSheafify (𝒜 := algebra P' α' hF) hF _ _ U x

end Hom

end AffineCartesian

end AlgebraicGeometry.Space

end
