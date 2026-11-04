module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.FibreIdealIso
public import StacksFrontier.Deformation.ToposThickening.SolutionHomOfUniversal

/-!
# Solutions of `problem g` restricted along an isomorphism `ρ : X ≅ X₀`

For an isomorphism `ρ : X ≅ X₀` of algebraic spaces and `g : X₀ ⟶ Y`, a solution `𝒪'` of the
extension problem `problem g` (on the small étale site of `X₀`) restricts along `ρ` to a solution
of `problem (ρ ≫ g)` (on the small étale site of `X`): the middle term is the restriction of `𝒪'`,
its thickened base is identified with `(ρ ≫ g)⁻¹t⁻¹𝒪_{Y'}` through `fibreRingIso`, and its kernel,
the restriction of `g^*𝒞_{Y/Y'}`, is identified with `(ρ ≫ g)^*𝒞_{Y/Y'}` through the map it
receives from the base ideal, which is universal because the corresponding map of `𝒪'` is
(`CategoryTheory.bijective_comp_map_of_transport`).

## Main definitions
* `AlgebraicGeometry.Space.FlatThickeningDeformation.fibreRestriction`: the restricted
  extension.
* `AlgebraicGeometry.Space.FlatThickeningDeformation.fibreSolution`: the restricted solution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback
open Deformation.ToposThickening

universe u v w

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

/-- A cancellation in a category, used to identify the structure map of the restricted
extension: if `red ≫ χR.hom = χE.hom ≫ rr`, `sh ≫ ω.hom = χR.hom ≫ rs` and `rrs = rr ≫ rs`, then
`χE.inv ≫ red ≫ sh = rrs ≫ ω.inv`. -/
theorem fibreBaseMap_aux {𝒞 : Type*} [Category 𝒞] {E R O E' R' O' : 𝒞} (red : E ⟶ R)
    (sh : R ⟶ O) (χE : E ≅ E') (χR : R ≅ R') (rr : E' ⟶ R') (rs : R' ⟶ O') (rrs : E' ⟶ O')
    (ω : O ≅ O') (n : red ≫ χR.hom = χE.hom ≫ rr) (c : sh ≫ ω.hom = χR.hom ≫ rs)
    (hrs : rrs = rr ≫ rs) :
    χE.inv ≫ red ≫ sh = rrs ≫ ω.inv := by
  rw [Iso.inv_comp_eq, hrs]
  simp only [Category.assoc]
  rw [← reassoc_of% n, ← reassoc_of% c, Iso.hom_inv_id, Category.comp_id]

/-- The inclusion of the kernel of an extension transported along `e : ℳ ≅ 𝒩`, evaluated on the
image of a map into `𝒩` with restricted scalars; stated with the modules as variables. -/
theorem transportKernel_incl_restrictScalars {𝒞 : Type v} [Category.{w} 𝒞]
    {L : GrothendieckTopology 𝒞} [L.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A O : Sheaf L CommRingCat.{u}} {a : A ⟶ O}
    {M N : SheafOfModules.{u} ((sheafCompose L (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
    {R : Sheaf L RingCat.{u}} {α : R ⟶ (sheafCompose L (forget₂ CommRingCat.{u} RingCat.{u})).obj O}
    (P : Deformation.AlgebraExtension.{u, v, w} a M) (e : M ≅ N) {I : SheafOfModules.{u} R}
    (c : I ⟶ (SheafOfModules.restrictScalars α).obj N) (U : 𝒞ᵒᵖ) (x : I.val.obj U) :
    (P.transportKernel e).incl (show N.val.obj U from c.val.app U x) =
      P.incl (show M.val.obj U from
        (c ≫ (SheafOfModules.restrictScalars α).map e.inv).val.app U x) :=
  rfl

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1)
  {X X₀ : AlgebraicSpaces B S hS} (ρ : X ≅ X₀)
  (g : X₀ ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))

/-- The structure map `g⁻¹t⁻¹𝒪_{Y'} ⟶ 𝒪_{X₀}` of the solutions of `problem g`. -/
abbrev fibreBaseMap₀ :
    (inverseImageCommRingFunctor (problem g hZ).f.toToposHom).obj (problem g hZ).baseExtension ⟶
      (smallEtaleRingedTopos B S hS X₀).O :=
  (inverseImageCommRingFunctor (problem g hZ).f.toToposHom).map (problem g hZ).baseReduction ≫
    (problem g hZ).f.fSharpInverseImage

/-- `𝒪_X ≅ ρ^*𝒪_{X₀}`. -/
abbrev fibreStructureIso :
    (smallEtaleRingedTopos B S hS X).O ≅ (fibreRingRes ρ).obj (smallEtaleRingedTopos B S hS X₀).O :=
  (etaleRestrictionStructureSheafIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).symm

/-- The structure map of the restricted extensions: `ρ^*g⁻¹t⁻¹𝒪_{Y'} ⟶ ρ^*𝒪_{X₀} ≅ 𝒪_X`. -/
abbrev fibreBaseMap₁ :
    (fibreRingRes ρ).obj ((inverseImageCommRingFunctor (problem g hZ).f.toToposHom).obj
      (problem g hZ).baseExtension) ⟶ (smallEtaleRingedTopos B S hS X).O :=
  (fibreRingRes ρ).map (fibreBaseMap₀ hZ g) ≫ (fibreStructureIso ρ).inv

/-- The ring data of the restriction along `ρ`: the base is restricted as it is. -/
def fibreRingComparison :
    Deformation.AlgebraExtension.RingComparison
      (G := smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
      (K := SmallEtale.topology B S hS X.1) (J := SmallEtale.topology B S hS X₀.1)
      (fibreBaseMap₀ hZ g) (fibreBaseMap₁ hZ ρ g) where
  α := Iso.refl _
  ω := fibreStructureIso ρ
  comm := by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.refl_hom, Category.id_comp]

/-- The restriction along `ρ` of an extension of `g⁻¹t⁻¹𝒪_{Y'}`-algebras of `𝒪_{X₀}` by
`g^*𝒞_{Y/Y'}`. -/
def fibreRestriction (Q : Deformation.AlgebraExtension.{u, u + 1, u}
      (J := SmallEtale.topology B S hS X₀.1) (fibreBaseMap₀ hZ g) (problem g hZ).G) :
    Deformation.AlgebraExtension.{u, u + 1, u} (J := SmallEtale.topology B S hS X.1)
      (fibreBaseMap₁ hZ ρ g) ((fibreModuleRes ρ).obj (problem g hZ).G) :=
  Deformation.AlgebraExtension.restrictVia.{u, u + 1, u, u + 1, u}
    (G := smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
    (K := SmallEtale.topology B S hS X.1) (J := SmallEtale.topology B S hS X₀.1)
    (fibreRingComparison hZ ρ g)
    (etaleRestrictionModuleComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ) g
      (problem g hZ).G) Q

/-- The identification of the thickened base of the restricted extension with that of
`problem (ρ ≫ g)`. -/
abbrev fibreTheta :
    (fibreRingRes ρ).obj ((inverseImageCommRingFunctor (problem g hZ).f.toToposHom).obj
      (problem g hZ).baseExtension) ≅
      (inverseImageCommRingFunctor (problem (ρ.hom ≫ g) hZ).f.toToposHom).obj
        (problem (ρ.hom ≫ g) hZ).baseExtension :=
  (fibreRingIso ρ g (baseExtension hZ).extension).symm

/-- The identification `fibreTheta` carries the structure map of `problem (ρ ≫ g)` to the
structure map `fibreBaseMap₁` of the restricted extension. -/
theorem fibreTheta_comp :
    (fibreTheta hZ ρ g).hom ≫
        (inverseImageCommRingFunctor (problem (ρ.hom ≫ g) hZ).f.toToposHom).map
          (problem (ρ.hom ≫ g) hZ).baseReduction ≫ (problem (ρ.hom ≫ g) hZ).f.fSharpInverseImage =
      fibreBaseMap₁ hZ ρ g :=
  fibreBaseMap_aux _ _ (fibreRingIso ρ g (baseExtension hZ).extension)
    (fibreRingIso ρ g (smallEtaleRingedTopos B S hS _).O) _ _ _ (fibreStructureIso ρ)
    (fibreRingIso_naturality ρ g (baseExtension hZ).reduction)
    (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ) g).comm
    (Functor.map_comp _ _ _)

/-! ### The restricted solution -/

variable (P : (problem g hZ).CompatibleFirstOrderThickening)

/-- A solution of `problem g`, as an extension of `g⁻¹t⁻¹𝒪_{Y'}`-algebras. -/
abbrev fibreQ₀ :
    Deformation.AlgebraExtension.{u, u + 1, u} (J := SmallEtale.topology B S hS X₀.1)
      (fibreBaseMap₀ hZ g) (problem g hZ).G :=
  (problem g hZ).toAlgebraExtension (Iso.refl _) (Category.id_comp (fibreBaseMap₀ hZ g)) P

/-- The map from the base ideal of `problem (ρ ≫ g)` to the kernel `ρ^*g^*𝒞_{Y/Y'}` of the
restriction of a solution of `problem g`. -/
def fibreIdealMap :
    (problem (ρ.hom ≫ g) hZ).I ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (problem (ρ.hom ≫ g) hZ).f.fSharpInverseImage)).obj
          ((fibreModuleRes ρ).obj (problem g hZ).G) :=
  (problem (ρ.hom ≫ g) hZ).idealMap (fibreTheta hZ ρ g) (fibreTheta_comp hZ ρ g)
    (fibreRestriction hZ ρ g (fibreQ₀ hZ g P))

/-- `fibreResCommIso`, with the restrictions of scalars spelled through the structure maps of the
two extension problems. -/
def fibreProblemCommIso :
    fibreModuleRes ρ ⋙ SheafOfModules.restrictScalars
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (problem (ρ.hom ≫ g) hZ).f.fSharpInverseImage) ≅
      SheafOfModules.restrictScalars
          ((sheafCompose (SmallEtale.topology B S hS X₀.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map (problem g hZ).f.fSharpInverseImage) ⋙
        fibreScalarRes ρ g :=
  fibreResCommIso ρ g

/-- On sections, the restriction along `ρ` of `c : I ⟶ N` followed by `fibreProblemCommIso` is
`c` itself. -/
theorem fibreScalarRes_map_comp_inv_val_app {I : SheafOfModules.{u} ((sheafCompose
      (SmallEtale.topology B S hS X₀.1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS _).O))}
    {N : SheafOfModules.{u} ((sheafCompose
      (SmallEtale.topology B S hS X₀.1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X₀).O)}
    (c : I ⟶ (SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X₀.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (problem g hZ).f.fSharpInverseImage)).obj N)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (y : ((fibreScalarRes ρ g).obj I).val.obj U) :
    ((fibreScalarRes ρ g).map c ≫ (fibreProblemCommIso hZ ρ g).inv.app N).val.app U y =
      c.val.app _ y :=
  rfl

/-- The restriction of `c` along `ρ`, read through the identification of the base ideals and the
commutation of restrictions. -/
abbrev fibreC :
    (problem (ρ.hom ≫ g) hZ).I ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (problem (ρ.hom ≫ g) hZ).f.fSharpInverseImage)).obj
          ((fibreModuleRes ρ).obj (problem g hZ).G) :=
  (fibreIdealIso hZ ρ g).hom ≫ (fibreScalarRes ρ g).map (problem g hZ).c ≫
    (fibreProblemCommIso hZ ρ g).inv.app (problem g hZ).G

/-- On sections, the isomorphism `fibreIdealIso` is given by `fibreIdealApp`. -/
theorem fibreIdealIso_hom_val_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (problem (ρ.hom ≫ g) hZ).I.val.obj U) :
    (fibreIdealIso hZ ρ g).hom.val.app U x =
      (show ((fibreScalarRes ρ g).obj (problem g hZ).I).val.obj U from fibreIdealApp hZ ρ g U x) :=
  SheafOfModules.idealLift_val_app _ _ _ _ U x

/-- On sections, `fibreC` is the map `c` of `problem g` evaluated at `fibreIdealApp`. -/
theorem fibreC_app (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : (problem (ρ.hom ≫ g) hZ).I.val.obj U) :
    (fibreC hZ ρ g).val.app U x = (problem g hZ).c.val.app _ (fibreIdealApp hZ ρ g U x) :=
  SheafOfModules.comp_val_app_eq _ _ (fibreIdealIso_hom_val_app hZ ρ g U x)
    (fibreScalarRes_map_comp_inv_val_app hZ ρ g (problem g hZ).c U _)

/-- The image of the base ideal in the restricted extension is the inclusion of `fibreC`. -/
private theorem idealImage_eq_incl_fibreC (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (problem (ρ.hom ≫ g) hZ).I.val.obj U) :
    (problem (ρ.hom ≫ g) hZ).idealImage (fibreTheta hZ ρ g)
        (fibreRestriction hZ ρ g (fibreQ₀ hZ g P)) x =
      (fibreRestriction hZ ρ g (fibreQ₀ hZ g P)).incl
        (show ((fibreModuleRes ρ).obj (problem g hZ).G).val.obj U from
          (fibreC hZ ρ g).val.app U x) := by
  have h2 := congrArg ((fibreQ₀ hZ g P).algebraMap.hom.app
    ((smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).op.obj U))
    (incl_fibreIdealApp hZ ρ g U x)
  have h3 := (problem g hZ).isCompatible_toAlgebraExtension (Iso.refl _)
    (Category.id_comp (fibreBaseMap₀ hZ g)) P
    ((smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).op.obj U)
    (fibreIdealApp hZ ρ g U x)
  have h4 := SheafOfModules.congr_restrictScalars_val _ _
    (fibreRestriction hZ ρ g (fibreQ₀ hZ g P)).incl (fibreC_app hZ ρ g U x)
  have h5 := (h2.symm.trans h3).trans h4.symm
  exact h5

/-- **The map from the base ideal is the restriction of `c`.** -/
theorem fibreIdealMap_eq : fibreIdealMap hZ ρ g P = fibreC hZ ρ g := by
  refine SheafOfModules.hom_ext_of_injective
    (fun U => (fibreRestriction hZ ρ g (fibreQ₀ hZ g P)).incl (U := U))
    (fun U => (fibreRestriction hZ ρ g (fibreQ₀ hZ g P)).incl_injective) fun U x => ?_
  exact ((problem (ρ.hom ≫ g) hZ).incl_idealMap (fibreTheta hZ ρ g) (fibreTheta_comp hZ ρ g)
    (fibreRestriction hZ ρ g (fibreQ₀ hZ g P)) U x).trans (idealImage_eq_incl_fibreC hZ ρ g P U x)

/-! ### The kernel identification -/

/-- The map `c` of `problem g` is universal: it is the unit of extension of scalars. -/
theorem bijective_problem_c {X₁ : AlgebraicSpaces B S hS}
    (g₁ : X₁ ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X₁.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X₁).O)) :
    Function.Bijective fun k : (problem g₁ hZ).G ⟶ M => (problem g₁ hZ).c ≫
      (SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X₁.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map (problem g₁ hZ).f.fSharpInverseImage)).map k :=
  (extendScalarsFSharpAdjunction B S hS g₁).bijective_comp_map_unit _ M

/-- The map `c` of `problem g` is universal on endomorphisms. -/
theorem cIsUniversal_problem {X₁ : AlgebraicSpaces B S hS}
    (g₁ : X₁ ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :
    (problem g₁ hZ).CIsUniversal := fun k hk =>
  (bijective_problem_c hZ g₁ _).1
    (by beta_reduce; rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact hk)

/-- **The restriction of `c` is universal**, as the restriction along the equivalence `ρ` of the
universal arrow `c` of `problem g`. -/
theorem bijective_fibreC
    (M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)) :
    Function.Bijective fun k : (fibreModuleRes ρ).obj (problem g hZ).G ⟶ M => fibreC hZ ρ g ≫
      (SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (problem (ρ.hom ≫ g) hZ).f.fSharpInverseImage)).map k :=
  bijective_comp_map_of_transport_of_fullyFaithful (fibreProblemCommIso hZ ρ g)
    (have := full_fibreScalarRes ρ g; have := faithful_fibreScalarRes ρ g
     Functor.FullyFaithful.ofFullyFaithful (fibreScalarRes ρ g)) (problem g hZ).c
    (bijective_problem_c hZ g) (fibreIdealIso hZ ρ g) M

/-- **The kernel identification** `(ρ ≫ g)^*𝒞_{Y/Y'} ⟶ ρ^*g^*𝒞_{Y/Y'}`, the adjoint of the
restriction of `c`. -/
def fibreKernelMap : (problem (ρ.hom ≫ g) hZ).G ⟶ (fibreModuleRes ρ).obj (problem g hZ).G :=
  ((extendScalarsFSharpAdjunction B S hS (ρ.hom ≫ g)).homEquiv _ _).symm (fibreC hZ ρ g)

/-- The kernel identification `fibreKernelMap` is an isomorphism. -/
instance isIso_fibreKernelMap : IsIso (fibreKernelMap hZ ρ g) :=
  (extendScalarsFSharpAdjunction B S hS (ρ.hom ≫ g)).isIso_homEquiv_symm_of_bijective _
    (bijective_fibreC hZ ρ g)

/-- The map `c` of `problem (ρ ≫ g)` followed by `fibreKernelMap` is `fibreC`. -/
theorem problem_c_comp_fibreKernelMap :
    (problem (ρ.hom ≫ g) hZ).c ≫ (SheafOfModules.restrictScalars
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (problem (ρ.hom ≫ g) hZ).f.fSharpInverseImage)).map (fibreKernelMap hZ ρ g) =
      fibreC hZ ρ g :=
  ((extendScalarsFSharpAdjunction B S hS (ρ.hom ≫ g)).homEquiv_unit _ _ _).symm.trans
    (((extendScalarsFSharpAdjunction B S hS (ρ.hom ≫ g)).homEquiv _ _).apply_symm_apply _)

/-! ### The restricted solution -/

/-- The restricted extension, with its kernel identified with `(ρ ≫ g)^*𝒞_{Y/Y'}`. -/
abbrev fibreExtension :
    Deformation.AlgebraExtension.{u, u + 1, u} (J := SmallEtale.topology B S hS X.1)
      (fibreBaseMap₁ hZ ρ g) (problem (ρ.hom ≫ g) hZ).G :=
  (fibreRestriction hZ ρ g (fibreQ₀ hZ g P)).transportKernel (asIso (fibreKernelMap hZ ρ g)).symm

/-- The extension `fibreExtension` is compatible, through `fibreTheta`, with the map `c` of
`problem (ρ ≫ g)`. -/
theorem isCompatible_fibreExtension :
    (problem (ρ.hom ≫ g) hZ).IsCompatible (fibreTheta hZ ρ g) (problem (ρ.hom ≫ g) hZ).c
      (fibreExtension hZ ρ g P) := fun U x => by
  have h3 : fibreC hZ ρ g = (problem (ρ.hom ≫ g) hZ).c ≫ (SheafOfModules.restrictScalars
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (problem (ρ.hom ≫ g) hZ).f.fSharpInverseImage)).map
          (asIso (fibreKernelMap hZ ρ g)).symm.inv :=
    (problem_c_comp_fibreKernelMap hZ ρ g).symm
  have h4 := congrArg (fun d => d.val.app U x) h3
  have h5 := transportKernel_incl_restrictScalars (fibreRestriction hZ ρ g (fibreQ₀ hZ g P))
    (asIso (fibreKernelMap hZ ρ g)).symm (problem (ρ.hom ≫ g) hZ).c U x
  exact (idealImage_eq_incl_fibreC hZ ρ g P U x).trans
    ((SheafOfModules.congr_restrictScalars_val _ _
      (fibreRestriction hZ ρ g (fibreQ₀ hZ g P)).incl h4).trans h5.symm)

/-- **The restriction along `ρ : X ≅ X₀` of a solution of `problem g`**, a solution of
`problem (ρ ≫ g)`. -/
def fibreSolution : (problem (ρ.hom ≫ g) hZ).CompatibleFirstOrderThickening :=
  (problem (ρ.hom ≫ g) hZ).ofAlgebraExtension (fibreTheta hZ ρ g) (fibreTheta_comp hZ ρ g)
    (fibreExtension hZ ρ g P) (isCompatible_fibreExtension hZ ρ g P)

/-! ### The solution attached to a flat deformation, on the small étale site of `X` -/

/-- **The solution of `problem f` attached to a flat deformation** `D` of `f : X ⟶ Y`: the
solution `Deformation.solution` of the closed fibre `X'_0 = f'⁻¹(Y)`, restricted along the
identification `X ≅ X'_0` (`Deformation.fibreIso`), whose composite with `f'_0` is `f`. -/
def Deformation.solutionOnSource {f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)}
    (D : Deformation f) : (problem f hZ).CompatibleFirstOrderThickening :=
  D.fibreIso_hom_reduction ▸ fibreSolution hZ D.fibreIso D.reduction (D.solution hZ)

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
