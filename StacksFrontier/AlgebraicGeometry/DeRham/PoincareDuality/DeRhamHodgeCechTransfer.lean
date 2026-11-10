module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamComplexSections
public import StacksFrontier.AlgebraicGeometry.DeRham.CechCupProduct
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCechTransferCup
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyGlobalScalars
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyVanishingAboveDimension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraCounitEssentiallySmall
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The graded pieces of the de Rham complex and Hodge cohomology, on Čech cocycles

Let `f : X ⟶ S` be a morphism of schemes with `X` of affine diagonal, and write
`Ω^•_{X/S}` for its relative de Rham complex, a complex of sheaves of `f⁻¹𝒪_S`-modules whose
term in degree `n ≥ 0` is the `𝒪_X`-module `Ωⁿ_{X/S}` read over `f⁻¹𝒪_S`. Since restriction of
scalars does not change the underlying abelian sheaves, the Čech cocycles of the two readings are
the same, and the hypercohomology `H^{p+n}(X, Ωⁿ[-n])`, computed in sheaves of `f⁻¹𝒪_S`-modules,
is identified with the cohomology `H^p(X, Ωⁿ)` of the `𝒪_X`-module `Ωⁿ`
(`Stacks.Cech.Hypercohomology.cechTransferEquiv`). This file records this identification for the
de Rham complex and its compatibility with the global sections of `f⁻¹𝒪_S`, acting through
`𝒪_X`, and with the wedge product.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamPlus`: the relative de Rham complex as a bounded below
  complex of sheaves of `f⁻¹𝒪_S`-modules.
* `AlgebraicGeometry.Scheme.Hom.deRhamTermTransfer`: `H^{p+n}(X, Ωⁿ[-n]) ≃ H^p(X, Ωⁿ)`.

## References

* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (abSections SectionRing)
open Stacks.Cech.Hypercohomology
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (bilinearPostcomp bilinearPostcomp_app)

universe u

namespace AlgebraicGeometry.Scheme.Hom

open scoped Stacks.StandardDerivedModel
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The relative de Rham complex `Ω^•_{X/S}` as a bounded below complex** of sheaves of
`f⁻¹𝒪_S`-modules. -/
abbrev deRhamPlus :
    CochainComplex.Plus (_root_.SheafOfModules.{u} (ringSheaf (inverseImageRingSheaf f))) :=
  SheafOfModules.deRhamComplexPlus (deRhamAlgebras f)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras f))

/-- The structural morphism `f⁻¹𝒪_S ⟶ 𝒪_X`, on sheaves of rings. -/
abbrev formsRingHom : ringSheaf (inverseImageRingSheaf f) ⟶ ringSheaf X.sheaf :=
  SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap f)

/-- **The term of degree `n ≥ 0` of the relative de Rham complex is `Ωⁿ_{X/S}`**, read over
`f⁻¹𝒪_S`. -/
theorem deRhamPlus_X (n : ℕ) :
    (deRhamPlus f).obj.X (n : ℤ) =
      (_root_.SheafOfModules.restrictScalars (formsRingHom f)).obj
        (relativeDifferentialForms f (n : ℤ)) :=
  SheafOfModules.deRhamComplexInt_X_of_nonneg _ _ n (Int.natCast_nonneg n)

/-- The underlying abelian presheaves of the term of degree `n` of the de Rham complex and of
`Ωⁿ_{X/S}` agree. -/
def deRhamTermAbIso (n : ℕ) :
    abSections ((deRhamPlus f).obj.X (n : ℤ)) ≅ abSections (relativeDifferentialForms f (n : ℤ)) :=
  eqToIso (congrArg abSections (deRhamPlus_X f n)) ≪≫ (sheafToPresheaf _ _).mapIso
    ((Stacks.SheafOfModules.CoextendScalars.restrictScalarsCompToSheafIso (formsRingHom f)).app
      (relativeDifferentialForms f (n : ℤ)))

/-- The identification of underlying abelian presheaves is the identity on local sections. -/
theorem deRhamTermAbIso_hom_app_heq (n : ℕ) (V : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (x : ((deRhamPlus f).obj.X (n : ℤ)).val.obj V) :
    HEq ((deRhamTermAbIso f n).hom.app V x) x := by
  have key : ∀ {M : _root_.SheafOfModules.{u} (ringSheaf (inverseImageRingSheaf f))}
      (h : M = (_root_.SheafOfModules.restrictScalars (formsRingHom f)).obj
        (relativeDifferentialForms f (n : ℤ))) (x : M.val.obj V),
      HEq ((eqToIso (congrArg abSections h) ≪≫ (sheafToPresheaf _ _).mapIso
        ((Stacks.SheafOfModules.CoextendScalars.restrictScalarsCompToSheafIso (formsRingHom f)).app
          (relativeDifferentialForms f (n : ℤ)))).hom.app V x) x := by
    rintro M rfl x
    rfl
  exact key (deRhamPlus_X f n) x

/-! ### The wedge product -/

/-- **The wedge product `Ωᵃ × Ωᵇ ⟶ Ωⁿ`**, `a + b = n`, of the relative de Rham differential
graded algebra (Tag 0FU6), as a bilinear map of the terms of the de Rham complex. -/
def deRhamWedge (a b n : ℤ) (h : a + b = n) :
    Stacks.BilinearMap ((deRhamPlus f).obj.X a).val ((deRhamPlus f).obj.X b).val
      ((deRhamPlus f).obj.X n).val :=
  bilinearPostcomp ((SheafOfModules.deRhamDifferentialGradedAlgebra (deRhamAlgebras f)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras f))).mul a b)
    ((deRhamPlus f).obj.XIsoOfEq h).hom.val

/-- **The wedge product `Ωᵃ × Ωᵇ ⟶ Ωⁿ`**, `a + b = n`, of the algebra of differential forms, as
a bilinear map of sheaves of `𝒪_X`-modules. -/
def formsWedge (a b n : ℤ) (h : a + b = n) :
    Stacks.BilinearMap (relativeDifferentialForms f a).val (relativeDifferentialForms f b).val
      (relativeDifferentialForms f n).val :=
  bilinearPostcomp ((relativeDifferentialFormsAlgebra f).mul a b)
    (eqToHom (congrArg (relativeDifferentialForms f) h)).val

/-- The pairing on sections attached to a bilinear map followed by a morphism is the pairing
attached to the bilinear map, followed by the morphism on sections. -/
theorem _root_.Stacks.Cech.Hypercohomology.bilinearPairing_bilinearPostcomp {Y : TopCat.{u}}
    {O : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
    {F G H H' : _root_.SheafOfModules.{u} (ringSheaf O)} (β : Stacks.BilinearMap F.val G.val H.val)
    (φ : H ⟶ H') :
    bilinearPairing (bilinearPostcomp β φ.val) =
      bilinearPairing β ≫ (Stacks.Cohomology.CechSheaf.sectionsPresheafFunctor (R := ringSheaf O)
        (⊤ : TopologicalSpace.Opens Y)).map φ := by
  refine NatTrans.ext (funext fun Z => ModuleCat.hom_ext (TensorProduct.ext' fun x y => ?_))
  rfl

/-- **The wedge product of the de Rham complex is the pairing of the de Rham complex with itself
in each bidegree.** -/
theorem deRhamCechPairing_μ (a b n : ℤ) (h : a + b = n) :
    (SheafOfModules.deRhamCechPairing (deRhamAlgebras f)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras f))).μ a b n h =
      bilinearPairing (deRhamWedge f a b n h) :=
  (Stacks.Cech.Hypercohomology.bilinearPairing_bilinearPostcomp _ _).symm

/-- A morphism `eqToHom` of sheaves of modules is the identity on local sections. -/
theorem _root_.SheafOfModules.eqToHom_val_app_heq {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{u} R}
    (h : M = N) (V : Cᵒᵖ) (z : M.val.obj V) : HEq ((eqToHom h).val.app V z) z := by
  subst h
  rfl

/-- **The identifications of the terms of the de Rham complex with the sheaves of differential
forms carry the wedge product of the de Rham complex to the wedge product of forms.** -/
theorem deRhamTermAbIso_deRhamWedge (a b n : ℕ) (h : (a : ℤ) + b = n)
    (V : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (x : ((deRhamPlus f).obj.X (a : ℤ)).val.obj V)
    (y : ((deRhamPlus f).obj.X (b : ℤ)).val.obj V) :
    (deRhamTermAbIso f n).hom.app V ((deRhamWedge f a b n h).app V x y) =
      (formsWedge f a b n h).app V ((deRhamTermAbIso f a).hom.app V x)
        ((deRhamTermAbIso f b).hom.app V y) := by
  have hm := SheafOfModules.deRhamDifferentialGradedAlgebra_mul (deRhamAlgebras f)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras f)) a b V x y _ _
    (deRhamTermAbIso_hom_app_heq f a V x).symm (deRhamTermAbIso_hom_app_heq f b V y).symm
  have e₁ : HEq ((deRhamWedge f a b n h).app V x y)
      (((SheafOfModules.deRhamDifferentialGradedAlgebra (deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras f))).mul a b).app V x y) :=
    _root_.SheafOfModules.eqToHom_val_app_heq (congrArg (deRhamPlus f).obj.X h) V _
  have e₂ : HEq ((formsWedge f a b n h).app V ((deRhamTermAbIso f a).hom.app V x)
        ((deRhamTermAbIso f b).hom.app V y))
      (((relativeDifferentialFormsAlgebra f).mul a b).app V ((deRhamTermAbIso f a).hom.app V x)
        ((deRhamTermAbIso f b).hom.app V y)) :=
    _root_.SheafOfModules.eqToHom_val_app_heq (congrArg (relativeDifferentialForms f) h) V _
  exact eq_of_heq ((deRhamTermAbIso_hom_app_heq f n V _).trans (e₁.trans (hm.trans e₂.symm)))

section Transfer

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- Čech cohomology computes the hypercohomology of a term of the de Rham complex placed in its
degree. -/
theorem cechComputes_deRhamPlus_X (n : ℤ) :
    CechComputes (inverseImageRingSheaf f)
      (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X n) n) :=
  (cechComputesSheaf_deRhamComplexInt_X f n).singlePlus _ n

/-- Čech cohomology computes the cohomology of the sheaf of differential forms of degree `n`. -/
theorem cechComputes_relativeDifferentialForms (n : ℕ) :
    CechComputes X.sheaf (singlePlus X.sheaf (relativeDifferentialForms f (n : ℤ)) 0) :=
  have := isQuasicoherent_relativeDifferentialForms f n
  (cechComputesSheaf_of_isQuasicoherent X (relativeDifferentialForms f (n : ℤ))).singlePlus _ 0

/-- **The hypercohomology of a term of the de Rham complex is the cohomology of the sheaf of
differential forms**: `H^{p+n}(X, Ωⁿ[-n])`, computed in sheaves of `f⁻¹𝒪_S`-modules, is
`H^p(X, Ωⁿ)`, computed in sheaves of `𝒪_X`-modules; the class of a Čech cocycle goes to the class
of the same cocycle. -/
def deRhamTermTransfer (n p : ℕ) :
    hypercohomology (inverseImageRingSheaf f)
        (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X (n : ℤ)) n) ((p : ℤ) + n) ≃+
      hypercohomology X.sheaf (singlePlus X.sheaf (relativeDifferentialForms f (n : ℤ)) 0) p :=
  cechTransferEquiv (n : ℤ) 0 (deRhamTermAbIso f n) (cechComputes_deRhamPlus_X f n)
    (cechComputes_relativeDifferentialForms f n) p

/-- The structural morphism `Γ(X, f⁻¹𝒪_S) ⟶ Γ(X, 𝒪_X)` on global sections. -/
abbrev inverseImageRingTop : (inverseImageRingSheaf f).obj.obj (op ⊤) ⟶ X.presheaf.obj (op ⊤) :=
  (inverseImageStructureMap f).hom.app (op ⊤)

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- **Multiplication by a global section of `f⁻¹𝒪_S` on a term of the de Rham complex is
multiplication by its image in `Γ(X, 𝒪_X)` on the sheaf of differential forms**, on the
underlying abelian presheaves. -/
theorem smulHom_comp_deRhamTermAbIso (n : ℕ) (r : (inverseImageRingSheaf f).obj.obj (op ⊤)) :
    ((_root_.SheafOfModules.toSheaf _).map (Stacks.Cohomology.InvertibleDerived.smulHom
        (X := ringedSpaceOf (inverseImageRingSheaf f)) r ((deRhamPlus f).obj.X (n : ℤ)))).hom ≫
      (deRhamTermAbIso f n).hom =
    (deRhamTermAbIso f n).hom ≫ ((_root_.SheafOfModules.toSheaf _).map
      (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace)
        (inverseImageRingTop f r) (relativeDifferentialForms f (n : ℤ)))).hom := by
  have key : ∀ {M : _root_.SheafOfModules.{u} (ringSheaf (inverseImageRingSheaf f))}
      (h : M = (_root_.SheafOfModules.restrictScalars (formsRingHom f)).obj
        (relativeDifferentialForms f (n : ℤ))),
      ((_root_.SheafOfModules.toSheaf _).map (Stacks.Cohomology.InvertibleDerived.smulHom
          (X := ringedSpaceOf (inverseImageRingSheaf f)) r M)).hom ≫
        (eqToIso (congrArg abSections h) ≪≫ (sheafToPresheaf _ _).mapIso
          ((Stacks.SheafOfModules.CoextendScalars.restrictScalarsCompToSheafIso
            (formsRingHom f)).app
            (relativeDifferentialForms f (n : ℤ)))).hom =
      (eqToIso (congrArg abSections h) ≪≫ (sheafToPresheaf _ _).mapIso
          ((Stacks.SheafOfModules.CoextendScalars.restrictScalarsCompToSheafIso
            (formsRingHom f)).app
            (relativeDifferentialForms f (n : ℤ)))).hom ≫
        ((_root_.SheafOfModules.toSheaf _).map (Stacks.Cohomology.InvertibleDerived.smulHom
          (X := X.toRingedSpace) (inverseImageRingTop f r)
            (relativeDifferentialForms f (n : ℤ)))).hom := by
    rintro M rfl
    refine NatTrans.ext (funext fun V => ?_)
    ext x
    change (show (ringSheaf X.sheaf).obj.obj V from (inverseImageStructureMap f).hom.app V
        ((inverseImageRingSheaf f).obj.map (homOfLE le_top).op r)) •
        (show (relativeDifferentialForms f (n : ℤ)).val.obj V from x) =
      (show (ringSheaf X.sheaf).obj.obj V from
        X.presheaf.map (homOfLE le_top).op (inverseImageRingTop f r)) •
        (show (relativeDifferentialForms f (n : ℤ)).val.obj V from x)
    exact congrArg (fun a : (ringSheaf X.sheaf).obj.obj V =>
        a • (show (relativeDifferentialForms f (n : ℤ)).val.obj V from x))
      (ConcreteCategory.congr_hom ((inverseImageStructureMap f).hom.naturality
        (homOfLE (le_top : V.unop ≤ ⊤)).op) r)
  exact key (deRhamPlus_X f n)

/-- **The identification `H^{p+n}(X, Ωⁿ[-n]) ≃ H^p(X, Ωⁿ)` is semilinear along
`Γ(X, f⁻¹𝒪_S) ⟶ Γ(X, 𝒪_X)`.** -/
theorem deRhamTermTransfer_smul (n p : ℕ) (r : SectionRing (ringSheaf (inverseImageRingSheaf f)) ⊤)
    (x : hypercohomology (inverseImageRingSheaf f)
      (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X (n : ℤ)) n) ((p : ℤ) + n)) :
    deRhamTermTransfer f n p (r • x) =
      (show SectionRing (ringSheaf X.sheaf) ⊤ from inverseImageRingTop f r) •
        deRhamTermTransfer f n p x := by
  have h₁ := hypercohomologyMap_smulHom (X := ringedSpaceOf (inverseImageRingSheaf f)) r
    ((deRhamPlus f).obj.X (n : ℤ)) n (cechComputes_deRhamPlus_X f n) _ x
  have h₃ := hypercohomologyMap_smulHom (X := X.toRingedSpace) (inverseImageRingTop f r)
    (relativeDifferentialForms f (n : ℤ)) 0 (cechComputes_relativeDifferentialForms f n) _
    (deRhamTermTransfer f n p x)
  have h₂ := cechTransfer_hypercohomologyMap (deRhamTermAbIso f n).hom (n : ℤ) 0
    (deRhamTermAbIso f n).hom _ _ (smulHom_comp_deRhamTermAbIso f n r)
    (cechComputes_deRhamPlus_X f n) (cechComputes_deRhamPlus_X f n) p x
  exact (congrArg (deRhamTermTransfer f n p) h₁.symm).trans (h₂.trans h₃)

/-- **The identifications `H^{p+n}(X, Ωⁿ[-n]) ≃ H^p(X, Ωⁿ)` carry the cup product along the wedge
product of the de Rham complex to the cup product along the wedge product of forms**, up to the
sign `(-1)^{aq}`. -/
theorem deRhamTermTransfer_cup (a b n : ℕ) (h : (a : ℤ) + b = n) (p q : ℕ)
    (x : hypercohomology (inverseImageRingSheaf f)
      (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X (a : ℤ)) a) ((p : ℤ) + a))
    (y : hypercohomology (inverseImageRingSheaf f)
      (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X (b : ℤ)) b) ((q : ℤ) + b)) :
    deRhamTermTransfer f n (p + q)
        (cup (inverseImageRingSheaf f) (cechComputes_deRhamPlus_X f a)
          (cechComputes_deRhamPlus_X f b)
          (singlePairingAtTo (inverseImageRingSheaf f) a b n h
            (bilinearPairing (deRhamWedge f a b n h)))
          ((p : ℤ) + a) ((q : ℤ) + b) (((p + q : ℕ) : ℤ) + n) (by push_cast; omega) x y) =
      ((a * q : ℤ).negOnePow : ℤ) • cup X.sheaf (cechComputes_relativeDifferentialForms f a)
        (cechComputes_relativeDifferentialForms f b)
          (singlePairing (bilinearPairing (formsWedge f a b n h))) p q ((p + q : ℕ) : ℤ)
          (by push_cast; rfl) (deRhamTermTransfer f a p x) (deRhamTermTransfer f b q y) := by
  have key := cechTransfer_cupTo (deRhamTermAbIso f a).hom (deRhamTermAbIso f b).hom
    (deRhamTermAbIso f n).hom (deRhamWedge f a b n h) (formsWedge f a b n h)
    (fun V x y => deRhamTermAbIso_deRhamWedge f a b n h (op V) x y) (a : ℤ) b n 0 0 0 h rfl
    (cechComputes_deRhamPlus_X f a) (cechComputes_deRhamPlus_X f b) (cechComputes_deRhamPlus_X f n)
    (cechComputes_relativeDifferentialForms f a) (cechComputes_relativeDifferentialForms f b) p q
    x y
  rw [zero_mul, Int.negOnePow_zero, Units.val_one, one_smul] at key
  exact key

/-- `deRhamTermTransfer_cup` with the total Čech degree given by an equation. -/
theorem deRhamTermTransfer_cup' (a b n : ℕ) (h : (a : ℤ) + b = n) (p q P : ℕ) (hP : p + q = P)
    (x : hypercohomology (inverseImageRingSheaf f)
      (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X (a : ℤ)) a) ((p : ℤ) + a))
    (y : hypercohomology (inverseImageRingSheaf f)
      (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X (b : ℤ)) b) ((q : ℤ) + b)) :
    deRhamTermTransfer f n P
        (cup (inverseImageRingSheaf f) (cechComputes_deRhamPlus_X f a)
          (cechComputes_deRhamPlus_X f b)
          (singlePairingAtTo (inverseImageRingSheaf f) a b n h
            (bilinearPairing (deRhamWedge f a b n h)))
          ((p : ℤ) + a) ((q : ℤ) + b) ((P : ℤ) + n) (by subst hP; push_cast; omega) x y) =
      ((a * q : ℤ).negOnePow : ℤ) • cup X.sheaf (cechComputes_relativeDifferentialForms f a)
        (cechComputes_relativeDifferentialForms f b)
          (singlePairing (bilinearPairing (formsWedge f a b n h))) p q (P : ℤ)
          (by subst hP; push_cast; rfl) (deRhamTermTransfer f a p x)
          (deRhamTermTransfer f b q y) := by
  subst hP
  exact deRhamTermTransfer_cup f a b n h p q x y

end Transfer

end AlgebraicGeometry.Scheme.Hom

end
