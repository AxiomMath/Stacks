module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.SectionsHom
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.AffineAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.BaseChangeHomQI
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.InjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.Basis

/-!
# The comparison map of Stacks 0E50 is a quasi-isomorphism

Let `A` be Noetherian, `P` a complex of `A`-modules with finite cohomology, `I` a bounded complex
of injective `A`-modules and `ι : ε^* Ĩ ⟶ J` a quasi-isomorphism into a K-injective complex of
`𝒪_étale`-modules. This file proves that the chain-level comparison map

`ψ : (ε^* Hom^•_A(P, I)~)^lift ⟶ SheafHom^•(ε^* P̃, J)`

(`AlgebraicGeometry.AffineEtaleDuality.compMap`) is a quasi-isomorphism.

Quasi-isomorphy is tested on sections over the affine objects `V` of the small étale site, which
are enough objects. There, with `R = 𝒪(V)`, the source is `R ⊗_A Hom^•_A(P, I)` (the cartesian
isomorphism), the target is `Hom^•_A(P, J(V))` (the slice universal property), and `ψ` becomes
the base-change map `θ : R ⊗_A Hom^•_A(P, I) ⟶ Hom^•_A(P, R ⊗_A I)` followed by postcomposition
with `κ : R ⊗_A I ⟶ J(V)`. The map `θ` is a quasi-isomorphism by flat base change of Hom
complexes (`Stacks.FlatBaseChangeHom.quasiIso_theta`), and `κ` is a quasi-isomorphism between
K-injective complexes: `R ⊗_A I` is a bounded below complex of injective `A`-modules (étale base
change of injectives over a Noetherian ring) and `J(V)` is K-injective.

## Main results

* `AlgebraicGeometry.AffineEtaleDuality.compMapSections_square`: the local identification.
* `AlgebraicGeometry.AffineEtaleDuality.quasiIso_compMapSections`.
* `AlgebraicGeometry.AffineEtaleDuality.quasiIso_compMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.AffineEtaleDuality

variable {A : CommRingCat.{u}} {B : BigEtaleSite.{u}} {hX : B.Contains (Spec A)}

open Stacks.FlatBaseChangeHom

variable (V : Site A B hX)
  (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V))

/-- Sections over `V` of a complex of `𝒪_étale`-modules, as abelian groups. -/
abbrev sectionsFunctor : SheafOfModules.{u + 1} (O A B hX) ⥤ AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf (O A B hX) ⋙ sheafToPresheaf _ AddCommGrpCat.{u + 1} ⋙
    (evaluation _ AddCommGrpCat.{u + 1}).obj (op V)

variable (P I : CochainComplex (ModuleCat.{u} A) ℤ) {J : CochainComplex (Mod A B hX) ℤ}
  (ι : ((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)

/-- The cartesian isomorphism
`ulift (𝒪(V) ⊗_A Hom^•_A(P, I)) ≅ Γ(V, (ε^* Hom^•_A(P, I)~)^lift)`. -/
def cartComplexIso :
    (AddCommGrpCat.uliftFunctor.{u + 1}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (S₀ (ρc A B hX V) P I) ≅
      RingedSite.sectionComplex (Xs A B hX)
        (((Up A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (Fc (B := B) (hX := hX) (Dc P I))) V :=
  (AddCommGrpCat.uliftFunctor.{u + 1}.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    ((NatIso.mapHomologicalComplex (Functor.isoWhiskerRight (cartNatIso A B hX V hV)
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) (ComplexShape.up ℤ)).app (Dc P I))

/-- The comparison `𝒪(V) ⊗_A I ⟶ J(V)`: the cartesian isomorphism followed by `ι` on sections. -/
def kappa :
    REc (ρc A B hX V) I ⟶ ((secA A B hX V).mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
  (NatTrans.mapHomologicalComplex (cartNatIso A B hX V hV).hom (ComplexShape.up ℤ)).app I ≫
    ((secA A B hX V).mapHomologicalComplex (ComplexShape.up ℤ)).map ι

/-- The comparison map on sections over `V`. -/
abbrev compMapSections :
    RingedSite.sectionComplex (Xs A B hX)
        (((Up A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (Fc (B := B) (hX := hX) (Dc P I))) V ⟶
      RingedSite.sectionComplex (Xs A B hX) (Tc P J) V :=
  ((sheafToPresheaf _ AddCommGrpCat.{u + 1} ⋙
    (evaluation _ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((SheafOfModules.toSheaf (O A B hX)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (compMap ι))

omit hV in
/-- The cartesian map on a pure tensor: `b ⊗ m ↦ b • m|_V`. -/
lemma cartMap_tmul (M : ModuleCat.{u} A) (b : (Rc A B hX).obj (op V)) (m : M) :
    (cartMap A B hX M V).hom (b ⊗ₜ[A, ρc A B hX V] m) =
      b • (show evc A B hX V ((epsT A B hX).obj M) from unitSectionAt A B hX M V m) := by
  have h : (b ⊗ₜ[A, ρc A B hX V] m : (ModuleCat.extendScalars (ρc A B hX V)).obj M) =
      b • (show (ModuleCat.extendScalars (ρc A B hX V)).obj M from
        (1 : (Rc A B hX).obj (op V)) ⊗ₜ[A, ρc A B hX V] m) :=
    (congrArg (fun r : (Rc A B hX).obj (op V) => r ⊗ₜ[A, ρc A B hX V] m) (mul_one b)).symm.trans
      (ModuleCat.ExtendScalars.smul_tmul (ρc A B hX V) b 1 m).symm
  rw [h, map_smul, cartMap_one_tmul]

/-- The two sides of `compMapSections_square` agree on a pure tensor `b ⊗ d`, evaluated at
`m : P^p` in the component `(p, q)` with `p + n = q`. -/
lemma square_tmul (n : ℤ) (b : (Rc A B hX).obj (op V)) (d : Cochain P I n) (p q : ℤ)
    (hpq : p + n = q) (m : P.X p) :
    (((sectionsHomIso P J V).hom.f n ((compMapSections V P I ι).f n
      ((cartComplexIso V hV P I).hom.f n (ULift.up (b ⊗ₜ[A, ρc A B hX V] d))))).down.v
        p q hpq).hom m =
      (((homComplexMap (𝟙 P) (kappa V hV I ι)).f n
        (thetaCochain (ρc A B hX V) P I b d)).v p q hpq).hom m := by
  have hR : (((homComplexMap (𝟙 P) (kappa V hV I ι)).f n
        (thetaCochain (ρc A B hX V) P I b d)).v p q hpq).hom m =
      (show (J.X q).val.obj (op V) from (b • (show evc A B hX V (J.X q) from
        (ι.f q).val.app (op V) (unitSectionAt A B hX (I.X q) V ((d.v p q hpq).hom m))))) := by
    have h1 := cochainMap_v (𝟙 P) (kappa V hV I ι) n p q hpq (thetaCochain (ρc A B hX V) P I b d)
    rw [thetaCochain_v, HomologicalComplex.id_f, Category.id_comp] at h1
    refine (congrArg (fun f => f.hom m) h1).trans ?_
    show ((kappa V hV I ι).f q).hom ((mulApp (ρc A B hX V) b (I.X q)).hom
      (((unitRE (ρc A B hX V)).app (I.X q)).hom ((d.v p q hpq).hom m))) = _
    rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
    show ((ι.f q).val.app (op V)).hom ((cartMap A B hX (I.X q) V).hom
      (b • (show (ModuleCat.extendScalars (ρc A B hX V)).obj (I.X q) from
        (1 : (Rc A B hX).obj (op V)) ⊗ₜ[A, ρc A B hX V] (d.v p q hpq).hom m))) = _
    rw [map_smul, cartMap_one_tmul]
    exact map_smul ((ι.f q).val.app (op V)).hom (show (O A B hX).obj.obj (op V) from b) _
  refine Eq.trans ?_ hR.symm
  let b' : (O A B hX).obj.obj (op V) := b
  have hL1 : (compMapSections V P I ι).f n ((cartComplexIso V hV P I).hom.f n
      (ULift.up (b ⊗ₜ[A, ρc A B hX V] d))) =
      (show ((Tc P J).X n).val.obj (op V) from
        b' • ((Tc P J).X n).val.map (toTop A B hX V).op (topSection ι d)) := by
    show (phiN ι n).val.app (op V) (ULift.up ((cartMap A B hX ((Dc P I).X n) V).hom
      (b ⊗ₜ[A, ρc A B hX V] d))) = _
    refine (congrArg (fun x => (phiN ι n).val.app (op V) (ULift.up x))
      (cartMap_tmul V ((Dc P I).X n) b d)).trans ?_
    show (phiN ι n).val.app (op V) (b' •
      ULift.up (unitSectionAt A B hX ((Dc P I).X n) V d)) = _
    refine (map_smul ((phiN ι n).val.app (op V)).hom b' _).trans ?_
    refine congrArg (b' • ·) ?_
    show (phiN ι n).val.app (op V) ((((Up A B hX).obj ((epsT A B hX).obj ((Dc P I).X n))).val.map
      (toTop A B hX V).op (ULift.up (unitSection A B hX ((Dc P I).X n) d)))) = _
    refine (PresheafOfModules.naturality_apply (phiN ι n).val (toTop A B hX V).op _).trans ?_
    exact congrArg (((Tc P J).X n).val.map (toTop A B hX V).op) (phiN_app_top ι n d)
  let sV := (RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).sectionsIso V
  let sT := (RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).sectionsIso (top A B hX)
  let y := unitSectionAt A B hX (P.X p) V m
  let s := ((Tc P J).X n).val.map (toTop A B hX V).op (topSection ι d)
  have h2 := congrArg (fun x => (((homComplexSliceIso P J V).hom.f n (sV.hom.f n x)).down.v
    p q hpq).hom m) hL1
  refine h2.trans ?_
  refine (congrArg (fun φ => φ.hom m)
    (homComplexSliceIso_hom_apply P J V n (sV.hom.f n (b' • s)) p q hpq)).trans ?_
  refine (sliceHomAddEquiv_apply (P.X p) (J.X q) V _ m).trans ?_
  refine ((RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).smul_natural V b' n p q hpq s
    (𝟙 V) y).trans ?_
  have h3 := (RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).restrict_natural
    (toTop A B hX V) n p q hpq (topSection ι d) (𝟙 V) y
  have hXV : (((sV.hom.f n s).v p q hpq).val.app (op (Over.mk (𝟙 V)))) y =
      (ι.f q).val.app (op V) (unitSectionAt A B hX (I.X q) V ((d.v p q hpq).hom m)) := by
    refine h3.symm.trans ?_
    have h4 := congrArg (fun z => ((z.v p q hpq).val.app
      (op (Over.mk (𝟙 V ≫ toTop A B hX V)))) y) (sectionsIso_hom_topSection ι d)
    refine h4.trans ?_
    have h5 := congrArg (fun z => (z.val.app (op (Over.mk (𝟙 V ≫ toTop A B hX V)))) y)
      (topCochain_v ι d p q hpq)
    refine h5.trans ?_
    show (ι.f q).val.app (op V) (((epsT A B hX).map (d.v p q hpq)).val.app (op V) y) = _
    exact congrArg ((ι.f q).val.app (op V)) (unitSectionAt_naturality A B hX (d.v p q hpq) V m)
  have hb : (Stacks.SheafOfModules.Tensor.ringSheaf (Xs A B hX).O).obj.map (𝟙 V).op b' = b' := by
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl
  exact congrArg₂ (fun r x => r • x) hb hXV

/-- **On sections over an affine `V`, the comparison map is `θ` followed by `κ`**, up to the
cartesian isomorphism and the description of the sections of the internal Hom complex. -/
lemma compMapSections_square :
    (cartComplexIso V hV P I).hom ≫ compMapSections V P I ι ≫ (sectionsHomIso P J V).hom =
      (AddCommGrpCat.uliftFunctor.{u + 1}.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (theta (ρc A B hX V) P I ≫ homComplexMap (𝟙 P) (kappa V hV I ι)) := by
  ext n : 1
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun ⟨x⟩ => ?_)
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy =>
    exact (map_add _ (ULift.up x) (ULift.up y)).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ (ULift.up x) (ULift.up y)).symm)
  | tmul b d =>
    refine ULift.ext _ _ (Cochain.ext _ _ (fun p q hpq => ?_))
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    exact square_tmul V hV P I ι n b d p q hpq m

/-- `κ : 𝒪(V) ⊗_A I ⟶ J(V)` is a quasi-isomorphism. -/
lemma quasiIso_kappa [J.IsKInjective] [QuasiIso ι] : QuasiIso (kappa V hV I ι) := by
  have : IsIso ((NatTrans.mapHomologicalComplex (cartNatIso A B hX V hV).hom
      (ComplexShape.up ℤ)).app I) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex (cartNatIso A B hX V hV)
      (ComplexShape.up ℤ)).app I).hom)
  have := quasiIso_secA_map A B hX V hV I J ι
  exact quasiIso_comp _ _

include hV in
/-- **On sections over an affine object, the comparison map is a quasi-isomorphism**, for `P`
with finite cohomology and `I` a bounded complex of injectives over a Noetherian ring. -/
theorem quasiIso_compMapSections [IsNoetherianRing A] (a b : ℤ) [I.IsStrictlyGE a]
    [I.IsStrictlyLE b] [∀ k, Injective (I.X k)] [J.IsKInjective] [QuasiIso ι]
    (hP : ∀ i, Module.Finite A (P.homology i)) :
    QuasiIso (compMapSections V P I ι) := by
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  have : (REc (ρc A B hX V) I).IsKInjective := isKInjective_REc A B hX V hV I a
  have : CochainComplex.IsKInjective
      (((secA A B hX V).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    isKInjective_secA A B hX V J
  have := quasiIso_theta (ρc A B hX V) (flat_ρc A B hX V hV) P I a b hP
  have := quasiIso_kappa V hV I ι
  have := homComplexMap_quasiIso (𝟙 P) (kappa V hV I ι)
  have hsq : QuasiIso ((cartComplexIso V hV P I).hom ≫ compMapSections V P I ι ≫
      (sectionsHomIso P J V).hom) := by
    rw [compMapSections_square]
    infer_instance
  have := quasiIso_of_comp_left (cartComplexIso V hV P I).hom
    (compMapSections V P I ι ≫ (sectionsHomIso P J V).hom)
  exact quasiIso_of_comp_right _ (sectionsHomIso P J V).hom

omit V in
/-- **The chain-level comparison map is a quasi-isomorphism**:
`(ε^* Hom^•_A(P, I)~)^lift ⟶ SheafHom^•(ε^* P̃, J)` for `P` with finite cohomology, `I` a bounded
complex of injective modules over a Noetherian ring, and `ι : ε^* Ĩ ⟶ J` a quasi-isomorphism into
a K-injective complex. -/
theorem quasiIso_compMap [IsNoetherianRing A] (a b : ℤ) [I.IsStrictlyGE a]
    [I.IsStrictlyLE b] [∀ k, Injective (I.X k)] [J.IsKInjective] [QuasiIso ι]
    (hP : ∀ i, Module.Finite A (P.homology i)) :
    QuasiIso (compMap (P := P) ι) := by
  refine Stacks.SheafOfModules.quasiIso_of_hasEnoughObjects
    (SmallEtale.hasEnoughObjects_isAffine B (Spec A) hX) (compMap ι) (fun V hV => ?_)
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{u + 1} ((O A B hX).obj.obj (op V))) AddCommGrpCat.{u + 1})).1
    (quasiIso_compMapSections V hV P I ι a b hP)

end AlgebraicGeometry.AffineEtaleDuality

end
