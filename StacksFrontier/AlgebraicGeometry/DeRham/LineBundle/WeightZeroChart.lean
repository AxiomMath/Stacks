module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.AffineChart
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.GradedDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistCompatible
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.LaurentChartForms
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamComplexIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection
public import StacksFrontier.RingTheory.DeRham.LaurentResidueTransport

/-!
# The weight-zero forms of the complement of the zero section over a chart

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `π : L^⋆ ⟶ X` the
complement of the zero section of its line bundle. A *base chart* is an affine open `U` of `X`
mapping into an affine open `V` of `S`, together with a Laurent chart of `L` over `U`. Over a
base chart the functions on `π⁻¹U` are `A[T;T⁻¹]` for `A = Γ(X, U)`, as an algebra over
`R = Γ(S, V)`, and the relative forms on `X` over `U` and on `L^⋆` over `π⁻¹U` are the Kähler
forms of `A` and of `Γ(L^⋆, π⁻¹U)` over `R`.

This file reads the local computation of Stacks 0FUF through these identifications and packages
it as a `LaurentDeRham.FormsModel` of the base chart: the sections over `U` of the weight-zero
part `Ω^p_{L^⋆/S,0}` of the pushed-forward forms are, uniquely, the forms `π^*α + π^*β ∧ dlog u`
for `u` any invertible function on `π⁻¹U` of degree one, with `α` and `β` relative forms on `U`.
Up to the sign `(-1)^p` of graded commutativity this is `π^*α + dlog u ∧ π^*β`, the description
in the proof of Stacks 0FUF.

## Main definitions

* `Stacks.LineBundle.Situation.BaseChart`: an affine open of `X` mapping into an affine open of
  `S`, with a Laurent chart of the line bundle over it.
* `Stacks.LineBundle.Situation.pullbackForms`, `Stacks.LineBundle.Situation.pullbackG`: the
  pullback of relative forms along `π`, on sections over an open of `X`.
* `Stacks.LineBundle.Situation.BaseChart.formsLF`, `formsXF`: the identifications of the
  relative forms of `L^⋆` over `π⁻¹U` and of `X` over `U` with Kähler forms.
* `Stacks.LineBundle.Situation.BaseChart.model`: the forms model of a base chart.

## Main results

* `Stacks.LineBundle.Situation.BaseChart.formsLF_pullbackG`: the pullback of forms is the
  pullback of Kähler forms along `Γ(X, U) → Γ(L^⋆, π⁻¹U)`.
* `Stacks.LineBundle.Situation.BaseChart.isDlog_laurentDlog`,
  `Stacks.LineBundle.Situation.BaseChart.unit_mem`: the coordinate of a base chart is a unit of
  degree one, and `d log` of it is the logarithmic one-form of the model.

## References

* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry KaehlerDifferential

universe u

namespace Stacks.AlgebraicGeometry.AffineOpenDeRham

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} {V : S.Opens}
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)

include hU hV in
/-- **The comparison of forms over an affine open commutes with the de Rham differential**, on
an arbitrary Kähler form. -/
theorem deRhamComplex_d_formsSectionsIso_inv (p : ℕ)
    (x : ⋀[Γ(X, U)]^p ↥(CommRingCat.KaehlerDifferential (f.appLE V U e))) :
    ((f.deRhamComplex.d p (p + 1)).val.app (op U)) ((formsSectionsIso f hU hV e p).inv x) =
      (formsSectionsIso f hU hV e (p + 1)).inv
        (((AffineDifferentialsIso.ringDeRhamComplex (f.appLE V U e)).d p (p + 1)).hom x) :=
  congrArg (fun φ => φ.hom x) (sectionsAbTermMap_comm f hU hV e p)

include hU hV in
/-- **The comparison of forms over an affine open commutes with the de Rham differential**, read
through its forward map. -/
theorem formsSectionsIso_hom_deRhamComplex_d (p : ℕ)
    (y : Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), U)) :
    (formsSectionsIso f hU hV e (p + 1)).hom (((f.deRhamComplex.d p (p + 1)).val.app (op U)) y) =
      ((AffineDifferentialsIso.ringDeRhamComplex (f.appLE V U e)).d p (p + 1)).hom
        ((formsSectionsIso f hU hV e p).hom y) := by
  have h := deRhamComplex_d_formsSectionsIso_inv f hU hV e p ((formsSectionsIso f hU hV e p).hom y)
  rw [Iso.hom_inv_id_apply] at h
  rw [h]
  exact (formsSectionsIso f hU hV e (p + 1)).inv_hom_id_apply _

include hU hV in
/-- The algebraic de Rham differential of `Γ(S, V) → Γ(X, U)` is `deRhamDifferential`. -/
theorem ringDeRhamComplex_d_apply (p : ℕ)
    (x : ⋀[Γ(X, U)]^p ↥(CommRingCat.KaehlerDifferential (f.appLE V U e))) :
    letI := (f.appLE V U e).hom.toAlgebra
    ((AffineDifferentialsIso.ringDeRhamComplex (f.appLE V U e)).d p (p + 1)).hom x =
      deRhamDifferential (A := Γ(S, V)) (B := Γ(X, U)) p x := by
  let := (f.appLE V U e).hom.toAlgebra
  show ((KaehlerDifferential.deRhamComplex Γ(S, V) Γ(X, U)).d p (p + 1)).hom x = _
  rw [KaehlerDifferential.deRhamComplex_d]
  rfl

include hU hV in
/-- **The comparison of forms over an affine open is multiplicative**: it carries the product of
relative forms to the wedge product of Kähler forms. -/
theorem formsSectionsIso_hom_mul (p q : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), U))
    (β : Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), U)) :
    (formsSectionsIso f hU hV e (p + q)).hom
        ((eqToHom (congrArg (Stacks.AffineExteriorPower.pieceModules
          (Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f)))
          (Nat.cast_add p q).symm)).val.app (op U)
          (((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f)).mul
            (p : ℤ) q).app (op U) α β)) =
      exteriorPower.wedgeMul p q ((formsSectionsIso f hU hV e p).hom α)
        ((formsSectionsIso f hU hV e q).hom β) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentials f
  exact (congrArg (exteriorPower.map (p + q) (kaehlerSectionsEquiv f hU hV e).symm.toLinearMap)
    (Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso_hom_mul
      (Scheme.Hom.relativeDifferentials f) hU (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)
      p q α β)).trans (exteriorPower.wedgeMul_map p q _ _ _)

include hU hV in
/-- **The comparison of forms over an affine open carries the product by a one-form to the
wedge product**, with no transport of degrees. -/
theorem formsSectionsIso_hom_mul_one (p : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), U))
    (β : Γ(Scheme.Hom.relativeDifferentialForms f ((1 : ℕ) : ℤ), U)) :
    (formsSectionsIso f hU hV e (p + 1)).hom
        (((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f)).mul
          (p : ℤ) 1).app (op U) α β) =
      exteriorPower.wedgeMul p 1 ((formsSectionsIso f hU hV e p).hom α)
        ((formsSectionsIso f hU hV e 1).hom β) := by
  refine Eq.trans ?_ (formsSectionsIso_hom_mul f hU hV e p 1 α β)
  congr 1

include hU hV in
/-- **The comparison of forms over an affine open carries the constant form `1` to the empty
wedge.** -/
theorem formsSectionsIso_hom_one :
    (formsSectionsIso f hU hV e 0).hom ((Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op U)) =
      exteriorPower.ιMulti Γ(X, U) 0 Fin.elim0 := by
  have h := formsSectionsIso_inv_ιMulti_d f hU hV e 0 Fin.elim0
  have h2 : (fun i : Fin 0 => CommRingCat.KaehlerDifferential.d (f := f.appLE V U e)
      (Fin.elim0 i : Γ(X, U))) = Fin.elim0 := funext fun i => i.elim0
  rw [h2] at h
  rw [← Iso.inv_hom_id_apply (formsSectionsIso f hU hV e 0)
    (exteriorPower.ιMulti Γ(X, U) 0 Fin.elim0)]
  exact congrArg (formsSectionsIso f hU hV e 0).hom h.symm

include hU hV in
/-- **The comparison of forms over an affine open carries the exact one-form `d b` to
`d b`.** -/
theorem formsSectionsIso_hom_exactOne (b : Γ(X, U)) :
    (formsSectionsIso f hU hV e 1).hom
        (_root_.AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras f) (op U) b) =
      exteriorPower.ιMulti Γ(X, U) 1 fun _ => CommRingCat.KaehlerDifferential.d b := by
  have h := formsSectionsIso_inv_ιMulti_d f hU hV e 1 fun _ => b
  rw [← Iso.inv_hom_id_apply (formsSectionsIso f hU hV e 1)
    (exteriorPower.ιMulti Γ(X, U) 1 fun _ => CommRingCat.KaehlerDifferential.d b), h]
  congr 1
  rw [Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd]
  exact (eq_of_heq ((Scheme.Hom.deRhamAlgebras f).exterior.one_mul 1 (op U) _)).symm

include hU hV in
/-- The comparison of forms over an affine open is linear over the functions there. -/
theorem formsSectionsIso_hom_smul (p : ℕ) (b : Γ(X, U))
    (ω : Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), U)) :
    (formsSectionsIso f hU hV e p).hom (b • ω) = b • (formsSectionsIso f hU hV e p).hom ω :=
  map_smul _ _ _

end Stacks.AlgebraicGeometry.AffineOpenDeRham

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The pullback of relative forms along `π : L^⋆ ⟶ X`**, on sections over an open `U` of `X`:
the degree-`p` component of the canonical map of Tag 07HX for the square of `π` over `S`, with its
value seated at `π⁻¹U`. -/
def Situation.pullbackForms (p : ℕ) (U : D.X.Opens)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    Γ(Scheme.Hom.relativeDifferentialForms (D.laurentSpectrumToBase ≫ D.f) (p : ℤ),
      D.laurentSpectrumToBase ⁻¹ᵁ U) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardSections
    D.laurentSpectrumToBase D.f (D.laurentSpectrumToBase ≫ D.f) (𝟙 D.S)
    ((Category.comp_id (D.laurentSpectrumToBase ≫ D.f)).symm) p ω

/-- The pullback of relative forms along `π` is additive. -/
theorem Situation.pullbackForms_add (p : ℕ) (U : D.X.Opens)
    (ω χ : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    D.pullbackForms p U (ω + χ) = D.pullbackForms p U ω + D.pullbackForms p U χ :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardSections_add _ _ _ _ _ p ω χ

/-- The pullback of relative forms along `π` is semilinear over `π^♯ : Γ(X, U) → Γ(L^⋆, π⁻¹U)`. -/
theorem Situation.pullbackForms_smul (p : ℕ) (U : D.X.Opens) (b : Γ(D.X, U))
    (ω : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    D.pullbackForms p U (b • ω) = (D.laurentSpectrumToBase.app U).hom b • D.pullbackForms p U ω :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardSections_smul _ _ _ _ _ p b ω

/-- The pullback of relative forms along `π` carries `0` to `0`. -/
theorem Situation.pullbackForms_zero (p : ℕ) (U : D.X.Opens) : D.pullbackForms p U 0 = 0 := by
  have h := D.pullbackForms_add p U 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- The sections over `U` of the pushed-forward forms of `L^⋆`, read as the sections over `π⁻¹U`
of the relative forms of `π ≫ f`: the same group in two spellings. -/
def Situation.secG (p : ℕ) (U : D.X.Opens) :
    Γ(D.gradedAmbient p, U) ≃+
      Γ(Scheme.Hom.relativeDifferentialForms (D.laurentSpectrumToBase ≫ D.f) (p : ℤ),
        D.laurentSpectrumToBase ⁻¹ᵁ U) :=
  AddEquiv.refl _

/-- Read over `π⁻¹U`, the product of a form by a one-form is the product of relative forms of
`π ≫ f`. -/
theorem Situation.secG_gradedWedge (p : ℕ) (U : D.X.Opens) (η : Γ(D.gradedAmbient p, U))
    (ξ : Γ(D.gradedAmbient 1, U)) :
    D.secG (p + 1) U (D.gradedWedge p U η ξ) =
      ((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials
        (D.laurentSpectrumToBase ≫ D.f))).mul (p : ℤ) 1).app
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) (D.secG p U η) (D.secG 1 U ξ) :=
  rfl

/-- Read over `π⁻¹U`, the differential of a function is its exact one-form relative to `π ≫ f`. -/
theorem Situation.secG_gradedD (U : D.X.Opens)
    (b : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) :
    D.secG 1 U (D.gradedD U b) =
      _root_.AlgebraicGeometry.SheafOfModules.exactOne
        (Scheme.Hom.deRhamAlgebras (D.laurentSpectrumToBase ≫ D.f))
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) b :=
  rfl

/-- Read over `π⁻¹U`, the constant form `1` is the unit of the exterior algebra of `π ≫ f`. -/
theorem Situation.secG_gradedOne (U : D.X.Opens) :
    D.secG 0 U (D.gradedOne U) =
      (Scheme.Hom.deRhamAlgebras (D.laurentSpectrumToBase ≫ D.f)).exterior.one.eval
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) :=
  rfl

/-- The forms on `π⁻¹U`, read as sections over `U` of the pushed-forward forms. -/
def Situation.secF (p : ℕ) (U : D.X.Opens) :
    (D.laurentForms (p : ℤ)).val.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) ≃+
      Γ(D.gradedAmbient p, U) :=
  AddEquiv.refl _

/-- The functions on an open of `L^⋆`, in the two spellings of its structure sheaf. -/
def Situation.secR (W : D.laurentSpectrum.Opens) :
    D.laurentSpectrum.sheaf.obj.obj (op W) ≃+* Γ(D.laurentSpectrum, W) :=
  RingEquiv.refl _

/-- Read over `π⁻¹U`, the product of a form by a function on `π⁻¹U` is scalar multiplication. -/
theorem Situation.secG_gradedSmul (p : ℕ) (U : D.X.Opens)
    (b : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω : Γ(D.gradedAmbient p, U)) :
    D.secG p U (D.gradedSmul p U b ω) =
      D.secR (D.laurentSpectrumToBase ⁻¹ᵁ U) b • D.secG p U ω :=
  rfl

/-- The `𝒪_X`-action on the pushed-forward forms is multiplication by the pulled-back function. -/
theorem Situation.smul_eq_gradedSmul (p : ℕ) (U : D.X.Opens) (r : Γ(D.X, U))
    (ω : Γ(D.gradedAmbient p, U)) :
    r • ω = D.gradedSmul p U ((D.secR _).symm ((D.laurentSpectrumToBase.app U).hom r)) ω :=
  rfl

/-- Read over `π⁻¹U`, the differential of the pushed-forward forms is the relative de Rham
differential of `π ≫ f`. -/
theorem Situation.secG_gradedDiff (p : ℕ) (U : D.X.Opens) (ω : Γ(D.gradedAmbient p, U)) :
    D.secG (p + 1) U (D.gradedDiff p U ω) =
      (((D.laurentSpectrumToBase ≫ D.f).deRhamComplex.d p (p + 1)).val.app
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) (D.secG p U ω) :=
  rfl

/-- **The relative de Rham differential of `X` over `S`**, on sections over an open `U` of `X`. -/
def Situation.dX (p : ℕ) (U : D.X.Opens)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), U) :=
  ((D.f.deRhamComplex.d p (p + 1)).val.app (op U)) α

/-- `Stacks.LineBundle.Situation.dX` is the de Rham differential of `f` on sections over `U`. -/
theorem Situation.dX_eq (p : ℕ) (U : D.X.Opens)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    D.dX p U α = ((D.f.deRhamComplex.d p (p + 1)).val.app (op U)) α :=
  rfl

/-- The pullback of forms along `π`, with its value read as a section over `U` of the
pushed-forward forms. -/
def Situation.pullbackG (p : ℕ) (U : D.X.Opens)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) : Γ(D.gradedAmbient p, U) :=
  (D.secG p U).symm (D.pullbackForms p U α)

/-- **A base chart**: an affine open `U` of `X` lying over an affine open `V` of `S`, together
with a Laurent chart of the line bundle over `U`. Such opens form a basis of `X`. -/
structure Situation.BaseChart extends D.AffineChart where
  /-- A Laurent chart of the line bundle over `U`. -/
  chart : D.LaurentChart U.1

namespace Situation.BaseChart

variable {D} (c : D.BaseChart)

/-- The functions on `π⁻¹U`. -/
abbrev B : Type u := Γ(D.laurentSpectrum, D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)

/-- The open `π⁻¹U` of `L^⋆` lies over the affine open `V` of `S`. -/
theorem preimage_le :
    D.laurentSpectrumToBase ⁻¹ᵁ c.U.1 ≤ (D.laurentSpectrumToBase ≫ D.f) ⁻¹ᵁ c.V.1 :=
  D.laurentPreimage_le_laurentToBase_preimage c.le

/-- The open `π⁻¹U` of `L^⋆` is affine. -/
theorem isAffineOpen_preimage : IsAffineOpen (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1) :=
  D.isAffineOpen_laurentPreimage c.U.2

/-- `Γ(L^⋆, π⁻¹U)` as a `Γ(S, V)`-algebra. -/
abbrev algebraRB : Algebra c.R c.B :=
  ((D.laurentSpectrumToBase ≫ D.f).appLE c.V.1 _ c.preimage_le).hom.toAlgebra

/-- `Γ(L^⋆, π⁻¹U)` as a `Γ(X, U)`-algebra, along `π`. -/
abbrev algebraAB : Algebra c.A c.B := (D.laurentSpectrumToBase.app c.U.1).hom.toAlgebra

attribute [local instance] Situation.AffineChart.algebraRA algebraRB algebraAB

/-- The algebras `Γ(S, V) → Γ(X, U) → Γ(L^⋆, π⁻¹U)` form a scalar tower. -/
theorem isScalarTower : IsScalarTower c.R c.A c.B :=
  IsScalarTower.of_algebraMap_eq fun r => by
    show ((D.laurentSpectrumToBase ≫ D.f).appLE c.V.1 _ c.preimage_le).hom r =
      (D.laurentSpectrumToBase.app c.U.1).hom ((D.f.appLE c.V.1 c.U.1 c.le).hom r)
    rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

attribute [local instance] isScalarTower

/-- **The affine local model of `L^⋆` over a base chart**, as an isomorphism of
`Γ(X, U)`-algebras `Γ(X, U)[T;T⁻¹] ≃ Γ(L^⋆, π⁻¹U)`. -/
def equiv : LaurentPolynomial c.A ≃ₐ[c.A] c.B :=
  AlgEquiv.ofRingEquiv (f := c.chart.sectionsRingEquiv) fun a => by
    rw [LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Situation.LaurentChart.sectionsRingEquiv_apply,
      Situation.LaurentChart.hom_C, D.laurentSectionsIso_hom_laurentStructureHom c.U a]
    rfl

/-- The affine local model is the ring isomorphism of the Laurent chart. -/
theorem equiv_apply (q : LaurentPolynomial c.A) : c.equiv q = c.chart.sectionsRingEquiv q := rfl

/-- The Kähler differentials of `Γ(S, V) → Γ(L^⋆, π⁻¹U)`. -/
abbrev ΩB : ModuleCat.{u} c.B :=
  CommRingCat.KaehlerDifferential ((D.laurentSpectrumToBase ≫ D.f).appLE c.V.1 _ c.preimage_le)

/-- The differential of `Γ(S, V) → Γ(X, U)` in the two spellings of the Kähler differentials. -/
theorem d_eq_D (b : c.A) :
    (CommRingCat.KaehlerDifferential.d (f := D.f.appLE c.V.1 c.U.1 c.le) b : c.ΩA) =
      KaehlerDifferential.D c.R c.A b :=
  rfl

/-- **The relative forms of `L^⋆` over `π⁻¹U`, as Kähler forms** `⋀^p Ω[Γ(L^⋆, π⁻¹U)⁄Γ(S, V)]`. -/
abbrev formsL (p : ℕ) :
    ModuleCat.of c.B Γ(Scheme.Hom.relativeDifferentialForms (D.laurentSpectrumToBase ≫ D.f)
        (p : ℤ), D.laurentSpectrumToBase ⁻¹ᵁ c.U.1) ≅ ModuleCat.of c.B (⋀[c.B]^p c.ΩB) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso (D.laurentSpectrumToBase ≫ D.f)
    c.isAffineOpen_preimage c.V.2 c.preimage_le p

/-- The pullback of forms over a base chart is semilinear over `π^♯`. -/
theorem formsL_pullbackForms_smul (p : ℕ) (a0 : c.A) (y : ⋀[c.A]^p c.ΩA) :
    (c.formsL p).hom (D.pullbackForms p c.U.1 ((c.formsX p).inv (a0 • y : ⋀[c.A]^p c.ΩA))) =
      (D.laurentSpectrumToBase.app c.U.1).hom a0 •
        (c.formsL p).hom (D.pullbackForms p c.U.1 ((c.formsX p).inv y)) := by
  have hs := Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_pushforwardSections_smul
    D.laurentSpectrumToBase D.f (D.laurentSpectrumToBase ≫ D.f) (𝟙 D.S) c.U.2
    c.isAffineOpen_preimage c.V.2 c.V.2 c.le c.preimage_le
    ((Category.comp_id (D.laurentSpectrumToBase ≫ D.f)).symm) p a0 y
  rw [Situation.pullbackForms, Situation.pullbackForms]
  convert hs using 1

/-- The pullback of forms over a base chart on a wedge of differentials. -/
theorem formsL_pullbackForms_ιMulti (p : ℕ) (a : Fin p → c.A) :
    (c.formsL p).hom (D.pullbackForms p c.U.1 ((c.formsX p).inv
      (exteriorPower.ιMulti c.A p fun i => CommRingCat.KaehlerDifferential.d (a i) :
        ⋀[c.A]^p c.ΩA))) =
      (exteriorPower.ιMulti c.B p fun i =>
        CommRingCat.KaehlerDifferential.d ((D.laurentSpectrumToBase.app c.U.1).hom (a i)) :
          ⋀[c.B]^p c.ΩB) := by
  have h :=
    AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_deRhamFormsPushforwardHom_ιMulti_d
      D.laurentSpectrumToBase D.f (D.laurentSpectrumToBase ≫ D.f) (𝟙 D.S) c.U.2
      c.isAffineOpen_preimage c.V.2 c.V.2 c.le c.preimage_le
      ((Category.comp_id (D.laurentSpectrumToBase ≫ D.f)).symm) p a
  rw [Situation.pullbackForms,
    Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardSections_apply]
  convert h using 1

/-- The pullback of Kähler forms on a generator. -/
theorem mapExteriorPower_gen (p : ℕ) (a : Fin (p + 1) → c.A) :
    mapExteriorPower c.R c.A c.B p (a 0 • exteriorPower.ιMulti c.A p fun i =>
        KaehlerDifferential.D c.R c.A (a i.succ)) =
      (D.laurentSpectrumToBase.app c.U.1).hom (a 0) • exteriorPower.ιMulti c.B p fun i =>
        KaehlerDifferential.D c.R c.B ((D.laurentSpectrumToBase.app c.U.1).hom (a i.succ)) := by
  rw [LinearMap.map_smul, mapExteriorPower_ιMulti, ← algebraMap_smul c.B (a 0)]
  refine congrArg (fun z => algebraMap c.A c.B (a 0) • z) ?_
  refine congrArg (exteriorPower.ιMulti c.B p) (funext fun i => ?_)
  exact map_D c.R c.R c.A c.B (a i.succ)

/-- A characterization of the pullback of forms over a base chart by its values on the
generators `a₀ · d a₁ ∧ ⋯ ∧ d a_p`. -/
theorem formsL_pullbackForms_eq_of_gen (p : ℕ) (G : ⋀[c.A]^p c.ΩA → ⋀[c.B]^p c.ΩB)
    (hadd : ∀ x y, G (x + y) = G x + G y)
    (hgen : ∀ a : Fin (p + 1) → c.A,
      G (a 0 • exteriorPower.ιMulti c.A p fun i => CommRingCat.KaehlerDifferential.d (a i.succ)) =
        (D.laurentSpectrumToBase.app c.U.1).hom (a 0) • exteriorPower.ιMulti c.B p fun i =>
          CommRingCat.KaehlerDifferential.d ((D.laurentSpectrumToBase.app c.U.1).hom (a i.succ)))
    (x : ⋀[c.A]^p c.ΩA) :
    (c.formsL p).hom (D.pullbackForms p c.U.1 ((c.formsX p).inv x)) = G x := by
  let G' : ⋀[c.A]^p c.ΩA →+ ⋀[c.B]^p c.ΩB := AddMonoidHom.mk' G hadd
  let F : ⋀[c.A]^p c.ΩA →+ ⋀[c.B]^p c.ΩB :=
    AddMonoidHom.mk' (fun x => (c.formsL p).hom (D.pullbackForms p c.U.1 ((c.formsX p).inv x)))
      fun x y => by
        rw [map_add, Situation.pullbackForms_add, map_add]
  have hD : Submodule.span c.A
      (Set.range fun b : c.A => (CommRingCat.KaehlerDifferential.d b : c.ΩA)) = ⊤ :=
    @span_range_derivation c.R c.A _ _ c.algebraRA
  have key : F = G' := Stacks.AlgebraicGeometry.AffineOpenDeRham.addMonoidHom_ext_of_span_int_eq_top
    (Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ)
      (fun b : c.A => (CommRingCat.KaehlerDifferential.d b : c.ΩA)) hD p) (by
        rintro _ ⟨a, rfl⟩
        simp only [F, G', AddMonoidHom.mk'_apply]
        have h1 := c.formsL_pullbackForms_smul p (a 0)
          (exteriorPower.ιMulti c.A p fun i => CommRingCat.KaehlerDifferential.d (a i.succ))
        rw [h1]
        refine (congrArg (fun z => (D.laurentSpectrumToBase.app c.U.1).hom (a 0) • z)
          (c.formsL_pullbackForms_ιMulti p (fun i => a i.succ))).trans ?_
        exact (hgen a).symm)
  exact DFunLike.congr_fun key x

/-- **The pullback of forms along `π`, read through the two identifications, is the pullback
of Kähler forms along `Γ(X, U) → Γ(L^⋆, π⁻¹U)`.** -/
theorem formsL_pullbackForms (p : ℕ) (x : ⋀[c.A]^p c.ΩA) :
    (c.formsL p).hom (D.pullbackForms p c.U.1 ((c.formsX p).inv x)) =
      mapExteriorPower c.R c.A c.B p x :=
  c.formsL_pullbackForms_eq_of_gen p _ (fun _ _ => map_add _ _ _)
    (fun a => c.mapExteriorPower_gen p a) x
/-- **Over a base chart the identification of the forms of `L^⋆` carries the product by a
one-form to the wedge product.** -/
theorem formsL_mul_one (p : ℕ)
    (x : Γ(Scheme.Hom.relativeDifferentialForms (D.laurentSpectrumToBase ≫ D.f) (p : ℤ),
      D.laurentSpectrumToBase ⁻¹ᵁ c.U.1))
    (y : Γ(Scheme.Hom.relativeDifferentialForms (D.laurentSpectrumToBase ≫ D.f) ((1 : ℕ) : ℤ),
      D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)) :
    (c.formsL (p + 1)).hom
        (((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials
          (D.laurentSpectrumToBase ≫ D.f))).mul (p : ℤ) 1).app
          (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)) x y) =
      exteriorPower.wedgeMul p 1 ((c.formsL p).hom x) ((c.formsL 1).hom y) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_mul_one
    (D.laurentSpectrumToBase ≫ D.f) c.isAffineOpen_preimage c.V.2 c.preimage_le p x y

/-- **Over a base chart the identification of the forms of `L^⋆` carries the exact one-form of a
function to its Kähler differential.** -/
theorem formsL_exactOne (b : c.B) :
    (c.formsL 1).hom (_root_.AlgebraicGeometry.SheafOfModules.exactOne
        (Scheme.Hom.deRhamAlgebras (D.laurentSpectrumToBase ≫ D.f))
        (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)) b) =
      exteriorPower.ιMulti c.B 1 fun _ => CommRingCat.KaehlerDifferential.d b :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_exactOne
    (D.laurentSpectrumToBase ≫ D.f) c.isAffineOpen_preimage c.V.2 c.preimage_le b

/-- **Over a base chart the identification of the forms of `L^⋆` carries the constant form `1` to
the empty wedge.** -/
theorem formsL_one :
    (c.formsL 0).hom ((Scheme.Hom.deRhamAlgebras (D.laurentSpectrumToBase ≫ D.f)).exterior.one.eval
        (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1))) =
      exteriorPower.ιMulti c.B 0 Fin.elim0 :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_one
    (D.laurentSpectrumToBase ≫ D.f) c.isAffineOpen_preimage c.V.2 c.preimage_le

/-! ### The grading over a base chart -/

/-- **The grading of `Γ(L^⋆, π⁻¹U)` over a base chart**, transported from the weight grading of
`Γ(X, U)[T;T⁻¹]` along the affine local model. -/
abbrev grading (n : ℤ) :
    Submodule c.R c.B :=
  LaurentDeRham.transportGrading (R := c.R) c.equiv n

/-- **A homogeneous function of degree `n` has degree `n` for the transported grading.** -/
theorem laurentFunction_mem_grading (n : ℤ) (x : (D.laurentAlgebra.piece n).val.obj (op c.U.1)) :
    D.laurentFunction n c.U x ∈ c.grading n := by
  obtain ⟨q, hq, hqx⟩ := c.chart.exists_mem_grade_hom_eq c.U.2 n x
  refine ⟨q, hq, ?_⟩
  show c.chart.sectionsRingEquiv q = D.laurentFunction n c.U x
  rw [Situation.LaurentChart.sectionsRingEquiv_apply, hqx]
  rfl

/-- **Every element of degree `n` for the transported grading is a homogeneous function of
degree `n`.** -/
theorem exists_laurentFunction_of_mem_grading {n : ℤ} {b : c.B} (hb : b ∈ c.grading n) :
    ∃ x : (D.laurentAlgebra.piece n).val.obj (op c.U.1), D.laurentFunction n c.U x = b := by
  obtain ⟨q, hq, rfl⟩ := hb
  obtain ⟨x, hx⟩ := c.chart.exists_hom_eq_of_mem_grade hq
  refine ⟨x, ?_⟩
  show D.laurentFunction n c.U x = c.chart.sectionsRingEquiv q
  rw [Situation.LaurentChart.sectionsRingEquiv_apply, hx]
  rfl

/-- The exterior powers of the two spellings of the Kähler differentials of
`Γ(S, V) → Γ(L^⋆, π⁻¹U)` are the same module; this is the identity between them. -/
def toΩB (p : ℕ) : ⋀[c.B]^p c.ΩB ≃ₗ[c.B] ⋀[c.B]^p Ω[c.B⁄c.R] :=
  LinearEquiv.refl c.B _

/-- The exterior powers of the two spellings of the Kähler differentials of `Γ(S, V) → Γ(X, U)`
are the same module; this is the identity between them. -/
def toΩA (p : ℕ) : ⋀[c.A]^p c.ΩA ≃ₗ[c.A] ⋀[c.A]^p Ω[c.A⁄c.R] :=
  LinearEquiv.refl c.A _

/-- `Stacks.LineBundle.Situation.BaseChart.toΩB` carries a wedge of differentials to the same
wedge. -/
theorem toΩB_ιMulti (p : ℕ) (b : Fin p → c.B) :
    c.toΩB p (exteriorPower.ιMulti c.B p fun i => CommRingCat.KaehlerDifferential.d (b i)) =
      exteriorPower.ιMulti c.B p fun i => KaehlerDifferential.D c.R c.B (b i) :=
  rfl

/-- `Stacks.LineBundle.Situation.BaseChart.toΩB` commutes with the wedge product. -/
theorem toΩB_wedgeMul (p q : ℕ) (x : ⋀[c.B]^p c.ΩB) (y : ⋀[c.B]^q c.ΩB) :
    c.toΩB (p + q) (exteriorPower.wedgeMul p q x y) =
      exteriorPower.wedgeMul p q (c.toΩB p x) (c.toΩB q y) :=
  rfl

/-- **The relative forms of `L^⋆` over `π⁻¹U`, read as Kähler forms**
`⋀^p Ω[Γ(L^⋆, π⁻¹U)⁄Γ(S, V)]`, on the sections over `U` of the pushed-forward forms. -/
def formsLF (p : ℕ) : Γ(D.gradedAmbient p, c.U.1) →+ ⋀[c.B]^p Ω[c.B⁄c.R] :=
  AddMonoidHom.mk' (fun ω => c.toΩB p ((c.formsL p).hom (D.secG p c.U.1 ω))) fun ω χ => by
    rw [map_add, map_add, map_add]

/-- The value of `Stacks.LineBundle.Situation.BaseChart.formsLF` on a form. -/
theorem formsLF_apply (p : ℕ) (ω : Γ(D.gradedAmbient p, c.U.1)) :
    c.formsLF p ω = c.toΩB p ((c.formsL p).hom (D.secG p c.U.1 ω)) :=
  rfl

/-- The inverse of `Stacks.LineBundle.Situation.BaseChart.formsLF`. -/
def formsLFInv (p : ℕ) (x : ⋀[c.B]^p Ω[c.B⁄c.R]) :
    Γ(D.gradedAmbient p, c.U.1) :=
  (D.secG p c.U.1).symm ((c.formsL p).inv ((c.toΩB p).symm x))

/-- `Stacks.LineBundle.Situation.BaseChart.formsLFInv` is a right inverse of `formsLF`. -/
@[simp]
theorem formsLF_formsLFInv (p : ℕ) (x : ⋀[c.B]^p Ω[c.B⁄c.R]) :
    c.formsLF p (c.formsLFInv p x) = x := by
  rw [formsLF_apply, formsLFInv, AddEquiv.apply_symm_apply, Iso.inv_hom_id_apply,
    LinearEquiv.apply_symm_apply]

/-- `Stacks.LineBundle.Situation.BaseChart.formsLFInv` is a left inverse of `formsLF`. -/
@[simp]
theorem formsLFInv_formsLF (p : ℕ) (ω : Γ(D.gradedAmbient p, c.U.1)) :
    c.formsLFInv p (c.formsLF p ω) = ω := by
  rw [formsLF_apply, formsLFInv, LinearEquiv.symm_apply_apply, Iso.hom_inv_id_apply,
    AddEquiv.symm_apply_apply]

/-- `Stacks.LineBundle.Situation.BaseChart.formsLF` is injective. -/
theorem formsLF_injective (p : ℕ) : Function.Injective (c.formsLF p) :=
  Function.LeftInverse.injective (c.formsLFInv_formsLF p)

/-- **The identification carries the product by a one-form to the wedge product.** -/
theorem formsLF_gradedWedge (p : ℕ) (η : Γ(D.gradedAmbient p, c.U.1))
    (ξ : Γ(D.gradedAmbient 1, c.U.1)) :
    c.formsLF (p + 1) (D.gradedWedge p c.U.1 η ξ) =
      exteriorPower.wedgeMul p 1 (c.formsLF p η) (c.formsLF 1 ξ) := by
  rw [formsLF_apply, D.secG_gradedWedge]
  exact c.formsL_mul_one p (D.secG p c.U.1 η) (D.secG 1 c.U.1 ξ)

/-- **The identification carries the differential of a function to its Kähler
differential.** -/
theorem formsLF_gradedD
    (b : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1))) :
    c.formsLF 1 (D.gradedD c.U.1 b) =
      exteriorPower.ιMulti c.B 1 fun _ => KaehlerDifferential.D c.R c.B (D.secR _ b) := by
  rw [formsLF_apply, D.secG_gradedD]
  exact congrArg (c.toΩB 1) (c.formsL_exactOne (D.secR _ b))

/-- **The identification carries the constant form `1` to the empty wedge.** -/
theorem formsLF_gradedOne :
    c.formsLF 0 (D.gradedOne c.U.1) = exteriorPower.ιMulti c.B 0 Fin.elim0 := by
  rw [formsLF_apply, D.secG_gradedOne]
  exact c.formsL_one

/-- **The identification is linear over the functions on `π⁻¹U`.** -/
theorem formsLF_gradedSmul (p : ℕ)
    (b : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)))
    (ω : Γ(D.gradedAmbient p, c.U.1)) :
    c.formsLF p (D.gradedSmul p c.U.1 b ω) =
      D.secR (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1) b • c.formsLF p ω := by
  rw [formsLF_apply, formsLF_apply, D.secG_gradedSmul]
  exact Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_smul
    (D.laurentSpectrumToBase ≫ D.f) c.isAffineOpen_preimage c.V.2 c.preimage_le p
    (D.secR _ b) (D.secG p c.U.1 ω)

/-- **The identification is linear over the functions on `U`**, acting on `π⁻¹U` through `π`. -/
theorem formsLF_smul (p : ℕ) (r : c.A) (ω : Γ(D.gradedAmbient p, c.U.1)) :
    c.formsLF p (r • ω) = (D.laurentSpectrumToBase.app c.U.1).hom r • c.formsLF p ω := by
  rw [D.smul_eq_gradedSmul, c.formsLF_gradedSmul, RingEquiv.apply_symm_apply]

/-! ### Homogeneous forms and graded components -/

/-- **The identification carries a homogeneous form of degree `n` into the degree-`n` component
of Stacks 0FU9.** -/
theorem formsLF_mem_of_isHomogeneous {p : ℕ} {n : ℤ} {ω : Γ(D.gradedAmbient p, c.U.1)}
    (h : D.IsHomogeneousLaurentForm c.U p n ω) :
    c.formsLF p ω ∈ gradedDifferentialFormComponent c.grading p n := by
  induction p generalizing n with
  | zero =>
      obtain ⟨x, hx⟩ := h
      have hx' : ω = D.gradedSmul 0 c.U.1 (D.laurentFunction n c.U x) (D.gradedOne c.U.1) := hx
      rw [hx', c.formsLF_gradedSmul, c.formsLF_gradedOne]
      have h2 : (exteriorPower.ιMulti c.B 0 Fin.elim0 : ⋀[c.B]^0 Ω[c.B⁄c.R]) =
          exteriorPower.ιMulti c.B 0 (fun i : Fin 0 => KaehlerDifferential.D c.R c.B
            ((fun _ : Fin 1 => D.secR _ (D.laurentFunction n c.U x)) i.succ)) :=
        congrArg _ (funext fun i => i.elim0)
      rw [h2]
      exact smul_ιMulti_D_mem_gradedDifferentialFormComponent c.grading (fun _ => n)
        (fun _ => D.secR _ (D.laurentFunction n c.U x))
        (fun _ => c.laurentFunction_mem_grading n x) (by simp)
  | succ p ih =>
      obtain ⟨i, j, hij, η, x, hη, hω⟩ := h
      have hω' : ω = D.gradedWedge p c.U.1 (D.secF p c.U.1 η)
          (D.gradedD c.U.1 (D.laurentFunction j c.U x)) := hω
      have hη' : D.IsHomogeneousLaurentForm c.U p i (D.secF p c.U.1 η) := hη
      rw [hω', c.formsLF_gradedWedge, c.formsLF_gradedD, ← hij]
      exact wedgeMul_ιMulti_D_mem_gradedDifferentialFormComponent (ih hη')
        (c.laurentFunction_mem_grading j x)

/-- **Every generator of the degree-`n` component is the image of a homogeneous form of degree
`n`.** -/
theorem exists_isHomogeneous_formsLF_eq (p : ℕ) (degree : Fin (p + 1) → ℤ)
    (a : Fin (p + 1) → c.B) (ha : ∀ i, a i ∈ c.grading (degree i)) :
    ∃ ω : Γ(D.gradedAmbient p, c.U.1), D.IsHomogeneousLaurentForm c.U p (∑ i, degree i) ω ∧
      c.formsLF p ω = a 0 • exteriorPower.ιMulti c.B p fun i => KaehlerDifferential.D c.R c.B
        (a i.succ) := by
  induction p with
  | zero =>
      obtain ⟨x, hx⟩ := c.exists_laurentFunction_of_mem_grading (ha 0)
      refine ⟨D.gradedSmul 0 c.U.1 (D.laurentFunction (degree 0) c.U x) (D.gradedOne c.U.1),
        ?_, ?_⟩
      · rw [Fin.sum_univ_one]
        exact D.isHomogeneousLaurentForm_gradedSmul_one (degree 0) c.U x
      · rw [c.formsLF_gradedSmul, c.formsLF_gradedOne]
        refine congrArg₂ (· • ·) hx (congrArg _ (funext fun i => i.elim0))
  | succ p ih =>
      obtain ⟨η, hη, hηeq⟩ := ih (fun i => degree i.castSucc) (fun i => a i.castSucc)
        (fun i => ha i.castSucc)
      obtain ⟨x, hx⟩ := c.exists_laurentFunction_of_mem_grading (ha (Fin.last (p + 1)))
      refine ⟨D.gradedWedge p c.U.1 η
          (D.gradedD c.U.1 (D.laurentFunction (degree (Fin.last (p + 1))) c.U x)), ?_, ?_⟩
      · rw [Fin.sum_univ_castSucc]
        exact D.isHomogeneousLaurentForm_gradedWedge p (∑ i : Fin (p + 1), degree i.castSucc)
          (degree (Fin.last (p + 1)))
          ((∑ i : Fin (p + 1), degree i.castSucc) + degree (Fin.last (p + 1))) rfl c.U hη x
      · rw [c.formsLF_gradedWedge, c.formsLF_gradedD]
        refine (congrArg (fun z => exteriorPower.wedgeMul p 1 z (exteriorPower.ιMulti c.B 1
          fun _ => KaehlerDifferential.D c.R c.B
            (D.secR _ (D.laurentFunction (degree (Fin.last (p + 1))) c.U x)))) hηeq).trans ?_
        refine (KaehlerDifferential.wedgeMul_smul_ιMulti_D p (a 0) (fun i => a i.succ.castSucc)
          _).trans ?_
        refine congrArg (a 0 • ·) (congrArg (exteriorPower.ιMulti c.B (p + 1)) (funext fun k => ?_))
        refine congrArg (KaehlerDifferential.D c.R c.B) ?_
        refine Fin.lastCases ?_ (fun l => ?_) k
        · rw [Fin.snoc_last, Fin.succ_last]
          exact hx
        · rw [Fin.snoc_castSucc, ← Fin.castSucc_fin_succ]

/-- **The identification carries the sections of `Ω^p_{L^⋆/S, n}` over `U` into the degree-`n`
component.** -/
theorem formsLF_mem_of_mem {p : ℕ} {n : ℤ} {ω : Γ(D.gradedAmbient p, c.U.1)}
    (hω : ω ∈ (D.gradedLaurentForms p n).obj (op c.U.1)) :
    c.formsLF p ω ∈ gradedDifferentialFormComponent c.grading p n := by
  rw [← D.homogeneousSheafSubmodule_eq] at hω
  have hω' : ω ∈ Submodule.span Γ(D.X, c.U.1) (D.homogeneousSet p n c.U) := by
    rw [← D.homogeneousSheafSubmodule_obj p n c.U]
    exact hω
  clear hω
  induction hω' using Submodule.span_induction with
  | mem y hy => exact c.formsLF_mem_of_isHomogeneous hy
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
      rw [c.formsLF_smul]
      exact KaehlerDifferential.smul_mem_gradedDifferentialFormComponent
        (fun hb hb' => LaurentDeRham.mul_mem_transportGrading c.equiv hb hb')
        (LaurentDeRham.algebraMap_mem_transportGrading c.equiv r) hy

/-- **Every element of the degree-`n` component comes from a section of `Ω^p_{L^⋆/S, n}`
over `U`.** -/
theorem formsLFInv_mem_of_mem {p : ℕ} {n : ℤ}
    {x : ⋀[c.B]^p Ω[c.B⁄c.R]}
    (hx : x ∈ gradedDifferentialFormComponent c.grading p n) :
    c.formsLFInv p x ∈ (D.gradedLaurentForms p n).obj (op c.U.1) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨degree, a, hg, rfl⟩ := hy
      obtain ⟨ω, hω, hωeq⟩ := c.exists_isHomogeneous_formsLF_eq p degree (fun i => a i)
        (fun i => (a i).2)
      rw [← hωeq, formsLFInv_formsLF, hg]
      exact D.mem_gradedLaurentForms c.U hω
  | zero =>
      have h0 : c.formsLFInv p 0 = 0 := by
        rw [← map_zero (c.formsLF p), formsLFInv_formsLF]
      rw [h0]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      have h0 : c.formsLFInv p (y + z) = c.formsLFInv p y + c.formsLFInv p z := by
        refine c.formsLF_injective p ?_
        rw [map_add, formsLF_formsLFInv, formsLF_formsLFInv, formsLF_formsLFInv]
      rw [h0]
      exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
      have h0 : c.formsLFInv p (r • y) = (algebraMap c.R c.A r) • c.formsLFInv p y := by
        refine c.formsLF_injective p ?_
        rw [c.formsLF_smul, formsLF_formsLFInv, formsLF_formsLFInv, ← algebraMap_smul c.B r y,
          IsScalarTower.algebraMap_apply c.R c.A c.B r]
        rfl
      rw [h0]
      exact Submodule.smul_mem _ _ hy

/-! ### The pullback and the logarithmic differential over a base chart -/

/-- The relative forms of `X` over `U` as Kähler forms, in the spelling of the algebra
`Γ(S, V) → Γ(X, U)`. -/
def formsXF (p : ℕ) (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    ⋀[c.A]^p Ω[c.A⁄c.R] :=
  c.toΩA p ((c.formsX p).hom α)

/-- The value of `Stacks.LineBundle.Situation.BaseChart.formsXF` on a form. -/
theorem formsXF_apply (p : ℕ) (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.formsXF p α = c.toΩA p ((c.formsX p).hom α) :=
  rfl

/-- The inverse of `Stacks.LineBundle.Situation.BaseChart.formsXF`. -/
def formsXFInv (p : ℕ) (x : ⋀[c.A]^p Ω[c.A⁄c.R]) :
    Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1) :=
  (c.formsX p).inv ((c.toΩA p).symm x)

/-- `Stacks.LineBundle.Situation.BaseChart.formsXFInv` is a right inverse of `formsXF`. -/
@[simp]
theorem formsXF_formsXFInv (p : ℕ) (x : ⋀[c.A]^p Ω[c.A⁄c.R]) :
    c.formsXF p (c.formsXFInv p x) = x := by
  rw [formsXF, formsXFInv, Iso.inv_hom_id_apply, LinearEquiv.apply_symm_apply]

/-- `Stacks.LineBundle.Situation.BaseChart.formsXFInv` is a left inverse of `formsXF`. -/
@[simp]
theorem formsXFInv_formsXF (p : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.formsXFInv p (c.formsXF p α) = α := by
  rw [formsXF, formsXFInv, LinearEquiv.symm_apply_apply, Iso.hom_inv_id_apply]

/-- `Stacks.LineBundle.Situation.BaseChart.formsXF` is injective. -/
theorem formsXF_injective (p : ℕ) : Function.Injective (c.formsXF p) :=
  Function.LeftInverse.injective (c.formsXFInv_formsXF p)

/-- **The pullback of forms along `π`, read through the identifications, is the pullback of
Kähler forms along `Γ(X, U) → Γ(L^⋆, π⁻¹U)`.** -/
theorem formsLF_pullbackG (p : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.formsLF p (D.pullbackG p c.U.1 α) = mapExteriorPower c.R c.A c.B p (c.formsXF p α) := by
  have h := c.formsL_pullbackForms p ((c.toΩA p).symm (c.formsXF p α))
  have e : (c.formsX p).inv ((c.toΩA p).symm (c.formsXF p α)) = α := c.formsXFInv_formsXF p α
  rw [e] at h
  rw [formsLF_apply, Situation.pullbackG, AddEquiv.apply_symm_apply]
  exact congrArg (c.toΩB p) h

/-! ### The differential over a base chart -/

/-- **The identification of the forms of `L^⋆` commutes with the de Rham differential.** -/
theorem formsLF_gradedDiff (p : ℕ) (ω : Γ(D.gradedAmbient p, c.U.1)) :
    c.formsLF (p + 1) (D.gradedDiff p c.U.1 ω) =
      deRhamDifferential (A := c.R) p (c.formsLF p ω) := by
  rw [formsLF_apply, formsLF_apply, D.secG_gradedDiff]
  have h := Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_deRhamComplex_d
    (D.laurentSpectrumToBase ≫ D.f) c.isAffineOpen_preimage c.V.2 c.preimage_le p
    (D.secG p c.U.1 ω)
  have h2 := Stacks.AlgebraicGeometry.AffineOpenDeRham.ringDeRhamComplex_d_apply
    (D.laurentSpectrumToBase ≫ D.f) c.isAffineOpen_preimage c.V.2 c.preimage_le p
    ((c.formsL p).hom (D.secG p c.U.1 ω))
  exact (congrArg (c.toΩB (p + 1)) h).trans h2

/-- **The identification of the forms of `X` commutes with the de Rham differential.** -/
theorem formsXF_dX (p : ℕ) (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.formsXF (p + 1) (D.dX p c.U.1 α) = deRhamDifferential (A := c.R) p (c.formsXF p α) := by
  rw [formsXF_apply, formsXF_apply, D.dX_eq]
  have h := Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_deRhamComplex_d
    D.f c.U.2 c.V.2 c.le p α
  have h2 := Stacks.AlgebraicGeometry.AffineOpenDeRham.ringDeRhamComplex_d_apply
    D.f c.U.2 c.V.2 c.le p ((c.formsX p).hom α)
  rw [h, h2]
  rfl

/-! ### The coordinate and the logarithmic differential over a base chart -/

/-- **The coordinate of a base chart**, the unit `s` of the functions on `π⁻¹U` attached to the
generator of the Laurent chart; it is the image of `T` under the affine local model. -/
def unit : (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)))ˣ :=
  Units.map (D.secR (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)).symm.toMonoidHom
    (LaurentDeRham.transportUnit c.equiv)

/-- Read in `Γ(L^⋆, π⁻¹U)`, the coordinate of a base chart is the transported unit `T`. -/
theorem secR_unit :
    Units.map (D.secR (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)).toMonoidHom c.unit =
      LaurentDeRham.transportUnit c.equiv := by
  ext
  exact (D.secR _).apply_symm_apply _

/-- **The coordinate of a base chart is the homogeneous function of degree one of the generator
of its Laurent chart.** -/
theorem unit_val :
    D.secR _ (c.unit : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1))) =
      D.laurentFunction 1 c.U c.chart.gen := by
  show c.equiv (LaurentDeRham.weightOneUnit (1 : c.Aˣ) : LaurentPolynomial c.A) = _
  rw [LaurentDeRham.weightOneUnit_val, Units.val_one, map_one, one_mul, equiv_apply,
    Situation.LaurentChart.sectionsRingEquiv_apply, Situation.LaurentChart.hom_T, zpow_one]
  rfl

/-- **The identification carries `d log w` to `dlog w`.** -/
theorem formsLF_laurentDlog
    (w : (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)))ˣ) :
    c.formsLF 1 (D.laurentDlog c.U.1 w) = exteriorPower.ιMulti c.B 1 fun _ =>
      Stacks.LogPoles.dlogUnit c.R
        (Units.map (D.secR (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)).toMonoidHom w) := by
  rw [D.laurentDlog_eq, c.formsLF_gradedSmul, c.formsLF_gradedD,
    KaehlerDifferential.smul_ιMulti_one]
  rfl

/-! ### The model of forms of a base chart -/

/-- The pullback of forms along `π` over a base chart is additive. -/
theorem pullbackG_add (p : ℕ)
    (α β : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    D.pullbackG p c.U.1 (α + β) = D.pullbackG p c.U.1 α + D.pullbackG p c.U.1 β := by
  rw [Situation.pullbackG, Situation.pullbackG, Situation.pullbackG, D.pullbackForms_add, map_add]

/-- `Stacks.LineBundle.Situation.BaseChart.formsXF` is additive. -/
theorem formsXF_add (p : ℕ) (α β : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.formsXF p (α + β) = c.formsXF p α + c.formsXF p β := by
  rw [formsXF_apply, formsXF_apply, formsXF_apply, map_add, map_add]

/-- `Stacks.LineBundle.Situation.BaseChart.formsXF` is linear over `Γ(X, U)`. -/
theorem formsXF_smul (p : ℕ) (a : c.A)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.formsXF p (a • α) = a • c.formsXF p α := by
  rw [formsXF_apply, formsXF_apply, map_smul, map_smul]

/-- The identification of the forms of `L^⋆` over `π⁻¹U`, as an additive equivalence. -/
def ψE (p : ℕ) : Γ(D.gradedAmbient p, c.U.1) ≃+ ⋀[c.B]^p Ω[c.B⁄c.R] where
  toFun := c.formsLF p
  invFun := c.formsLFInv p
  left_inv := c.formsLFInv_formsLF p
  right_inv := c.formsLF_formsLFInv p
  map_add' x y := by rw [map_add]

/-- `Stacks.LineBundle.Situation.BaseChart.ψE` is `formsLF`. -/
theorem ψE_apply (p : ℕ) (x : Γ(D.gradedAmbient p, c.U.1)) : c.ψE p x = c.formsLF p x := rfl

/-- The identification of the forms of `X` over `U`, as an additive equivalence. -/
def χE (p : ℕ) :
    Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1) ≃+ ⋀[c.A]^p Ω[c.A⁄c.R] where
  toFun := c.formsXF p
  invFun := c.formsXFInv p
  left_inv := c.formsXFInv_formsXF p
  right_inv := c.formsXF_formsXFInv p
  map_add' := c.formsXF_add p

/-- `Stacks.LineBundle.Situation.BaseChart.χE` is `formsXF`. -/
theorem χE_apply (p : ℕ) (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.χE p α = c.formsXF p α := rfl

/-- The pullback of forms along `π` over a base chart, as an additive map. -/
def pullE (p : ℕ) :
    Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1) →+ Γ(D.gradedAmbient p, c.U.1) :=
  AddMonoidHom.mk' (D.pullbackG p c.U.1) (c.pullbackG_add p)

/-- `Stacks.LineBundle.Situation.BaseChart.pullE` is `Stacks.LineBundle.Situation.pullbackG`. -/
theorem pullE_apply (p : ℕ) (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.pullE p α = D.pullbackG p c.U.1 α := rfl

/-- `Stacks.LineBundle.Situation.BaseChart.ψE` is semilinear over `Γ(X, U) → Γ(L^⋆, π⁻¹U)`. -/
theorem ψE_smul (p : ℕ) (a : c.A) (x : Γ(D.gradedAmbient p, c.U.1)) :
    c.ψE p (a • x) = algebraMap c.A c.B a • c.ψE p x := by
  rw [ψE_apply, ψE_apply, c.formsLF_smul]
  rfl

/-- `Stacks.LineBundle.Situation.BaseChart.χE` is linear over `Γ(X, U)`. -/
theorem χE_smul (p : ℕ) (a : c.A) (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.χE p (a • α) = a • c.χE p α := by
  rw [χE_apply, χE_apply, c.formsXF_smul]

/-- Through `ψE` and `χE`, the pullback of forms along `π` is the pullback of Kähler forms along
`Γ(X, U) → Γ(L^⋆, π⁻¹U)`. -/
theorem ψE_pullE (p : ℕ) (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.ψE p (c.pullE p α) = mapExteriorPower c.R c.A c.B p (c.χE p α) := by
  rw [ψE_apply, pullE_apply, χE_apply, c.formsLF_pullbackG]

/-- `Stacks.LineBundle.Situation.BaseChart.ψE` carries the product by a one-form to the wedge
product. -/
theorem ψE_gradedWedge (p : ℕ) (x : Γ(D.gradedAmbient p, c.U.1)) (y : Γ(D.gradedAmbient 1, c.U.1)) :
    c.ψE (p + 1) (D.gradedWedge p c.U.1 x y) =
      exteriorPower.wedgeMul p 1 (c.ψE p x) (c.ψE 1 y) :=
  c.formsLF_gradedWedge p x y

/-- `Stacks.LineBundle.Situation.BaseChart.ψE` commutes with the de Rham differential. -/
theorem ψE_gradedDiff (p : ℕ) (x : Γ(D.gradedAmbient p, c.U.1)) :
    c.ψE (p + 1) (D.gradedDiff p c.U.1 x) = deRhamDifferential (A := c.R) p (c.ψE p x) := by
  rw [ψE_apply, ψE_apply, c.formsLF_gradedDiff]

/-- `Stacks.LineBundle.Situation.BaseChart.χE` commutes with the de Rham differential. -/
theorem χE_dX (p : ℕ) (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.χE (p + 1) (D.dX p c.U.1 α) = deRhamDifferential (A := c.R) p (c.χE p α) := by
  rw [χE_apply, χE_apply, c.formsXF_dX]

/-- A section over `U` of the pushed-forward forms lies in the weight-zero part
`Ω^p_{L^⋆/S,0}` if and only if its image under `ψE` lies in the degree-zero component. -/
theorem mem_iff_ψE (p : ℕ) (x : Γ(D.gradedAmbient p, c.U.1)) :
    x ∈ ((D.gradedLaurentForms p 0).obj (op c.U.1)).toAddSubgroup ↔
      c.ψE p x ∈ gradedDifferentialFormComponent c.grading p 0 := by
  rw [ψE_apply]
  exact ⟨fun h => c.formsLF_mem_of_mem h, fun h => by
    rw [← c.formsLFInv_formsLF p x]
    exact c.formsLFInv_mem_of_mem h⟩

/-- **The model of the forms of a base chart**: the sections over `U` of the pushed-forward forms
of `L^⋆` and of the forms of `X`, identified with Kähler forms. -/
abbrev model : LaurentDeRham.FormsModel.{u, u} c.R c.A c.B where
  equiv := c.equiv
  F p := Γ(D.gradedAmbient p, c.U.1)
  G p := Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)
  ψ := c.ψE
  ψ_smul := c.ψE_smul
  χ := c.χE
  χ_smul := c.χE_smul
  pull := c.pullE
  ψ_pull := c.ψE_pullE
  wedge p x y := D.gradedWedge p c.U.1 x y
  ψ_wedge := c.ψE_gradedWedge
  N p := ((D.gradedLaurentForms p 0).obj (op c.U.1)).toAddSubgroup
  mem_N := c.mem_iff_ψE
  dF p x := D.gradedDiff p c.U.1 x
  ψ_dF := c.ψE_gradedDiff
  dG p x := D.dX p c.U.1 x
  χ_dG := c.χE_dX

/-- **`d log w` is the logarithmic differential of `w` in the model of a base chart.** -/
theorem isDlog_laurentDlog
    (w : (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)))ˣ) :
    c.model.IsDlog (D.laurentDlog c.U.1 w)
      (Units.map (D.secR (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)).toMonoidHom w) :=
  c.formsLF_laurentDlog w

/-- **The coordinate of a base chart has degree one.** -/
theorem unit_mem :
    ((Units.map (D.secR (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)).toMonoidHom c.unit : c.Bˣ) : c.B) ∈
      LaurentDeRham.transportGrading (R := c.R) c.model.equiv 1 := by
  rw [c.secR_unit]
  exact LaurentDeRham.transportUnit_mem c.equiv

end Situation.BaseChart

end Stacks.LineBundle

end
