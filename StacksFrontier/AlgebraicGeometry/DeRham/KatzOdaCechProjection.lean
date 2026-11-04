module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechFiltration
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsGeneratorCalculus
public import StacksFrontier.RingTheory.Kaehler.KatzOdaCechMul

/-!
# The projection of forms relative to `S` onto forms relative to `Y`, on the Čech intersections

For `f : X ⟶ Y` and `g : Y ⟶ S` with `Y`, `S` affine, the canonical map `Ω^•_{X/S} ⟶ Ω^•_{X/Y}`
of [Stacks, Tag 07HX] (for the square with top edge `𝟙 X`) is, on the sections over an affine
open `V` of `X`, the ring-level projection `⋀Ω_{Γ(V)/Γ(S)} ⟶ ⋀Ω_{Γ(V)/Γ(Y)}`. On the Čech
intersections of an affine covering this identifies the intersection-wise projection
`Stacks.KatzOda.Cech.projHom` of the scheme instantiation with the canonical map.

## Main results

* `AlgebraicGeometry.DeRhamKatzOdaCech.formsEquiv_relSections`: the canonical map on an affine
  open is the ring-level projection.
* `Stacks.KatzOda.Cech.FormsProjData.projAt_eq`: the intersection-wise projection is any map of
  sections that the identifications with Kähler forms carry to the ring-level projection.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.CategoryTheory.CechComplex

universe u

namespace Stacks.KatzOda

variable {R A B : CommRingCat.{u}} (gR : R ⟶ A) (φ : A ⟶ B) (ψ : R ⟶ B) (h : gR ≫ φ = ψ)

/-- The projection of forms on a multiple of a wedge of universal differentials. -/
theorem formsProj_smul_ιMulti_d (n : ℕ) (c : B) (a : Fin n → B) :
    formsProj gR φ ψ h n (c • exteriorPower.ιMulti B n fun i ↦
        CommRingCat.KaehlerDifferential.d (f := ψ) (a i)) =
      c • exteriorPower.ιMulti B n fun i ↦ CommRingCat.KaehlerDifferential.d (f := φ) (a i) := by
  let := gR.hom.toAlgebra
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  have := isScalarTower gR φ ψ h
  change exteriorPower.map n (KaehlerDifferential.map R A B B)
      (c • exteriorPower.ιMulti B n fun i ↦ KaehlerDifferential.D R B (a i)) =
    c • exteriorPower.ιMulti B n fun i ↦ KaehlerDifferential.D A B (a i)
  rw [map_smul, exteriorPower.map_apply_ιMulti]
  congr 2
  funext i
  exact KaehlerDifferential.map_D R A B B (a i)

end Stacks.KatzOda

namespace Stacks.KatzOda.Cech

open CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasFiniteProducts C] {ι : Type u} [Fintype ι]
  [DecidableEq ι] {U : ι → C} {R A : CommRingCat.{u}} {gR : R ⟶ A} (D : ChartData (ι := ι) gR)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ) (Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} A) ℕ)

/-- **Forms relative to `R` and to `A` with a projection between them**: forms data for `P` and
for `Q`, together with maps of sections over the intersections that the identifications with
Kähler forms carry to the projection `⋀Ω[B_t⁄R] ⟶ ⋀Ω[B_t⁄A]`. -/
structure FormsProjData where
  /-- The forms relative to `R`. -/
  EP : FormsData U D D.ψ D.ψ_ρ P
  /-- The forms relative to `A`. -/
  EQ : FormsData U D D.φ D.φ_ρ Q
  /-- The map of sections over the intersection selected by `t`, in degree `a`. -/
  pr : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι),
    (P.X a).obj (op (inter U t)) → (Q.X a).obj (op (inter U t))
  /-- The identifications with Kähler forms carry it to the projection of forms. -/
  e'_pr : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) (y : (P.X a).obj (op (inter U t))),
    letI := EQ.instAddCommGroup a t
    letI := EQ.instModule a t
    EQ.e' a t (EQ.s a t (pr a t y)) =
      formsProj gR (D.φ t) (D.ψ t) (D.comp_φ t) a (EP.e' a t (EP.s a t y))

variable {D P Q}

omit [Fintype ι] [DecidableEq ι] in
/-- **The intersection-wise projection is the given map of sections.** -/
theorem FormsProjData.projAt_eq (PD : FormsProjData D P Q) (a : ℕ) {m : ℕ}
    (t : Fin (m + 1) → ι) (y : (P.X a).obj (op (inter U t))) :
    projAt D PD.EP PD.EQ a t y = PD.pr a t y :=
  ((PD.EQ.e a t).symm_apply_eq).2 (PD.e'_pr a t y).symm

end Stacks.KatzOda.Cech

namespace AlgebraicGeometry.DeRhamKatzOdaCech

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The canonical map `Ω^a_{X/S} ⟶ Ω^a_{X/Y}` on sections over an open.** -/
abbrev relSections (a : ℕ) (V : X.Opens)
    (y : Γ(Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ), V)) :
    Γ(Scheme.Hom.relativeDifferentialForms f (a : ℤ), V) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardSections (𝟙 X) (f ≫ g) f g
    (Category.id_comp _) a y

/-- The map `relSections f g a V` sends `0` to `0`. -/
theorem relSections_zero (a : ℕ) (V : X.Opens) : relSections f g a V 0 = 0 :=
  map_zero (((Scheme.Hom.deRhamFormsPushforwardHom (𝟙 X) (f ≫ g) f g (Category.id_comp _)).app
    (a : ℤ)).val.app (op V)).hom

/-- The map `relSections f g a V` is additive. -/
theorem relSections_add (a : ℕ) (V : X.Opens)
    (y y' : Γ(Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ), V)) :
    relSections f g a V (y + y') = relSections f g a V y + relSections f g a V y' :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardSections_add (𝟙 X) (f ≫ g) f g
    (Category.id_comp _) a y y'

/-- `formsEquiv q hV a` is given by the isomorphism
`Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso` of sections of `Ω^a_{X/T}` over
the affine open `V` with Kähler forms. -/
theorem formsEquiv_apply {T : Scheme.{u}} [IsAffine T] (q : X ⟶ T) {V : X.Opens}
    (hV : IsAffineOpen V) (a : ℕ) (l : Γ(Scheme.Hom.relativeDifferentialForms q (a : ℤ), V)) :
    formsEquiv q hV a l = (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso q hV
      (isAffineOpen_top T) (le_preimage_top q V) a).hom l :=
  rfl

variable [IsAffine Y] [IsAffine S]

/-- **The canonical map `Ω^a_{X/S} ⟶ Ω^a_{X/Y}` on an affine open is the projection of Kähler
forms** `⋀^a Ω_{Γ(V)/Γ(S)} ⟶ ⋀^a Ω_{Γ(V)/Γ(Y)}`. -/
theorem formsEquiv_relSections {V : X.Opens} (hV : IsAffineOpen V) (a : ℕ)
    (y : Γ(Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ), V)) :
    formsEquiv f hV a (relSections f g a V y) =
      Stacks.KatzOda.formsProj (baseMap g) (chartMap f V) (totalChartMap f g V)
        (baseMap_comp_chartMap f g V) a (formsEquiv (f ≫ g) hV a y) := by
  induction y using Stacks.DeRham.FormsGenerators.induction_on_affine (f ≫ g) hV
    (isAffineOpen_top S) (le_preimage_top (f ≫ g) V) with
  | h0 =>
    rw [relSections_zero, (formsEquiv f hV a).map_zero, (formsEquiv (f ≫ g) hV a).map_zero,
      Stacks.KatzOda.formsProj_zero]
  | hadd x y hx hy =>
    rw [relSections_add, (formsEquiv f hV a).map_add, hx, hy,
      (formsEquiv (f ≫ g) hV a).map_add, Stacks.KatzOda.formsProj_add]
  | hgen c b =>
    have hgen : relSections f g a V (c • Stacks.DeRham.FormsGenerators.gen (f ≫ g) V b) =
        c • Stacks.DeRham.FormsGenerators.gen f V b :=
      (Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardSections_smul (𝟙 X)
        (f ≫ g) f g (Category.id_comp _) a c _).trans
        (congrArg (fun z : Γ(Scheme.Hom.relativeDifferentialForms f (a : ℤ), V) => c • z)
          (Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft (𝟙 X) (f ≫ g)
          f g (Category.id_comp _) (op V) a b))
    have h3 := Stacks.DeRham.FormsGenerators.formsSectionsIso_hom_smul_gen (f ≫ g) hV
      (isAffineOpen_top S) (le_preimage_top (f ≫ g) V) c b
    have h4 := Stacks.DeRham.FormsGenerators.formsSectionsIso_hom_smul_gen f hV
      (isAffineOpen_top Y) (le_preimage_top f V) c b
    refine (congrArg (formsEquiv f hV a) hgen).trans ?_
    refine (formsEquiv_apply f hV a _).trans (h4.trans ?_)
    refine Eq.trans ?_ (congrArg (Stacks.KatzOda.formsProj (baseMap g) (chartMap f V)
      (totalChartMap f g V) (baseMap_comp_chartMap f g V) a)
        ((formsEquiv_apply (f ≫ g) hV a _).trans h3)).symm
    exact (Stacks.KatzOda.formsProj_smul_ιMulti_d _ _ _ _ a c b).symm


/-- The canonical map `Ω^a_{X/S} ⟶ Ω^a_{X/Y}` on an affine open, read through `sectionsEquiv`, is
the projection of Kähler forms. -/
theorem formsEquiv_sectionsEquiv_relSections {V : X.Opens} (hV : IsAffineOpen V) (a : ℕ)
    (y : ↑(((f ≫ g).sectionsDeRhamComplex.X a).obj (op V))) :
    formsEquiv f hV a (sectionsEquiv f a V ((sectionsEquiv f a V).symm
        (relSections f g a V (sectionsEquiv (f ≫ g) a V y)))) =
      Stacks.KatzOda.formsProj (baseMap g) (chartMap f V) (totalChartMap f g V)
        (baseMap_comp_chartMap f g V) a
        (formsEquiv (f ≫ g) hV a (sectionsEquiv (f ≫ g) a V y)) := by
  rw [LinearEquiv.apply_symm_apply]
  exact formsEquiv_relSections f g hV a _

variable [Smooth f] {ι : Type u} (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) [Fintype ι] [DecidableEq ι]

/-- **The forms of `X/S` and of `X/Y` on the Čech intersections, with the canonical map
`Ω^•_{X/S} ⟶ Ω^•_{X/Y}` between them.** -/
def formsProjData : Stacks.KatzOda.Cech.FormsProjData (U := U) (chartData f g U haff)
    (f ≫ g).sectionsDeRhamComplex f.sectionsDeRhamComplex where
  EP :=
    { L a _ t := Γ(Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ), inter U t)
      instAddCommGroup _ _ _ := inferInstance
      instModule a _ t := baseModule (f ≫ g)
        (Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ)) (inter U t)
      s a _ t := sectionsEquiv (f ≫ g) a (inter U t)
      e' a m t := formsEquiv (f ≫ g) (@haff m t) a
      e'_smul a m t r y := formsEquiv_smul (f ≫ g) (@haff m t) a r y
      e'_cres a m t j y := formsEquiv_sectionsEquiv_cres U haff (f ≫ g) a m t j y
      e'_d a m t y := formsEquiv_sectionsEquiv_d (f ≫ g) (@haff m t) a y }
  EQ :=
    { L a _ t := Γ(Scheme.Hom.relativeDifferentialForms f (a : ℤ), inter U t)
      instAddCommGroup _ _ _ := inferInstance
      instModule a _ t := baseModule f (Scheme.Hom.relativeDifferentialForms f (a : ℤ)) (inter U t)
      s a _ t := sectionsEquiv f a (inter U t)
      e' a m t := formsEquiv f (@haff m t) a
      e'_smul a m t r y := formsEquiv_smul f (@haff m t) a r y
      e'_cres a m t j y := formsEquiv_sectionsEquiv_cres U haff f a m t j y
      e'_d a m t y := formsEquiv_sectionsEquiv_d f (@haff m t) a y }
  pr a _ t y := (sectionsEquiv f a (inter U t)).symm
    (relSections f g a (inter U t) (sectionsEquiv (f ≫ g) a (inter U t) y))
  e'_pr a m t y := formsEquiv_sectionsEquiv_relSections f g (@haff m t) a y

/-- The forms data of `X/S` in `formsProjData` is `formsDataTotal`. -/
theorem formsProjData_EP : (formsProjData f g U haff).EP = formsDataTotal f g U haff := rfl

/-- The forms data of `X/Y` in `formsProjData` is `formsDataRel`. -/
theorem formsProjData_EQ : (formsProjData f g U haff).EQ = formsDataRel f g U haff := rfl

/-- **The intersection-wise projection of the scheme instantiation is the canonical map
`Ω^•_{X/S} ⟶ Ω^•_{X/Y}`.** -/
theorem projAt_eq_relSections (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
    (y : ↑(((f ≫ g).sectionsDeRhamComplex.X a).obj (op (inter U t)))) :
    Stacks.KatzOda.Cech.projAt (chartData f g U haff) (formsDataTotal f g U haff)
        (formsDataRel f g U haff) a t y =
      (sectionsEquiv f a (inter U t)).symm
        (relSections f g a (inter U t) (sectionsEquiv (f ≫ g) a (inter U t) y)) := by
  have h := (formsProjData f g U haff).projAt_eq a t y
  rwa [formsProjData_EP, formsProjData_EQ] at h

end AlgebraicGeometry.DeRhamKatzOdaCech

end
