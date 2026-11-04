module

public import StacksFrontier.RingTheory.Kaehler.KatzOdaCech
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.SectionsDeRhamComplex
public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalGraded
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.WeightZeroChart

/-!
# The filtration of the Čech de Rham complex by forms from the base

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes with `Y` and `S` affine, and let
`U : ι → X` be a family of opens all of whose Čech intersections `U_t` are affine. Write
`R = Γ(S, 𝒪_S)` and `A = Γ(Y, 𝒪_Y)`. Over each intersection the relative forms of `X/S` are the
Kähler forms `⋀ Ω[Γ(X, U_t)⁄R]` (`Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso`),
which are filtered by the forms pulled back from `A` (`Stacks.KatzOda.step`). This file transports
that filtration to the sections of `Ω^•_{X/S}` over the intersections, as a filtration of the
complex of presheaves `Scheme.Hom.sectionsDeRhamComplex (f ≫ g)` on the Čech intersections
(`Stacks.CategoryTheory.CechComplex.InterFiltration`), and identifies its graded pieces, for `f`
smooth, with `Ω^k_{A/R} ⊗_A Γ(U_t, Ω^b_{X/Y})` compatibly with restriction and the differentials
(`Stacks.CategoryTheory.CechComplex.GradedTensorData`).

This is the filtration `F` of the proof of [Stacks, Tag 0FUM], items (6)(a)-(e).

## Main definitions

* `AlgebraicGeometry.DeRhamKatzOdaCech.cechFiltration`: the filtration on the intersections.
* `AlgebraicGeometry.DeRhamKatzOdaCech.gradedData`: the identification of its graded pieces.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

open Stacks.CategoryTheory.CechComplex

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The ring map `Γ(S, 𝒪_S) ⟶ Γ(Y, 𝒪_Y)`. -/
abbrev baseMap : Γ(S, ⊤) ⟶ Γ(Y, ⊤) := g.appLE ⊤ ⊤ (le_preimage_top g ⊤)

/-- The ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, V)`. -/
abbrev chartMap (V : X.Opens) : Γ(Y, ⊤) ⟶ Γ(X, V) := f.appLE ⊤ V (le_preimage_top f V)

/-- The ring map `Γ(S, 𝒪_S) ⟶ Γ(X, V)`. -/
abbrev totalChartMap (V : X.Opens) : Γ(S, ⊤) ⟶ Γ(X, V) :=
  (f ≫ g).appLE ⊤ V (le_preimage_top (f ≫ g) V)

/-- The composite `Γ(S, 𝒪_S) ⟶ Γ(Y, 𝒪_Y) ⟶ Γ(X, V)` is the ring map `Γ(S, 𝒪_S) ⟶ Γ(X, V)` of
`f ≫ g`. -/
theorem baseMap_comp_chartMap (V : X.Opens) :
    baseMap g ≫ chartMap f V = totalChartMap f g V :=
  Scheme.Hom.appLE_comp_appLE f g _ _ _ _ _

/-- The identification of the relative forms over an affine open with Kähler forms, as an
additive equivalence. -/
def formsEquiv {T : Scheme.{u}} [IsAffine T] (q : X ⟶ T) {V : X.Opens} (hV : IsAffineOpen V)
    (a : ℕ) :
    Γ(Scheme.Hom.relativeDifferentialForms q (a : ℤ), V) ≃+
      ⋀[Γ(X, V)]^a ↑(CommRingCat.KaehlerDifferential (q.appLE ⊤ V (le_preimage_top q V))) :=
  (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso q hV (isAffineOpen_top T)
    (le_preimage_top q V) a).toLinearEquiv.toAddEquiv

/-- `formsEquiv` is semilinear along the ring map `Γ(T, 𝒪_T) ⟶ Γ(X, V)` induced by `q`. -/
theorem formsEquiv_smul {T : Scheme.{u}} [IsAffine T] (q : X ⟶ T) {V : X.Opens}
    (hV : IsAffineOpen V) (a : ℕ) (r : Γ(T, ⊤))
    (l : Γ(Scheme.Hom.relativeDifferentialForms q (a : ℤ), V)) :
    letI := baseModule q (Scheme.Hom.relativeDifferentialForms q (a : ℤ)) V
    formsEquiv q hV a (r • l) = q.appLE ⊤ V (le_preimage_top q V) r • formsEquiv q hV a l := by
  let := baseModule q (Scheme.Hom.relativeDifferentialForms q (a : ℤ)) V
  have e : r • l = q.appLE ⊤ V (le_preimage_top q V) r • l := rfl
  rw [e]
  exact Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_smul q hV
    (isAffineOpen_top T) (le_preimage_top q V) a (q.appLE ⊤ V (le_preimage_top q V) r) l

/-- `formsEquiv` carries the restriction of forms from `V` to `V' ≤ V` to the map of Kähler forms
induced by restriction of functions. -/
theorem formsEquiv_restrict {T : Scheme.{u}} [IsAffine T] (q : X ⟶ T) {V V' : X.Opens}
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V) (a : ℕ)
    (l : Γ(Scheme.Hom.relativeDifferentialForms q (a : ℤ), V)) :
    formsEquiv q hV' a
        ((Scheme.Hom.relativeDifferentialForms q (a : ℤ)).presheaf.map (homOfLE hle).op l) =
      Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap (q.appLE ⊤ V (le_preimage_top q V))
        (q.appLE ⊤ V' (le_preimage_top q V')) (X.presheaf.map (homOfLE hle).op)
        (Scheme.Hom.appLE_map _ _ _) a (formsEquiv q hV a l) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_restrict hV hV'
    (isAffineOpen_top T) (le_preimage_top q V) (le_preimage_top q V') hle a l

/-- `formsEquiv` carries the de Rham differential of `X/T` to the exterior derivative
`Stacks.KatzOda.dForms` of Kähler forms. -/
theorem formsEquiv_d {T : Scheme.{u}} [IsAffine T] (q : X ⟶ T) {V : X.Opens}
    (hV : IsAffineOpen V) (a : ℕ) (l : Γ(Scheme.Hom.relativeDifferentialForms q (a : ℤ), V)) :
    formsEquiv q hV (a + 1) ((q.deRhamComplex.d a (a + 1)).val.app (op V) l) =
      Stacks.KatzOda.dForms (q.appLE ⊤ V (le_preimage_top q V)) a (formsEquiv q hV a l) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_deRhamComplex_d q hV
    (isAffineOpen_top T) (le_preimage_top q V) a l

/-- The sections of the forms of `X/T` over `V`, a module over `Γ(T, 𝒪_T)` through `q^♯`,
identified with themselves. -/
def sectionsEquiv {T : Scheme.{u}} (q : X ⟶ T) (b : ℕ) (V : X.Opens) :
    letI := baseModule q (Scheme.Hom.relativeDifferentialForms q (b : ℤ)) V
    ↑((q.sectionsDeRhamComplex.X b).obj (op V)) ≃ₗ[↑Γ(T, ⊤)]
      Γ(Scheme.Hom.relativeDifferentialForms q (b : ℤ), V) :=
  letI := baseModule q (Scheme.Hom.relativeDifferentialForms q (b : ℤ)) V
  { toFun := fun x => x
    invFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- `formsEquiv` carries the restriction maps of the presheaf `q.sectionsDeRhamComplex.X a` to the
maps of Kähler forms induced by restriction of functions. -/
theorem formsEquiv_sectionsEquiv_map {T : Scheme.{u}} [IsAffine T] (q : X ⟶ T) {V V' : X.Opens}
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (i : V' ⟶ V) (a : ℕ)
    (y : ↑((q.sectionsDeRhamComplex.X a).obj (op V))) :
    formsEquiv q hV' a (sectionsEquiv q a V' (((q.sectionsDeRhamComplex.X a).map i.op).hom y)) =
      Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap (q.appLE ⊤ V (le_preimage_top q V))
        (q.appLE ⊤ V' (le_preimage_top q V')) (X.presheaf.map i.op)
        (Scheme.Hom.appLE_map _ _ _) a (formsEquiv q hV a (sectionsEquiv q a V y)) := by
  obtain ⟨⟨hle⟩⟩ := i
  have h1 : sectionsEquiv q a V'
      (((q.sectionsDeRhamComplex.X a).map (Quiver.Hom.op (⟨⟨hle⟩⟩ : V' ⟶ V))).hom y) =
      (Scheme.Hom.relativeDifferentialForms q (a : ℤ)).presheaf.map (homOfLE hle).op
        (sectionsEquiv q a V y) := rfl
  rw [h1]
  exact formsEquiv_restrict q hV hV' hle a _

/-- `formsEquiv` carries the differential of `q.sectionsDeRhamComplex` to the exterior
derivative `Stacks.KatzOda.dForms` of Kähler forms. -/
theorem formsEquiv_sectionsEquiv_d {T : Scheme.{u}} [IsAffine T] (q : X ⟶ T) {V : X.Opens}
    (hV : IsAffineOpen V) (a : ℕ) (y : ↑((q.sectionsDeRhamComplex.X a).obj (op V))) :
    formsEquiv q hV (a + 1)
        (sectionsEquiv q (a + 1) V (((q.sectionsDeRhamComplex.d a (a + 1)).app (op V)).hom y)) =
      Stacks.KatzOda.dForms (q.appLE ⊤ V (le_preimage_top q V)) a
        (formsEquiv q hV a (sectionsEquiv q a V y)) := by
  have h1 : sectionsEquiv q (a + 1) V (((q.sectionsDeRhamComplex.d a (a + 1)).app (op V)).hom y) =
      (q.deRhamComplex.d a (a + 1)).val.app (op V) (sectionsEquiv q a V y) := rfl
  rw [h1]
  exact formsEquiv_d q hV a _

variable [IsAffine Y] [IsAffine S] [Smooth f]

/-- For `f` smooth and `V` affine, the ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, V)` is formally smooth. -/
theorem chartMap_formallySmooth {V : X.Opens} (hV : IsAffineOpen V) :
    (chartMap f V).hom.FormallySmooth :=
  (HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top Y⟩ ⟨V, hV⟩
    _).formallySmooth

variable {ι : Type u} (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t))

/-- **The rings of functions on the Čech intersections**, as algebras over `Γ(Y, 𝒪_Y)` and
`Γ(S, 𝒪_S)`, with the restriction maps along the face maps. -/
def chartData : Stacks.KatzOda.Cech.ChartData (ι := ι) (baseMap g) where
  B t := Γ(X, inter U t)
  φ t := chartMap f (inter U t)
  ψ t := totalChartMap f g (inter U t)
  comp_φ _ := baseMap_comp_chartMap f g _
  ρ t j := X.presheaf.map (interMap U t (Fin.succAbove j)).op
  φ_ρ _ _ := Scheme.Hom.appLE_map _ _ _
  ψ_ρ _ _ := Scheme.Hom.appLE_map _ _ _
  formallySmooth {m} t := chartMap_formallySmooth f (@haff m t)

/-- `formsEquiv` carries the restriction `cres` along the face map `Fin.succAbove j` between Čech
intersections to the map of Kähler forms induced by restriction of functions. -/
theorem formsEquiv_sectionsEquiv_cres {T : Scheme.{u}} [IsAffine T] (q : X ⟶ T) (a m : ℕ)
    (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (y : ↑((q.sectionsDeRhamComplex.X a).obj (op (inter U (t ∘ Fin.succAbove j))))) :
    formsEquiv q (@haff (m + 1) t) a (sectionsEquiv q a (inter U t)
        (cres U (q.sectionsDeRhamComplex.X a) (Fin.succAbove j) t y)) =
      Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap
        (q.appLE ⊤ (inter U (t ∘ Fin.succAbove j)) (le_preimage_top q _))
        (q.appLE ⊤ (inter U t) (le_preimage_top q _))
        (X.presheaf.map (interMap U t (Fin.succAbove j)).op) (Scheme.Hom.appLE_map _ _ _) a
        (formsEquiv q (@haff m (t ∘ Fin.succAbove j)) a
          (sectionsEquiv q a (inter U (t ∘ Fin.succAbove j)) y)) := by
  convert formsEquiv_sectionsEquiv_map q (@haff m (t ∘ Fin.succAbove j)) (@haff (m + 1) t)
    (interMap U t (Fin.succAbove j)) a y using 3

/-- **The forms of `X/S` on the Čech intersections as Kähler forms over `Γ(S, 𝒪_S)`.** -/
def formsDataTotal [Fintype ι] [DecidableEq ι] :
    Stacks.KatzOda.Cech.FormsData U (chartData f g U haff) (chartData f g U haff).ψ
      (chartData f g U haff).ψ_ρ (f ≫ g).sectionsDeRhamComplex where
  L a _ t := Γ(Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ), inter U t)
  instAddCommGroup _ _ _ := inferInstance
  instModule a _ t := baseModule (f ≫ g) (Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ))
    (inter U t)
  s a _ t := sectionsEquiv (f ≫ g) a (inter U t)
  e' a m t := formsEquiv (f ≫ g) (@haff m t) a
  e'_smul a m t r y := formsEquiv_smul (f ≫ g) (@haff m t) a r y
  e'_cres a m t j y := formsEquiv_sectionsEquiv_cres U haff (f ≫ g) a m t j y
  e'_d a m t y := formsEquiv_sectionsEquiv_d (f ≫ g) (@haff m t) a y

/-- **The forms of `X/Y` on the Čech intersections as Kähler forms over `Γ(Y, 𝒪_Y)`.** -/
def formsDataRel [Fintype ι] [DecidableEq ι] :
    Stacks.KatzOda.Cech.FormsData U (chartData f g U haff) (chartData f g U haff).φ
      (chartData f g U haff).φ_ρ f.sectionsDeRhamComplex where
  L a _ t := Γ(Scheme.Hom.relativeDifferentialForms f (a : ℤ), inter U t)
  instAddCommGroup _ _ _ := inferInstance
  instModule a _ t := baseModule f (Scheme.Hom.relativeDifferentialForms f (a : ℤ)) (inter U t)
  s a _ t := sectionsEquiv f a (inter U t)
  e' a m t := formsEquiv f (@haff m t) a
  e'_smul a m t r y := formsEquiv_smul f (@haff m t) a r y
  e'_cres a m t j y := formsEquiv_sectionsEquiv_cres U haff f a m t j y
  e'_d a m t y := formsEquiv_sectionsEquiv_d f (@haff m t) a y

variable [Fintype ι] [DecidableEq ι]

/-- **The filtration of the de Rham complex of `X/S` by the forms from `Y`**, on the Čech
intersections. -/
abbrev cechFiltration : InterFiltration U (f ≫ g).sectionsDeRhamComplex :=
  Stacks.KatzOda.Cech.filtration (chartData f g U haff) (formsDataTotal f g U haff)

/-- **The graded pieces of the filtration by the forms from `Y`**:
`gr^k Γ(U_t, Ω^{k+b}_{X/S}) ≅ Ω^k_{A/R} ⊗_A Γ(U_t, Ω^b_{X/Y})`, compatibly with the restrictions
and the differentials. -/
abbrev gradedData (k : ℕ) :
    GradedTensorData U (Stacks.KatzOda.Cech.formsN (baseMap g) k) f.sectionsDeRhamComplex
      (cechFiltration f g U haff) k :=
  Stacks.KatzOda.Cech.gradedTensorData (chartData f g U haff) (formsDataTotal f g U haff)
    (formsDataRel f g U haff) k

end AlgebraicGeometry.DeRhamKatzOdaCech

end
