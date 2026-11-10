module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateConeFormsKernelVanishing
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono

/-!
# Clause (3) of Stacks 0FUR: the ordered Čech complex of the positive-weight part

Let `K` be the kernel of `π_*r : π_*Ω^a_{L/S} ⟶ π_*0_*Ω^a_{P/S}` in the standard situation of
Section 50.16 of the source. On the intersection `⋂_{j ∈ t} D₊(yⱼ) = D₊(∏_{j ∈ t} yⱼ)` of the
standard cover of `P` the sections of `K` are, through
`Stacks.DeRham.CoordinateCone.formChart`, the localized forms of `Ω^a_{A/R}` of positive weight
(`Stacks.DeRham.CoordinateCone.formChart_kernel_mem`,
`Stacks.DeRham.CoordinateCone.exists_formChart_kernel_eq`), compatibly with restriction
(`Stacks.DeRham.CoordinateCone.formChart_restrict`). The ordered Čech complex of `K` for the cover
by the `D₊(yⱼ)` is therefore the positive part of the Čech complex `C^•(y₁, …, yₙ; Ω^a_{A/R})`,
which is exact; so `K` has no cohomology in positive degrees.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite KaehlerDifferential

universe u

namespace Stacks.ConeKernelSections

variable {X : Scheme.{u}}

/-- The sections of the presheaf of abelian groups underlying a module, as sections of the
module. -/
def abSectionsHom (F : X.Modules) (W : X.Opens) :
    ToType ((Stacks.Cohomology.CechSheaf.abSections F :
      TopCat.Presheaf AddCommGrpCat (TopCat.of X)).obj (op W)) →+ Γ(F, W) where
  toFun x := x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `abSectionsHom` is injective. -/
theorem abSectionsHom_injective (F : X.Modules) (W : X.Opens) :
    Function.Injective (abSectionsHom F W) := fun _ _ h => h

/-- `abSectionsHom` commutes with restriction to a smaller open. -/
theorem abSectionsHom_restr (F : X.Modules) {W W' : X.Opens} (h : W' ≤ W)
    (x : ToType ((Stacks.Cohomology.CechSheaf.abSections F :
      TopCat.Presheaf AddCommGrpCat (TopCat.of X)).obj (op W))) :
    abSectionsHom F W' (CechCochains.restr (Stacks.Cohomology.CechSheaf.abSections F :
      TopCat.Presheaf AddCommGrpCat (TopCat.of X)) h x) =
      F.presheaf.map (homOfLE h).op (abSectionsHom F W x) :=
  rfl

/-- An injective additive map after the restricted kernel sections on the whole preimage is
injective. -/
theorem comp_restrictedKernelHom_injective {Y : Scheme.{u}} (f : X ⟶ Y) {M N' : X.Modules}
    (ρ : M ⟶ N') (U : Y.Opens) {V : X.Opens} (hV : V = f ⁻¹ᵁ U) {C : Type*} [AddCommGroup C]
    (F : Γ(M, V) →+ C) (hF : Function.Injective F) :
    Function.Injective (F.comp ((restrictedKernelHom f ρ U (eqToHom hV)).comp
      (abSectionsHom (kernel ((Scheme.Modules.pushforward f).map ρ)) U))) :=
  fun _ _ h => abSectionsHom_injective _ _ (restrictedKernelHom_injective f ρ U _ hV (hF h))

/-- The restricted kernel sections of the sections of the presheaf of abelian groups commute with
restriction. -/
theorem comp_restrictedKernelHom_restr {Y : Scheme.{u}} (f : X ⟶ Y) {M N' : X.Modules}
    (ρ : M ⟶ N') {U U' : Y.Opens} (h : U' ≤ U) {V V' : X.Opens} (hV : V = f ⁻¹ᵁ U)
    (hV' : V' = f ⁻¹ᵁ U') (hVV : V' ≤ V)
    (x : ToType ((Stacks.Cohomology.CechSheaf.abSections
      (kernel ((Scheme.Modules.pushforward f).map ρ)) :
      TopCat.Presheaf AddCommGrpCat (TopCat.of Y)).obj (op U))) :
    restrictedKernelHom f ρ U' (eqToHom hV')
        (abSectionsHom (kernel ((Scheme.Modules.pushforward f).map ρ)) U'
          (CechCochains.restr (Stacks.Cohomology.CechSheaf.abSections
            (kernel ((Scheme.Modules.pushforward f).map ρ)) :
            TopCat.Presheaf AddCommGrpCat (TopCat.of Y)) h x)) =
      M.presheaf.map (homOfLE hVV).op (restrictedKernelHom f ρ U (eqToHom hV)
        (abSectionsHom (kernel ((Scheme.Modules.pushforward f).map ρ)) U x)) :=
  (congrArg (restrictedKernelHom f ρ U' (eqToHom hV')) (abSectionsHom_restr _ h x)).trans
    (restrictedKernelHom_restr f ρ U (eqToHom hV) h (eqToHom hV') hVV _)

/-- **`f_*ρ` is surjective on sections over `U`** when `ρ = φ ≫ ψ` with `ψ` an isomorphism and `φ`
is surjective on sections over `V = f⁻¹U`. -/
theorem surjective_app_pushforward_map {Y : Scheme.{u}} (f : X ⟶ Y) {M N N' : X.Modules}
    (ρ : M ⟶ N') {φ : M ⟶ N} {V : X.Opens} (U : Y.Opens) (hV : V = f ⁻¹ᵁ U)
    (hφ : Function.Surjective (Scheme.Modules.Hom.app φ V)) {ψ : N ⟶ N'} [IsIso ψ]
    (hρ : ρ = φ ≫ ψ) :
    Function.Surjective (Scheme.Modules.Hom.app ((Scheme.Modules.pushforward f).map ρ) U) := by
  subst hV
  subst hρ
  intro y
  obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app ψ (f ⁻¹ᵁ U))).2 y
  obtain ⟨z, rfl⟩ := hφ w
  exact ⟨z, hw⟩

/-- **A morphism of modules which is surjective on the sections over arbitrarily small
neighbourhoods of every point is an epimorphism.** -/
theorem epi_of_surjective_app {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ (U : X.Opens) (x : X), x ∈ U →
      ∃ V : X.Opens, V ≤ U ∧ x ∈ V ∧ Function.Surjective (Scheme.Modules.Hom.app f V)) :
    Epi f := by
  refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections f fun U t x hx => ?_
  obtain ⟨V, hVU, hxV, hs⟩ := h U x hx
  obtain ⟨s, hs'⟩ := hs (N.val.map (homOfLE hVU).op t)
  exact ⟨V, hVU, hxV, s, hs'⟩

end Stacks.ConeKernelSections

namespace Stacks.DeRham.CoordinateCone

open Cech.WeightedVariables Stacks.ProjConeChartForms Stacks.Truncation Stacks.Truncation.Chart
open Stacks.AlgebraicGeometry.ProjAndSpec Stacks.AlgebraicGeometry.ProjAndSpecTruncation
open CechCochains CechCochains.Coordinates

variable {R : Type u} [CommRing R] {m n : ℕ} (a : ℕ)

/-- The indices of the standard cover `D₊(yⱼ)` of `P` are ordered as `Fin n`. -/
abbrev coverOrder : ULift.{u} (Fin n) ≃o Fin n := ULift.orderIso

/-- The first index of an ordered index `i` lies in its support. -/
theorem mem_supp {p : ℕ} (i : OrdIndex (I := ULift.{u} (Fin n)) p) :
    coverOrder (i.1 0) ∈ supp coverOrder i.1 :=
  Finset.mem_image_of_mem _ (Finset.mem_univ 0)

/-- The product of the variables `yₖ` over the support of an ordered index `i` is the product of
the variables `y_{i k}`. -/
theorem prod_supp {p : ℕ} (i : OrdIndex (I := ULift.{u} (Fin n)) p) :
    (∏ k ∈ supp coverOrder i.1, yVar R m n k) =
      ∏ k, (MvPolynomial.X (Sum.inr (i.1 k).down) : MvPolynomial (Fin m ⊕ Fin n) R) := by
  rw [supp, Finset.prod_image (f := yVar R m n) (g := ⇑coverOrder ∘ i.1)
    fun x _ y _ h => i.2.injective (coverOrder.injective h)]
  rfl

/-- **The chart of the cone over an intersection of the standard cover is the whole preimage of the
intersection.** -/
theorem chartOpen_eq_preimage_inter {p : ℕ} (i : OrdIndex (I := ULift.{u} (Fin n)) p) :
    chartOpen (yGrading R m n) (∏ k ∈ supp coverOrder i.1, yVar R m n k) =
      coneProjection R m n ⁻¹ᵁ inter (bundleCover R m n) i.1 := by
  rw [prod_supp]
  refine (Stacks.AlgebraicGeometry.ProjAndSpecTruncation.pi_preimage_basicOpen
    (𝒜 := yGrading R m n) _ (p + 1) (prod_mem_yGrading R m n i.1) (Nat.succ_pos p)).symm.trans ?_
  exact congrArg (coneProjection R m n ⁻¹ᵁ ·) (iInf_bundleCover R m n i.1).symm

/-- The chart of `∏_{k ∈ supp i} yₖ` is contained in the chart of the product over the support
of the index obtained from `i` by omitting its `j`-th entry. -/
theorem chartOpen_le_omit {p : ℕ} (i : OrdIndex (I := ULift.{u} (Fin n)) (p + 1))
    (j : Fin (p + 2)) :
    chartOpen (yGrading R m n) (∏ k ∈ supp coverOrder i.1, yVar R m n k) ≤
      chartOpen (yGrading R m n)
        (∏ k ∈ supp coverOrder (⟨i.1 ∘ j.succAbove, strictMono_omit i.2 j⟩ :
          OrdIndex (I := ULift.{u} (Fin n)) p).1, yVar R m n k) := by
  rw [chartOpen_eq_preimage_inter, chartOpen_eq_preimage_inter]
  exact leOfHom ((TopologicalSpace.Opens.map (coneProjection R m n).base).map
    (homOfLE (inter_le_omit (bundleCover R m n) i.1 j)))

/-- **The coordinates of the ordered Čech cochains of `K`**: a section of `K` over
`⋂_k D₊(y_{i k})` goes to the localized form of `Ω^a_{A/R}` it restricts to on the punctured
cone, read in the chart of `j ∈ supp i`. -/
local notation "cechCoord[" R ", " m ", " n ", " a ", " i ", " hj ", " hV "]" =>
  AddMonoidHom.comp (formChartHom (R := R) (m := m) a hj)
    (AddMonoidHom.comp (Stacks.ConeKernelSections.restrictedKernelHom (coneProjection R m n)
      (coneFormsRestriction R m n (Nat.cast a)) (inter (bundleCover R m n) (Subtype.val i))
        (eqToHom hV))
      (Stacks.ConeKernelSections.abSectionsHom _ _))

section Coord

variable {p : ℕ} (i : OrdIndex (I := ULift.{u} (Fin n)) p) {j : Fin n}
  (hj : j ∈ supp coverOrder i.1)
  (hV : chartOpen (yGrading R m n) (∏ k ∈ supp coverOrder i.1, yVar R m n k) =
      coneProjection R m n ⁻¹ᵁ inter (bundleCover R m n) i.1)

/-- The coordinates `cechCoord` of the ordered Čech cochains of `K` are injective. -/
theorem cechCoord_injective : Function.Injective cechCoord[R, m, n, a, i, hj, hV] :=
  Stacks.ConeKernelSections.comp_restrictedKernelHom_injective (coneProjection R m n)
    (coneFormsRestriction R m n (a : ℤ)) (inter (bundleCover R m n) i.1) hV (formChartHom a hj)
    (formChart_injective a hj)

/-- The coordinates `cechCoord` of a section of `K` lie in the positive-weight part. -/
theorem cechCoord_mem (x : ToType ((Stacks.Cohomology.CechSheaf.abSections
      (kernel ((Scheme.Modules.pushforward (coneProjection R m n)).map
        (coneFormsRestriction R m n (a : ℤ)))) :
      TopCat.Presheaf AddCommGrpCat (TopCat.of (coneBundle R m n))).obj
        (op (inter (bundleCover R m n) i.1)))) :
    cechCoord[R, m, n, a, i, hj, hV] x ∈ posPart R m n a (supp coverOrder i.1) :=
  formChart_kernel_mem a hj _ _ _

/-- Every element of the positive-weight part is the coordinate `cechCoord` of a section of `K`. -/
theorem cechCoord_surj (z : Cech.cechMod (yVar R m n) (Forms R m n a) (supp coverOrder i.1))
    (hz : z ∈ posPart R m n a (supp coverOrder i.1)) :
    ∃ x : ToType ((Stacks.Cohomology.CechSheaf.abSections
      (kernel ((Scheme.Modules.pushforward (coneProjection R m n)).map
        (coneFormsRestriction R m n (a : ℤ)))) :
      TopCat.Presheaf AddCommGrpCat (TopCat.of (coneBundle R m n))).obj
        (op (inter (bundleCover R m n) i.1))),
      cechCoord[R, m, n, a, i, hj, hV] x = z := by
  have e := exists_formChart_kernel_eq a hj _ (eqToHom hV) hV z hz
  exact ⟨e.choose, e.choose_spec⟩

end Coord

/-- The coordinates `cechCoord` commute with restriction: the coordinate of the restriction of a
section along the omission of the `j`-th index is the image under `Cech.cechι` of its
coordinate. -/
theorem cechCoord_restr {p : ℕ} (i : OrdIndex (I := ULift.{u} (Fin n)) (p + 1)) (j : Fin (p + 2))
    {j₁ j₂ : Fin n} (hj₁ : j₁ ∈ supp coverOrder i.1)
    (hj₂ : j₂ ∈ supp coverOrder (⟨i.1 ∘ j.succAbove, strictMono_omit i.2 j⟩ :
      OrdIndex (I := ULift.{u} (Fin n)) p).1)
    (x : ToType ((Stacks.Cohomology.CechSheaf.abSections
      (kernel ((Scheme.Modules.pushforward (coneProjection R m n)).map
        (coneFormsRestriction R m n (a : ℤ)))) :
      TopCat.Presheaf AddCommGrpCat (TopCat.of (coneBundle R m n))).obj
        (op (inter (bundleCover R m n) (i.1 ∘ j.succAbove))))) :
    cechCoord[R, m, n, a, i, hj₁, chartOpen_eq_preimage_inter i]
      (CechCochains.restr (Stacks.Cohomology.CechSheaf.abSections
        (kernel ((Scheme.Modules.pushforward (coneProjection R m n)).map
          (coneFormsRestriction R m n (a : ℤ)))) :
        TopCat.Presheaf AddCommGrpCat (TopCat.of (coneBundle R m n)))
          (inter_le_omit (bundleCover R m n) i.1 j) x) =
      Cech.cechι (yVar R m n) (Forms R m n a) (supp_omit_subset coverOrder i.1 j)
        (cechCoord[R, m, n, a, (⟨i.1 ∘ j.succAbove, strictMono_omit i.2 j⟩ :
          OrdIndex (I := ULift.{u} (Fin n)) p), hj₂,
          chartOpen_eq_preimage_inter (⟨i.1 ∘ j.succAbove, strictMono_omit i.2 j⟩ :
            OrdIndex (I := ULift.{u} (Fin n)) p)] x) :=
  (congrArg (formChart a hj₁)
    (Stacks.ConeKernelSections.comp_restrictedKernelHom_restr (coneProjection R m n)
      (coneFormsRestriction R m n (a : ℤ)) (inter_le_omit (bundleCover R m n) i.1 j)
      (chartOpen_eq_preimage_inter (⟨i.1 ∘ j.succAbove, strictMono_omit i.2 j⟩ :
        OrdIndex (I := ULift.{u} (Fin n)) p)) (chartOpen_eq_preimage_inter i)
      (chartOpen_le_omit i j)
      x)).trans
    (formChart_restrict a (supp_omit_subset coverOrder i.1 j) hj₂ hj₁ (chartOpen_le_omit i j) _)


/-- **`K` is quasi-coherent**: the cone projection and the zero section are affine. -/
theorem isQuasicoherent_coneFormsKernel :
    (kernel ((Scheme.Modules.pushforward (coneProjection R m n)).map
      (coneFormsRestriction R m n (a : ℤ)))).IsQuasicoherent := by
  have h1 := Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom (coneProjection R m n)
    (Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ)) inferInstance
  have h2 := Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom (coneProjection R m n) _
    (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom
      (zeroSection (truncationConeData (yGrading R m n)))
      (Scheme.Hom.relativeDifferentialForms (coneBundleToBase R m n) (a : ℤ))
      (Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ _))
  exact Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _

/-- **(V) of clause (3) of [Stacks, Tag 0FUR]: `K` has no cohomology on `P` in positive
degrees.** The ordered Čech complex of `K` for the cover of `P` by the `D₊(yⱼ)` is, through the
coordinates `cechCoord`, the positive part of the Čech complex `C^•(y₁, …, yₙ; Ω^a_{A/R})`,
which is exact. -/
theorem isZero_rightDerived_coneFormsKernel (p : ℕ) (hp : 1 ≤ p) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (coneBundle R m n) ⊤).rightDerived p).obj
      (kernel ((Scheme.Modules.pushforward (coneProjection R m n)).map
        (coneFormsRestriction R m n (a : ℤ))))) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have := isQuasicoherent_coneFormsKernel (R := R) (m := m) (n := n) a
  refine isZero_rightDerived_bundle_of_exact R m n _ q fun c hc => ?_
  exact exists_ordD_eq_of_exists_cechD_eq
    (Ψ := fun p i => cechCoord[R, m, n, a, i, mem_supp i, chartOpen_eq_preimage_inter i])
    (fun s => posPart R m n a s)
    (fun p i j x => cechCoord_restr a i j (mem_supp i)
      (mem_supp (⟨i.1 ∘ j.succAbove, strictMono_omit i.2 j⟩ :
        OrdIndex (I := ULift.{u} (Fin n)) p)) x)
    (fun p i => cechCoord_injective a i (mem_supp i) _)
    (fun p i x => cechCoord_mem a i (mem_supp i) _ x)
    (fun p i z hz => cechCoord_surj a i (mem_supp i) _ z hz)
    (fun h z hz => cechι_mem_posPart h hz) q (forms_exists_eq_cechD_of_posPart q) c hc


/-! ### `π_*r` is an epimorphism -/

/-- The comparison map is surjective on the chart of `D₊(yⱼ h)`. -/
theorem surjective_comparison_app (j : Fin n) {h : MvPolynomial (Fin m ⊕ Fin n) R} {d : ℕ}
    (hh : h ∈ yGrading R m n d) :
    Function.Surjective (Scheme.Modules.Hom.app (Scheme.Hom.formsDirectImageComparison
        (zeroSection (truncationConeData (yGrading R m n))) (coneToBase R m n) (a : ℤ))
        (chartOpen (yGrading R m n) (yVar R m n j * h))) :=
  surjective_formsDirectImageComparison_zeroSection_app (coneToBase R m n) rfl
    (yVar_mem_yGrading j) hh rfl a

/-- **`π_*r` is surjective on the sections over `D₊(yⱼ h)`.** -/
theorem surjective_app_restriction (j : Fin n) {h : MvPolynomial (Fin m ⊕ Fin n) R} {d : ℕ}
    (hh : h ∈ yGrading R m n d) :
    Function.Surjective (Scheme.Modules.Hom.app
      ((Scheme.Modules.pushforward (coneProjection R m n)).map (coneFormsRestriction R m n (a : ℤ)))
      (Proj.basicOpen (yGrading R m n) (yVar R m n j * h))) :=
  Stacks.ConeKernelSections.surjective_app_pushforward_map (coneProjection R m n)
    (coneFormsRestriction R m n (a : ℤ)) _
    (Stacks.AlgebraicGeometry.ProjAndSpecTruncation.pi_preimage_basicOpen (𝒜 := yGrading R m n)
      (yVar R m n j * h) (d + 1)
      (Stacks.GradedLaurent.mem_of_mul_eq (yGrading R m n) (yVar_mem_yGrading j) hh rfl)
      (Nat.succ_pos d)).symm
    (surjective_comparison_app a j hh) (coneFormsRestriction.eq_1 R m n (a : ℤ))

/-- **(E) of clause (3) of [Stacks, Tag 0FUR]: `π_*r : π_*Ω^a_{L/S} ⟶ π_*0_*Ω^a_{P/S}` is an
epimorphism.** Every point of `P` has arbitrarily small neighbourhoods `D₊(yⱼ h)`, and on such a
chart the restriction of forms to the zero section `B₍ψ(yⱼh)₎ = A₍yⱼh₎[X] → A₍yⱼh₎` has a
section. -/
theorem epi_pushforward_coneProjection_coneFormsRestriction :
    Epi ((Scheme.Modules.pushforward (coneProjection R m n)).map
      (coneFormsRestriction R m n (a : ℤ))) := by
  refine Stacks.ConeKernelSections.epi_of_surjective_app _ fun U x hx => ?_
  have hx' : x ∈ ⨆ j, bundleCover R m n j := by
    rw [← iSup_bundleCover]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
  obtain ⟨_, ⟨f₀, rfl⟩, hxf, hfle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    (Proj.isBasis_basicOpen (yGrading R m n)) (show x ∈ U ⊓ bundleCover R m n j from ⟨hx, hj⟩)
  have hxf' := hxf
  rw [Proj.basicOpen_eq_iSup_proj] at hxf'
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hxf'
  have hh : GradedRing.proj (yGrading R m n) i f₀ ∈ yGrading R m n i := by
    rw [GradedRing.proj_apply]
    exact (DirectSum.decompose (yGrading R m n) f₀ i).2
  have hproj : Proj.basicOpen (yGrading R m n) (GradedRing.proj (yGrading R m n) i f₀) ≤
      Proj.basicOpen (yGrading R m n) f₀ := by
    rw [Proj.basicOpen_eq_iSup_proj (yGrading R m n) f₀]
    exact le_iSup
      (fun i => Proj.basicOpen (yGrading R m n) (GradedRing.proj (yGrading R m n) i f₀)) i
  refine ⟨Proj.basicOpen (yGrading R m n)
      (yVar R m n j.down * GradedRing.proj (yGrading R m n) i f₀),
    ?_, ?_, surjective_app_restriction a j.down hh⟩
  · rw [Proj.basicOpen_mul]
    exact inf_le_right.trans (hproj.trans (hfle.trans inf_le_left))
  · rw [Proj.basicOpen_mul]
    exact ⟨hj, hi⟩


/-! ### Clause (3) -/

section Derived

open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [-instance] CategoryTheory.catToReflQuiver

variable
  [HasDerivedCategory (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneTotal R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneCentre R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneBundle R m n).toRingedSpace)]

/-- **Clause (3) of [Stacks, Tag 0FUR].** In the standard situation of Section 50.16 — `X = Spec A`
for `A = R[x₁, …, x_m, y₁, …, y_n]`, `Z = Spec A₀ = V(y₁, …, y_n)`, `b : L ⟶ X` the blowing up of
`X` along `Z` with exceptional divisor `P = Proj(A) = 𝐏^{n-1}_Z`, `p : P ⟶ Z` and `i : Z ⟶ X` —
the canonical map `Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S}` is an isomorphism on cohomology sheaves in
every degree `q ≥ 1`, for every `a ≥ 0`.

By `isIso_homology_coneFormsDerivedComparison_of_vanishing` it is enough that `π_*r` is an
epimorphism (`epi_pushforward_coneProjection_coneFormsRestriction`) and that its kernel has no
cohomology on `P` in positive degrees (`isZero_rightDerived_coneFormsKernel`), where
`π : L ⟶ P` is the cone projection and `r : Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S}` the restriction of forms to
the zero section. -/
@[stacks 0FUR "clause (3): Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S} is an isomorphism on cohomology \
sheaves in every degree q ≥ 1, every a ≥ 0, every n ≥ 1, for the blowup L of X = Spec(A) along \
Z = Spec(A₀) as in Section 50.16"]
theorem isIso_homology_coneFormsDerivedComparison (a q : ℕ) (hq : 1 ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor _ (q : ℤ)).map
      (coneFormsDerivedComparison R m n (a : ℤ))) :=
  have := epi_pushforward_coneProjection_coneFormsRestriction (R := R) (m := m) (n := n) a
  isIso_homology_coneFormsDerivedComparison_of_vanishing R m n a
    (fun p hp => isZero_rightDerived_coneFormsKernel a p hp) q hq

end Derived

end Stacks.DeRham.CoordinateCone

end
