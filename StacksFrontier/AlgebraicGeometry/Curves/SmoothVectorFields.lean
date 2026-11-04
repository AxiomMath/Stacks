module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.DerivationZero
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationNodalDescent
public import StacksFrontier.AlgebraicGeometry.Curves.SingularGenusZero
public import StacksFrontier.AlgebraicGeometry.Curves.UniformizerDifferential
public import StacksFrontier.AlgebraicGeometry.F6Rank136.SmoothIsNodal
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularSmooth
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CokernelSupportDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vector fields on a smooth curve

Let `X` be a scheme over a field `k`. A vector field `D ∈ Der_k(𝒪_X, 𝒪_X)` factors as
`D = θ ∘ d` through the universal derivation `d : 𝒪_X ⟶ Ω_{X/k}`, for a unique `𝒪_X`-linear
`θ : Ω_{X/k} ⟶ 𝒪_X`. This file relates the points fixed by `D` to the zeros of `θ`, and bounds
their number on a smooth proper curve by `-deg(Ω_{X/k})`.

## Main definitions

* `Stacks.Curves.SheafDerivationOf.differentialsHom`: the morphism `θ : Ω_{X/k} ⟶ 𝒪_X` with
  `D = θ ∘ d`.
* `Stacks.Curves.SheafDerivationOf.restrictOpens`: the restriction of a vector field along an
  open immersion.

## Main results

* `Stacks.Curves.SheafDerivationOf.fixes_of_not_surjective`: if the stalk of `θ` at a closed
  point `x` is not surjective, then `D` fixes `x`.
* `Stacks.Curves.SheafDerivationOf.not_surjective_of_fixes`: conversely, over an algebraically
  closed field, if `D` fixes the closed point `x` then the stalk of `θ` at `x` is not surjective.
* `Stacks.Curves.smooth_normalizationOverField_of_isCurve`: the normalization of a curve over an
  algebraically closed field is smooth.
* `Stacks.Curves.SheafDerivationOf.encard_setOf_fixes_le`: a nonzero vector field on a smooth
  proper curve over an algebraically closed field fixes at most `-deg(Ω_{X/k})` closed points.
* `Stacks.Curves.SheafDerivationOf.fixes_restrictOpens` and
  `Stacks.Curves.SheafDerivationOf.eq_zero_of_restrictOpens_eq_zero`: restriction along open
  immersions preserves fixed points, and a vector field vanishing along a jointly surjective
  family of open immersions vanishes.

## Implementation notes

"`θ` vanishes at `x`" is expressed as non-surjectivity of the stalk map
`Ω_{X/k, x} ⟶ 𝒪_{X,x}`: its image is an ideal of the local ring `𝒪_{X,x}`, which is proper
exactly when it lies in the maximal ideal. This is the form that the support of the cokernel of
`θ` sees (`AlgebraicGeometry.mem_supp_cokernel_iff_not_surjective`).

## References

* [Stacks Project, Tag 0E67](https://stacks.math.columbia.edu/tag/0E67)
* [Stacks Project, Tag 0C1E](https://stacks.math.columbia.edu/tag/0C1E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.ModuleStalk IsLocalRing

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} {g : X ⟶ Spec (.of k)}

namespace SheafDerivationOf

/-- The zero vector field. -/
instance instZero : Zero (SheafDerivationOf g) :=
  PresheafOfModules.Derivation.instZero (R := X.presheaf)

/-- The zero vector field vanishes on every local section. -/
@[simp] theorem zero_onSections {U : X.Opens} (a : Γ(X, U)) :
    (0 : SheafDerivationOf g).onSections a = 0 := rfl

/-- **The morphism `θ : Ω_{X/k} ⟶ 𝒪_X` attached to a vector field `D`**, the unique one with
`D = θ ∘ d` for the universal derivation `d : 𝒪_X ⟶ Ω_{X/k}`. -/
def differentialsHom (D : SheafDerivationOf g) :
    Scheme.Hom.relativeDifferentials g ⟶ Stacks.UnitStalk.unitModule X :=
  (Scheme.Hom.existsUnique_hom_relativeDifferentials g _ D).exists.choose

/-- `D = θ ∘ d`. -/
theorem postcomp_differentialsHom (D : SheafDerivationOf g) :
    (Scheme.Hom.universalRelativeDerivation g).postcomp D.differentialsHom.val = D :=
  (Scheme.Hom.existsUnique_hom_relativeDifferentials g _ D).exists.choose_spec

/-- `θ (d a) = D a` on local sections. -/
theorem differentialsHom_app_d (D : SheafDerivationOf g) (U : X.Opens) (a : Γ(X, U)) :
    D.differentialsHom.app U ((Scheme.Hom.universalRelativeDerivation g).d (X := op U) a) =
      D.onSections a :=
  PresheafOfModules.Derivation.congr_d D.postcomp_differentialsHom a

/-- **A nonzero vector field has nonzero `θ`.** -/
theorem differentialsHom_ne_zero {D : SheafDerivationOf g} (hD : D ≠ 0) :
    D.differentialsHom ≠ 0 := by
  intro h
  apply hD
  rw [← D.postcomp_differentialsHom, h]
  exact PresheafOfModules.Derivation.postcomp_zero _

/-- **The stalk of `θ` sends the germ of `d a` to the germ of `D a`.** -/
theorem mapFun_differentialsHom_germ (D : SheafDerivationOf g) (x : X) (U : X.Opens)
    (hxU : x ∈ U) (a : Γ(X, U)) :
    mapFun D.differentialsHom x
        ((Scheme.Modules.presheaf (Scheme.Hom.relativeDifferentials g)).germ U x hxU
          ((Scheme.Hom.universalRelativeDerivation g).d (X := op U) a)) =
      Stacks.UnitStalk.unitStalkLinearEquiv X x
        ((X.presheaf.germ U x hxU).hom (D.onSections a)) := by
  refine (mapFun_germ D.differentialsHom x U hxU _).trans ?_
  rw [differentialsHom_app_d, Stacks.UnitStalk.unitStalkLinearEquiv_germ]

/-- **A vector field fixes every closed point at which `θ` vanishes.** If the image of the stalk
`Ω_{X/k, x} ⟶ 𝒪_{X,x}` of `θ` is a proper ideal, then `D a` vanishes at `x` for every local
function `a`, and in particular `D` preserves the ideal of `x`. -/
theorem fixes_of_not_surjective (D : SheafDerivationOf g) (x : X) (hx : IsClosed ({x} : Set X))
    (h : ¬ Function.Surjective (mapFun D.differentialsHom x)) : D.Fixes x hx := by
  rw [fixes_iff_basicOpen]
  intro V s _ hmem
  have hxV : x ∈ (V : X.Opens) := X.basicOpen_le _ hmem
  obtain ⟨c, hc⟩ := (X.mem_basicOpen _ x hxV).mp hmem
  apply h
  intro b
  obtain ⟨r, rfl⟩ := (Stacks.UnitStalk.unitStalkLinearEquiv X x).surjective b
  refine ⟨(r * ↑c⁻¹) • (Scheme.Modules.presheaf (Scheme.Hom.relativeDifferentials g)).germ
    (V : X.Opens) x hxV ((Scheme.Hom.universalRelativeDerivation g).d (X := op (V : X.Opens)) s),
    ?_⟩
  rw [mapFun_smul, mapFun_differentialsHom_germ, ← map_smul, ← hc, smul_eq_mul, mul_assoc,
    Units.inv_mul, mul_one]

/-- **A vector field fixing a closed point kills the residue of every local function there**,
over an algebraically closed field: if `D` fixes the closed point `x`, then `D a` vanishes at `x`
for every local function `a` near `x`. The residue field at `x` is `k`, so `a - c` vanishes at
`x` for a constant `c`, and `D a = D (a - c)` vanishes at `x` because `D` preserves the ideal of
`x`. -/
theorem germ_onSections_mem_maximalIdeal_of_fixes [IsAlgClosed k] [LocallyOfFiniteType g]
    (D : SheafDerivationOf g) (x : X) (hx : IsClosed ({x} : Set X)) (hfix : D.Fixes x hx)
    (U : X.Opens) (hxU : x ∈ U) (a : Γ(X, U)) :
    (X.presheaf.germ U x hxU).hom (D.onSections a) ∈ maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
  have hVU' : V ≤ U := hVU
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.Γevaluation x).hom.toAlgebra
  obtain ⟨c, hc⟩ := (bijective_algebraMap_residueField_of_isClosed g x hx).2
    (X.evaluation U x hxU a)
  let b : Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom c
  let res : Γ(X, U) ⟶ Γ(X, V) := X.presheaf.map (homOfLE hVU').op
  let resb : Γ(X, ⊤) ⟶ Γ(X, V) := X.presheaf.map (homOfLE le_top).op
  have hb : D.onSections (resb.hom b) = 0 := by
    rw [onSections_restrict, show D.onSections b = 0 from onSections_app D ⊤ _, map_zero]
  have heval : X.evaluation V x hxV (res.hom a - resb.hom b) = 0 := by
    rw [map_sub, sub_eq_zero]
    show (X.presheaf.germ V x hxV ≫ X.residue x).hom (res.hom a) =
      (X.presheaf.germ V x hxV ≫ X.residue x).hom (resb.hom b)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.germ_residue, Scheme.germ_residue]
    exact hc.symm
  have hres := (fixes_iff_basicOpen D x hx).mp hfix ⟨V, hV⟩ (res.hom a - resb.hom b)
    ((X.evaluation_eq_zero_iff_notMem_basicOpen x hxV _).mp heval)
  have hsub : D.onSections (res.hom a - resb.hom b) =
      D.onSections (res.hom a) - D.onSections (resb.hom b) := map_sub _ _ _
  rwa [hsub, hb, sub_zero, onSections_restrict, X.mem_basicOpen _ x hxV,
    TopCat.Presheaf.germ_res_apply] at hres

/-- **A vector field fixing a closed point has `θ` vanishing there**, over an algebraically
closed field: the image of the stalk `Ω_{X/k, x} ⟶ 𝒪_{X,x}` of `θ` lies in the maximal ideal.
The module `Ω_{X/k, x} = Ω_{𝒪_{X,x}/k}` is generated by the differentials `d a` of local
functions, and `θ (d a) = D a` vanishes at `x`
(`Stacks.Curves.SheafDerivationOf.germ_onSections_mem_maximalIdeal_of_fixes`). -/
theorem not_surjective_of_fixes [IsAlgClosed k] [LocallyOfFiniteType g]
    (D : SheafDerivationOf g) (x : X) (hx : IsClosed ({x} : Set X)) (hfix : D.Fixes x hx) :
    ¬ Function.Surjective (mapFun D.differentialsHom x) := by
  let : Algebra k (X.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra
  obtain ⟨E, hE⟩ := exists_relativeDifferentialStalk_kaehlerEquiv g x
  let ψ : TopCat.Presheaf.stalk (C := Ab.{u})
      (Scheme.Modules.presheaf (Scheme.Hom.relativeDifferentials g)) x →ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x :=
    (Stacks.UnitStalk.unitStalkLinearEquiv X x).symm.toLinearMap ∘ₗ map D.differentialsHom x
  have hψ : ∀ ω, ψ ω ∈ maximalIdeal (X.presheaf.stalk x) := by
    have htop : Submodule.span (X.presheaf.stalk x)
        (Set.range (KaehlerDifferential.D k (X.presheaf.stalk x))) ≤
        Submodule.comap (ψ ∘ₗ E.symm.toLinearMap) (maximalIdeal (X.presheaf.stalk x)) := by
      rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
      rw [SetLike.mem_coe, Submodule.mem_comap, ← hE U hxU a]
      have key : ψ (((Scheme.Modules.presheaf (Scheme.Hom.relativeDifferentials g)).germ U x
          hxU).hom ((Scheme.Hom.universalRelativeDerivation g).d (X := op U) a)) ∈
          maximalIdeal (X.presheaf.stalk x) := by
        show (Stacks.UnitStalk.unitStalkLinearEquiv X x).symm (mapFun D.differentialsHom x _) ∈ _
        rw [mapFun_differentialsHom_germ, LinearEquiv.symm_apply_apply]
        exact germ_onSections_mem_maximalIdeal_of_fixes D x hx hfix U hxU a
      exact (congrArg (· ∈ maximalIdeal (X.presheaf.stalk x))
        (congrArg ψ (E.symm_apply_apply _))).mpr key
    rw [KaehlerDifferential.span_range_derivation] at htop
    intro ω
    exact (congrArg (· ∈ maximalIdeal (X.presheaf.stalk x))
      (congrArg ψ (E.symm_apply_apply ω))).mp (htop (Submodule.mem_top (x := E ω)))
  intro hsurj
  obtain ⟨ω, hω⟩ := hsurj (Stacks.UnitStalk.unitStalkLinearEquiv X x 1)
  have h1 : ψ ω = 1 := by
    show (Stacks.UnitStalk.unitStalkLinearEquiv X x).symm (mapFun D.differentialsHom x ω) = 1
    rw [hω, LinearEquiv.symm_apply_apply]
  exact (maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
    ((Ideal.eq_top_iff_one _).mpr (h1 ▸ hψ ω))

/-- **The points fixed by a vector field lie in the support of the cokernel of `θ`**, over an
algebraically closed field: at such a point the stalk of `θ` is not surjective. -/
theorem mem_supp_cokernel_of_fixes [IsAlgClosed k] [LocallyOfFiniteType g]
    (D : SheafDerivationOf g) (x : X) (hx : IsClosed ({x} : Set X)) (hfix : D.Fixes x hx) :
    x ∈ SheafOfModules.supp (cokernel D.differentialsHom) :=
  (mem_supp_cokernel_iff_not_surjective _ x).mpr (not_surjective_of_fixes D x hx hfix)

/-! ### Restriction along an open immersion -/

section Restrict

variable (D : SheafDerivationOf g) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The value on a section of `𝒪_U` over `W` of a vector field restricted along an open immersion
`j : U ⟶ X`: transport the section to `j(W)`, apply `D` there, and transport back. -/
def restrictOpensSection {W : U.Opens} (a : Γ(U, W)) : Γ(U, W) :=
  (j.appIso W).hom.hom (D.onSections ((j.appIso W).inv.hom a))

/-- The restricted vector field is additive on sections. -/
theorem restrictOpensSection_add {W : U.Opens} (a b : Γ(U, W)) :
    D.restrictOpensSection j (a + b) =
      D.restrictOpensSection j a + D.restrictOpensSection j b := by
  simp only [restrictOpensSection, map_add, onSections_add]

/-- The restricted vector field satisfies the Leibniz rule `D (a * b) = a * D b + b * D a`. -/
theorem restrictOpensSection_mul {W : U.Opens} (a b : Γ(U, W)) :
    D.restrictOpensSection j (a * b) =
      a * D.restrictOpensSection j b + b * D.restrictOpensSection j a := by
  simp only [restrictOpensSection, map_mul, onSections_mul, map_add, Iso.inv_hom_id_apply]

/-- The restricted vector field vanishes on the section `1`. -/
theorem restrictOpensSection_one (W : U.Opens) :
    D.restrictOpensSection j (1 : Γ(U, W)) = 0 := by
  simp only [restrictOpensSection, map_one, onSections_one, map_zero]

/-- The restricted vector field commutes with the restriction maps of `𝒪_U`. -/
theorem restrictOpensSection_map {W W' : U.Opens} (f : op W ⟶ op W')
    (a : Γ(U, W)) :
    D.restrictOpensSection j ((U.presheaf.map f).hom a) =
      (U.presheaf.map f).hom (D.restrictOpensSection j a) := by
  have h1 := congrArg (fun φ => φ.hom a) (j.appIso_inv_naturality f)
  have h2 := congrArg (fun φ => φ.hom (D.onSections ((j.appIso W).inv.hom a)))
    (j.appIso_hom_naturality f)
  simp only [CommRingCat.comp_apply] at h1 h2
  simp only [restrictOpensSection, h1, ← h2]
  congr 1
  exact D.d_map (j.opensFunctor.op.map f) _

/-- The data of a vector field restricted along an open immersion, as a derivation relative to the
constant presheaf of integers. -/
def restrictOpensData : (SheafOfModules.unit U.ringCatSheaf).val.Derivation'
    (AlgebraicGeometry.SheafOfModules.constIntMap U.presheaf) where
  d {W} := AddMonoidHom.mk' (fun a => D.restrictOpensSection j (W := W.unop) a)
    (D.restrictOpensSection_add j)
  d_mul {W} a b := D.restrictOpensSection_mul j (W := W.unop) a b
  d_map {_W _W'} f a := D.restrictOpensSection_map j f a
  d_app {W} a :=
    AlgebraicGeometry.SheafOfModules.constIntMap_app_eq_zero
      (AddMonoidHom.mk' (fun a => D.restrictOpensSection j (W := W.unop) a)
        (D.restrictOpensSection_add j))
      (D.restrictOpensSection_one j W.unop) a

/-- The restricted vector field on a section pulled back along `j` is the transport of the
restriction of `D a` to `j(j⁻¹ W)`. -/
private theorem restrictOpensSection_app_apply {W : X.Opens} (a : Γ(X, W))
    (hle : j ''ᵁ j ⁻¹ᵁ W ≤ W) :
    D.restrictOpensSection j ((j.app W).hom a) =
      (j.appIso (j ⁻¹ᵁ W)).hom.hom ((X.presheaf.map (homOfLE hle).op).hom (D.onSections a)) := by
  have h1 : (j.appIso (j ⁻¹ᵁ W)).inv.hom ((j.app W).hom a) =
      (X.presheaf.map (homOfLE hle).op).hom a :=
    congrArg (fun φ => CommRingCat.Hom.hom φ a) (j.app_appIso_inv W)
  rw [restrictOpensSection, h1, onSections_map]

/-- The restricted vector field vanishes on functions pulled back from `Spec k` along `j ≫ g`. -/
theorem restrictOpensSection_app (W : (Spec (.of k)).Opens) (b : Γ(Spec (.of k), W)) :
    D.restrictOpensSection j (((j ≫ g).app W).hom b) = 0 := by
  have hle : j ''ᵁ j ⁻¹ᵁ (g ⁻¹ᵁ W) ≤ g ⁻¹ᵁ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  exact (D.restrictOpensSection_app_apply j ((g.app W).hom b) hle).trans
    (by rw [onSections_app, map_zero, map_zero]; rfl)

/-- **The restriction of a vector field along an open immersion.** -/
def restrictOpens : SheafDerivationOf (j ≫ g) :=
  AlgebraicGeometry.SheafOfModules.ofComorphism (j ≫ g) (D.restrictOpensData j)
    (D.restrictOpensSection_app j)

/-- The restriction of `D` along `j` acts on a section of `𝒪_U` by
`Stacks.Curves.SheafDerivationOf.restrictOpensSection`. -/
@[simp] theorem restrictOpens_onSections {W : U.Opens} (a : Γ(U, W)) :
    (D.restrictOpens j).onSections a = D.restrictOpensSection j a := rfl

/-- A point of `U` lies in the non-vanishing locus of a section exactly when its
image in `X` lies in the non-vanishing locus of the corresponding section of `𝒪_X`. -/
theorem mem_basicOpen_iff_mem_basicOpen_image {V : U.Opens} (t : Γ(U, V))
    (z : U) :
    z ∈ U.basicOpen t ↔ j z ∈ X.basicOpen ((j.appIso V).inv.hom t) := by
  rw [← Scheme.image_basicOpen j t]
  exact ⟨fun h => ⟨z, h, rfl⟩, fun ⟨w, hw, hwz⟩ => j.isOpenEmbedding.injective hwz ▸ hw⟩

/-- **A vector field fixing the image of a point of `U` restricts to one fixing it.** -/
theorem fixes_restrictOpens (z : U) (hz : IsClosed ({z} : Set U))
    (hy : IsClosed ({j z} : Set X)) (hfix : D.Fixes (j z) hy) :
    (D.restrictOpens j).Fixes z hz := by
  rw [fixes_iff_basicOpen] at hfix ⊢
  intro V s hs
  rw [mem_basicOpen_iff_mem_basicOpen_image j] at hs ⊢
  simpa only [restrictOpens_onSections, restrictOpensSection, Iso.hom_inv_id_apply] using
    hfix ⟨j ''ᵁ V, V.2.image_of_isOpenImmersion j⟩ _ hs

/-- **A vector field vanishing on every member of an open cover is zero.** -/
theorem eq_zero_of_restrictOpens_eq_zero {ι : Type*} {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (h : ∀ i, D.restrictOpens (j i) = 0) : D = 0 := by
  refine ext' fun W a => ?_
  show D.onSections a = 0
  refine TopCat.Presheaf.section_ext X.sheaf W (D.onSections a) 0 fun x hx => ?_
  obtain ⟨i, y, rfl⟩ := hcov x
  have hle : j i ''ᵁ j i ⁻¹ᵁ W ≤ W := Set.image_preimage_subset _ _
  have h0 := congrArg (fun E : SheafDerivationOf (j i ≫ g) => E.onSections (((j i).app W).hom a))
    (h i)
  simp only [restrictOpens_onSections, zero_onSections,
    D.restrictOpensSection_app_apply (j i) a hle] at h0
  have h2 := congrArg ((j i).appIso (j i ⁻¹ᵁ W)).inv.hom h0
  rw [Iso.hom_inv_id_apply, map_zero] at h2
  have h4 : (X.presheaf.germ W (j i y) hx).hom (D.onSections a) = 0 := by
    rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) (j i y) ⟨y, hx, rfl⟩, h2,
      map_zero]
  exact h4.trans (map_zero _).symm

end Restrict

end SheafDerivationOf

/-! ### Smooth curves -/

section SmoothCurve

variable (g)

/-- **A smooth curve over a field is smooth of relative dimension one**: its fibre over the
unique point of `Spec k` is the whole curve, of dimension one at every point. -/
theorem smoothOfRelativeDimension_one_of_isCurve [IsCurve k g] [Smooth g] :
    SmoothOfRelativeDimension 1 g := by
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq g 1 fun x => ?_
  have heq : (g ⁻¹' {g x}) = (Set.univ : Set X) :=
    Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  let e : g.fiber (g x) ≃ₜ X :=
    (g.fiberHomeo (g x)).trans ((Homeomorph.setCongr heq).trans (Homeomorph.Set.univ X))
  rw [topologicalKrullDimAt_eq_of_homeomorph e,
    ← AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X g]
  exact_mod_cast IsCurve.topologicalKrullDim_eq_one g

/-- **The sheaf of differentials of a smooth curve is invertible.** -/
instance isInvertible_relativeDifferentials_of_isCurve [IsCurve k g] [Smooth g] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Hom.relativeDifferentials g) :=
  haveI := smoothOfRelativeDimension_one_of_isCurve g
  Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one X _
    (Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials g)

/-- A curve has dimension at most one. -/
theorem topologicalKrullDim_le_one_of_isCurve [IsCurve k g] : topologicalKrullDim X ≤ 1 :=
  (IsCurve.topologicalKrullDim_eq_one g).le

/-- **The normalization of a curve over an algebraically closed field is a smooth curve**: it is
a normal curve, hence regular, and regular schemes of finite type over a perfect field are
smooth. -/
@[ega "II 7.4.6" "partial"]
theorem smooth_normalizationOverField_of_isCurve [IsAlgClosed k] [IsCurve k g] :
    Smooth (normalizationOverField k g ≫ g) := by
  have hC := isCurve_normalizationOverField_comp k g
  have : LocallyOfFiniteType (normalizationOverField k g ≫ g) := hC.toLocallyOfFiniteType
  have : IsLocallyNoetherian (normalizationSchemeOverField k g) :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizationOverField k g ≫ g)
  have : IsNormal (normalizationSchemeOverField k g) :=
    Scheme.isNormal_normalizationScheme X (finite_irreducibleComponents_of_locallyOfFiniteType k g)
  exact smooth_of_isRegular_over_perfectField _
    (isRegular_of_isNormal_of_topologicalKrullDim_le_one _
      (topologicalKrullDim_le_one_of_isCurve (normalizationOverField k g ≫ g)))

variable {g}

/-- **A nonzero vector field on a smooth proper curve over an algebraically closed field fixes at
most `-deg(Ω_{X/k})` closed points**, and in particular `deg(Ω_{X/k}) ≤ 0`. The fixed points lie
in the support of the cokernel of `θ : Ω_{X/k} ⟶ 𝒪_X`, which has at most `-deg(Ω_{X/k})` points
(`AlgebraicGeometry.encard_supp_cokernel_toUnit_le`). -/
theorem SheafDerivationOf.encard_setOf_fixes_le [IsAlgClosed k] [IsCurve k g] [Smooth g]
    [IsProper g] (D : SheafDerivationOf g) (hD : D ≠ 0) :
    0 ≤ -invertibleCurveDegree k g (topologicalKrullDim_le_one_of_isCurve g)
        (Scheme.Hom.relativeDifferentials g) ∧
      {x : X | ∃ hx : IsClosed ({x} : Set X), D.Fixes x hx}.encard ≤
        ((-invertibleCurveDegree k g (topologicalKrullDim_le_one_of_isCurve g)
          (Scheme.Hom.relativeDifferentials g)).toNat : ℕ∞) := by
  obtain ⟨h0, h1⟩ := encard_supp_cokernel_toUnit_le k g (topologicalKrullDim_le_one_of_isCurve g)
    D.differentialsHom (SheafDerivationOf.differentialsHom_ne_zero hD)
  exact ⟨h0, le_trans (Set.encard_le_encard fun x ⟨hcl, hfix⟩ =>
    D.mem_supp_cokernel_of_fixes x hcl hfix) h1⟩

end SmoothCurve


end Stacks.Curves

end
