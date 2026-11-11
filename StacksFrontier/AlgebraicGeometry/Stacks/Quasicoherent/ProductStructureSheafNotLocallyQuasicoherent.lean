module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianLargeSections
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.IrreducibleOpenSubobject
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# A countable product of structure sheaves which is not locally quasi-coherent

Let `k` be a nontrivial commutative ring and `S = Spec k[x]`. On the algebraic stack of `S`
itself, the countable product `∏_{n ∈ ℕ} 𝒪` of copies of the structure sheaf, formed among the
sheaves of modules on the fppf site with sections in the universe `u + 1`, is not locally
quasi-coherent in the sense of Stacks 06WJ. In particular it does not belong to
`LQCoh^fbc(𝒪)`.

The argument is the classical one. Sections of a product of sheaves are products of sections,
so over an object `U` of the site the product has sections `∏_n 𝒪(U)`. Suppose the restriction
to the small étale site of `S` were quasi-coherent. A quasi-coherent module `𝒢` on the small
étale site of an affine scheme is cartesian between affine objects: for the open immersion
`D(x) ⟶ S` the comparison `𝒪(D(x)) ⊗_{𝒪(S)} 𝒢(S) ⟶ 𝒢(D(x))` is bijective. As
`𝒪(D(x)) = k[x]_x`, every section over `D(x)` becomes, after multiplication by a single power
`x^n`, the restriction of a global section. The section `(x^{-m})_m` of the product over `D(x)`
is not of this form: its coordinate `m = n + 1` would give `x^{-1} ∈ k[x]`, and in the
localization this means `x^j = x^{j + 1} b` for some `j` and `b`, which fails in `k[x]`.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleToFibred`: the functor from the small étale site of the
  scheme below an object `x` of a category fibred in groupoids to that category.

## Main results

* `Polynomial.pow_X_mul_one_sub_mul_ne_zero`: over a nontrivial ring, `x^j (1 - x b) ≠ 0` in
  `k[x]`.
* `Stacks.PresheafOfModules.exists_pow_smul_eq_map_of_surjective_restrictionBaseChange`: when
  the base-change comparison of a restriction map is surjective and the target ring is a
  localization away from an element `t`, every section over the target becomes the restriction
  of a section after multiplication by a power of `t`.
* `AlgebraicGeometry.Stack.not_isLocallyQuasicoherent_of_isLimit`: a product of countably many
  copies of the structure sheaf, with sections raised to the universe `u + 1`, is not locally
  quasi-coherent as soon as some object lies over an affine scheme with a function `r` for which
  no equation `r^j = r^{j + 1} b` holds.
* `AlgebraicGeometry.Stack.not_isLocallyQuasicoherent_pi_uliftUnit_polynomial`: the product
  `∏_ℕ 𝒪` on the algebraic stack of `Spec k[x]` is not locally quasi-coherent.
* `AlgebraicGeometry.Stack.not_mem_locallyQuasicoherentFlatBaseChange_of_iso_pi`: no module
  isomorphic to that product belongs to `LQCoh^fbc(𝒪)` at the module universe `u + 1`.

## Implementation notes

The modules live in the universe `u + 1` while the structure ring lives in `u`, so the copies
of the structure sheaf are `Stacks.SheafOfModules.uliftUnit`, the structure sheaf with its
sections raised to `u + 1`.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ v₁ r m u v w

namespace Polynomial

/-- In `k[x]` over a nontrivial ring no equation `x^j = x^{j+1} b` holds: the coefficient of
`x^j` in `x^j (1 - x b)` is `1`. -/
theorem pow_X_mul_one_sub_mul_ne_zero {k : Type u} [CommRing k] [Nontrivial k] (j : ℕ)
    (b : Polynomial k) :
    (Polynomial.X : Polynomial k) ^ j * (1 - Polynomial.X * b) ≠ 0 := by
  intro hzero
  have hcomm : (1 - Polynomial.X * b) * (Polynomial.X : Polynomial k) ^ j = 0 := by
    rw [mul_comm]; exact hzero
  have hcoeff : ((1 - Polynomial.X * b) * (Polynomial.X : Polynomial k) ^ j).coeff (0 + j) =
      (1 - Polynomial.X * b).coeff 0 :=
    Polynomial.coeff_mul_X_pow _ _ _
  have hone : (1 - Polynomial.X * b).coeff 0 = (1 : k) := by
    simp [Polynomial.coeff_sub, Polynomial.mul_coeff_zero]
  rw [hcomm, Polynomial.coeff_zero, hone] at hcoeff
  exact zero_ne_one hcoeff

end Polynomial

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- When the base-change comparison `R Y ⊗[R X] M X ⟶ M Y` of a restriction map is surjective
and every element of `R Y` becomes the image of an element of `R X` after multiplication by a
power of the image of `t`, every section of `M` over `Y` becomes the restriction of a section
over `X` after multiplication by a single power of the image of `t`. -/
theorem exists_pow_smul_eq_map_of_surjective_restrictionBaseChange
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (hf : Function.Surjective (restrictionBaseChange M f))
    (t : R.obj X)
    (ht : ∀ a : R.obj Y, ∃ (b : R.obj X) (n : ℕ), a * (R.map f).hom t ^ n = (R.map f).hom b)
    (s : M.obj Y) :
    ∃ (n : ℕ) (y : M.obj X), ((R.map f).hom t) ^ n • s = M.map f y := by
  let ρ : M.obj X → M.obj Y := fun y => M.map f y
  have hρadd : ∀ y₁ y₂ : M.obj X, ρ (y₁ + y₂) = ρ y₁ + ρ y₂ := fun y₁ y₂ =>
    map_add (M.map f).hom y₁ y₂
  have hρsmul : ∀ (c : R.obj X) (y : M.obj X), ρ (c • y) = (R.map f).hom c • ρ y := fun c y =>
    PresheafOfModules.map_smul M f c y
  let P : M.obj Y → Prop := fun s => ∃ (n : ℕ) (y : M.obj X), ((R.map f).hom t) ^ n • s = ρ y
  have hP0 : P 0 := ⟨0, 0, by rw [smul_zero]; exact (map_zero (M.map f).hom).symm⟩
  have hPadd : ∀ s₁ s₂, P s₁ → P s₂ → P (s₁ + s₂) := by
    rintro s₁ s₂ ⟨n₁, y₁, h₁⟩ ⟨n₂, y₂, h₂⟩
    refine ⟨n₁ + n₂, t ^ n₂ • y₁ + t ^ n₁ • y₂, ?_⟩
    rw [hρadd, hρsmul, hρsmul, map_pow, map_pow, ← h₁, ← h₂, smul_add, smul_smul, smul_smul,
      ← pow_add, ← pow_add, add_comm n₂ n₁]
  have hPsmul : ∀ (a : R.obj Y) (s : M.obj Y), P s → P (a • s) := by
    rintro a s ⟨n, y, hy⟩
    obtain ⟨b, k, hb⟩ := ht a
    refine ⟨k + n, b • y, ?_⟩
    rw [hρsmul, ← hy, smul_smul, smul_smul, ← hb, pow_add]
    congr 1
    ring
  have hPρ : ∀ y : M.obj X, P (ρ y) := fun y => ⟨0, y, by rw [pow_zero, one_smul]⟩
  obtain ⟨z, rfl⟩ := hf s
  induction z using TensorProduct.induction_on with
  | zero => exact (congrArg P (map_zero (restrictionBaseChange M f).hom)).mpr hP0
  | tmul a y =>
    exact (congrArg P (restrictionBaseChange_tmul M f a y)).mpr (hPsmul a (ρ y) (hPρ y))
  | add z₁ z₂ h₁ h₂ =>
    exact (congrArg P (map_add (restrictionBaseChange M f).hom z₁ z₂)).mpr (hPadd _ _ h₁ h₂)

end Stacks.PresheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}}

/-- Sections of a product of sheaves of modules are products of sections: over each object, any
family of sections of the factors is the family of projections of one section of the
product. -/
theorem exists_app_eq_of_isLimit {ι : Type} {F : ι → SheafOfModules.{m} R}
    {c : Fan F} (hc : IsLimit c) (X : Cᵒᵖ) (a : ∀ j, (F j).val.obj X) :
    ∃ s : c.pt.val.obj X, ∀ j, (c.π.app ⟨j⟩).val.app X s = a j := by
  let G := SheafOfModules.evaluation R X ⋙ CategoryTheory.forget (ModuleCat (R.obj.obj X))
  let hc' := isLimitOfPreserves G hc
  let x : (Discrete.functor F ⋙ G).sections :=
    ⟨fun j => a j.as, by
      intro i j f
      have hij : i = j := Discrete.ext (Discrete.eq_of_hom f)
      subst hij
      rw [Subsingleton.elim f (𝟙 i), CategoryTheory.Functor.map_id]
      all_goals rfl⟩
  exact ⟨(Types.isLimitEquivSections hc').symm x, fun j =>
    Types.isLimitEquivSections_symm_apply hc' x ⟨j⟩⟩

end SheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor from the small étale site of the scheme `U` below an object `x` of a category
fibred in groupoids to that category: include the small étale site into the schemes over `U`,
transport along the localization equivalence of Stacks 06W0 and forget the map to `x`. This is
the functor along which `AlgebraicGeometry.Stack.restrictModuleToSmallEtale` restricts. -/
noncomputable def smallEtaleToFibred {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) ⥤ 𝒳 :=
  letI _ := isEquivalence_overPost B S hS p hp x
  smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x

/-- **A product of copies of the structure sheaf is not locally quasi-coherent**, presheaf
form. Let `F` be a presheaf of modules on a category fibred in groupoids with maps `π j` to the
structure sheaf with sections raised to `u + 1`, such that over every object every family of
sections of the target is the family of images of one section of `F`. If some object `x` lies
over an affine scheme with a function `r` admitting no equation `r^j (1 - r b) = 0`, then `F` is
not locally quasi-coherent: its restriction to the small étale site of the scheme below `x` is
not cartesian along the inclusion of the basic open `D(r)`. -/
theorem not_isLocallyQuasicoherent_of_forall_exists_app_eq {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (F : PresheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (π : ℕ → (F ⟶ (Stacks.SheafOfModules.uliftUnit.{u + 1}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))).val))
    (hπ : ∀ (z : 𝒳ᵒᵖ) (a : ℕ → (Stacks.SheafOfModules.uliftUnit.{u + 1}
      (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B))).val.obj z),
      ∃ s : F.obj z, ∀ j, (π j).app z s = a j)
    (x : 𝒳) (hx : IsAffine (p.obj x).left.1) (r : Γ((p.obj x).left.1, ⊤))
    (hr : ∀ (j : ℕ) (b : Γ((p.obj x).left.1, ⊤)), r ^ j * (1 - r * b) ≠ 0) :
    ¬ IsLocallyQuasicoherent B E h S hS p hp F := by
  intro hF
  have := hx
  obtain ⟨hM, hqc⟩ := hF.2 x
  -- the final object `X₀` of the small étale site and its basic open `Y₀ = D(r)`
  let X₀ : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) :=
    SmallEtale.final E (p.obj x).left.1 (contains_base B E h S hS p x)
  let W : ((p.obj x).left.1).Opens := ((p.obj x).left.1).basicOpen r
  have hW : E.Contains W.toScheme :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion W.ι) (contains_base B E h S hS p x)
  let Y₀ : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) :=
    SmallEtale.openObj X₀ W hW
  let ι₀ : Y₀ ⟶ X₀ := SmallEtale.openObjHom X₀ W hW
  have hX₀ : IsAffine ((SmallEtale.toScheme E _ (contains_base B E h S hS p x)).obj X₀) := hx
  have hY₀ : IsAffine ((SmallEtale.toScheme E _ (contains_base B E h S hS p x)).obj Y₀) :=
    (isAffineOpen_top ((p.obj x).left.1)).basicOpen r
  have hbij :=
    SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite_freeModuleUniverse.{u, 0}
      E (p.obj x).left.1 (contains_base B E h S hS p x) ⟨_, hM⟩ hqc hY₀ hX₀ ι₀
  -- the ring map `Γ(X₀) ⟶ Γ(Y₀)` is a localization away from `r`
  let φ := (SmallEtale.commStructurePresheaf E _ (contains_base B E h S hS p x)).map ι₀.op
  let r' : (SmallEtale.commStructurePresheaf E _ (contains_base B E h S hS p x)).obj (op X₀) := r
  have : IsLocalization.Away r Γ(W.toScheme, ⊤) := Γ_restrict_isLocalization _ r
  have ht : ∀ a : (SmallEtale.commStructurePresheaf E _ (contains_base B E h S hS p x)).obj
        (op Y₀),
      ∃ (b : (SmallEtale.commStructurePresheaf E _ (contains_base B E h S hS p x)).obj
        (op X₀)) (n : ℕ), a * φ.hom r' ^ n = φ.hom b := by
    intro a
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hb⟩ :=
      IsLocalization.surj (Submonoid.powers r) (S := Γ(W.toScheme, ⊤)) a
    refine ⟨b, n, ?_⟩
    rw [← map_pow]
    exact hb
  -- the restriction to the small étale site and the identification of structure sheaves
  let Rx := ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)
  let L := (Stacks.SheafOfModules.uliftUnit.{u + 1} Rx).val
  let q := smallEtaleToFibred B E h S hS p hp x
  let Φ : PresheafOfModules.{u + 1} Rx.obj ⥤ PresheafOfModules.{u + 1}
      (SmallEtale.structureSheaf E _ (contains_base B E h S hS p x)).obj :=
    restrictModuleToSmallEtaleFunctor B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) x
  let α := localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
    (etaleTopology_le_topology B)
  let ψ := ((SmallEtale.structureSheaf E _ (contains_base B E h S hS p x)).obj.map ι₀.op).hom
  let r'' : (SmallEtale.structureSheaf E _ (contains_base B E h S hS p x)).obj.obj (op X₀) := r
  let u' : (SmallEtale.structureSheaf E _ (contains_base B E h S hS p x)).obj.obj (op Y₀) :=
    ψ r''
  have hu : IsUnit u' := IsLocalization.Away.algebraMap_isUnit (S := Γ(W.toScheme, ⊤)) r
  have hv : IsUnit ((α.app (op Y₀)).hom u') := hu.map (α.app (op Y₀)).hom.hom
  let dY : (Φ.obj L).obj (op Y₀) →
      (restrictToSmallEtale B E h S hS p hp x Rx.obj).obj (op Y₀) := fun ℓ => ULift.down ℓ
  let dX : (Φ.obj L).obj (op X₀) →
      (restrictToSmallEtale B E h S hS p hp x Rx.obj).obj (op X₀) := fun ℓ => ULift.down ℓ
  -- the section `(r^{-j})_j` over `Y₀`, and a power of `r` carrying it to a restriction
  let wv : ℕ → (restrictToSmallEtale B E h S hS p hp x Rx.obj).obj (op Y₀) :=
    fun j => Units.val (hv.unit⁻¹ ^ j)
  obtain ⟨s₀, hs⟩ := hπ (op (q.obj Y₀)) fun j => ULift.up (wv j)
  let s : (Φ.obj F).obj (op Y₀) := s₀
  obtain ⟨n, y, hny⟩ :=
    Stacks.PresheafOfModules.exists_pow_smul_eq_map_of_surjective_restrictionBaseChange.{
        u + 1, u, u, u + 1}
      (R := SmallEtale.commStructurePresheaf E _ (contains_base B E h S hS p x))
      (Φ.obj F) ι₀.op hbij.2 r' ht s
  have key := congrArg (fun t => dY ((Φ.map (π (n + 1))).app (op Y₀) t)) hny
  obtain ⟨c, hc⟩ : ∃ c : (SmallEtale.structureSheaf E _ (contains_base B E h S hS p x)).obj.obj
      (op X₀), (α.app (op X₀)).hom c = dX ((Φ.map (π (n + 1))).app (op X₀) y) :=
    (α.app (op X₀)).ringCatIsoToRingEquiv.surjective _
  -- the coordinate `n + 1` of both sides
  have hs' : (Φ.map (π (n + 1))).app (op Y₀) s = ULift.up (wv (n + 1)) := hs (n + 1)
  have e1 : dY ((Φ.map (π (n + 1))).app (op Y₀) (u' ^ n • s)) =
      (α.app (op Y₀)).hom (u' ^ n) * wv (n + 1) := by
    rw [show (Φ.map (π (n + 1))).app (op Y₀) (u' ^ n • s) =
        u' ^ n • (Φ.map (π (n + 1))).app (op Y₀) s from
      map_smul ((Φ.map (π (n + 1))).app (op Y₀)).hom _ _]
    exact congrArg (fun ℓ => (α.app (op Y₀)).hom (u' ^ n) * dY ℓ) hs'
  have e2 : dY ((Φ.map (π (n + 1))).app (op Y₀) ((Φ.obj F).map ι₀.op y)) =
      (α.app (op Y₀)).hom (ψ c) := by
    rw [PresheafOfModules.naturality_apply]
    change (Rx.obj.map (q.map ι₀).op).hom (dX ((Φ.map (π (n + 1))).app (op X₀) y)) = _
    rw [← hc]
    exact (NatTrans.naturality_apply α.hom ι₀.op c).symm
  have e3 : (α.app (op Y₀)).hom (u' ^ n) * wv (n + 1) = Units.val hv.unit⁻¹ := by
    have hpow : (α.app (op Y₀)).hom (u' ^ n) = Units.val (hv.unit ^ n) := by
      rw [map_pow, Units.val_pow_eq_pow_val, hv.unit_spec]
    change (α.app (op Y₀)).hom (u' ^ n) * Units.val (hv.unit⁻¹ ^ (n + 1)) = _
    rw [hpow, ← Units.val_mul]
    congr 1
    group
  have hmain : (α.app (op Y₀)).hom (ψ c) = Units.val hv.unit⁻¹ :=
    calc (α.app (op Y₀)).hom (ψ c)
        = dY ((Φ.map (π (n + 1))).app (op Y₀) ((Φ.obj F).map ι₀.op y)) := e2.symm
      _ = dY ((Φ.map (π (n + 1))).app (op Y₀) (u' ^ n • s)) := key.symm
      _ = (α.app (op Y₀)).hom (u' ^ n) * wv (n + 1) := e1
      _ = Units.val hv.unit⁻¹ := e3
  -- hence `r c = 1` in `Γ(D(r))`, which forces `r^k (1 - r c) = 0`
  have hmul : (α.app (op Y₀)).hom (ψ (r'' * c)) = (α.app (op Y₀)).hom 1 := by
    rw [map_mul, map_mul, hmain, map_one]
    exact hv.mul_val_inv
  let c₀ : Γ((p.obj x).left.1, ⊤) := c
  have hφ1 : algebraMap Γ((p.obj x).left.1, ⊤) Γ(W.toScheme, ⊤) (r * c₀) =
      algebraMap Γ((p.obj x).left.1, ⊤) Γ(W.toScheme, ⊤) 1 := by
    rw [map_one]
    exact (α.app (op Y₀)).ringCatIsoToRingEquiv.injective hmul
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r) _).1 hφ1
  have hk' : r ^ k * (r * c₀) = r ^ k * 1 := hk
  exact hr k c₀ (by rw [mul_sub, hk', sub_self])

/-- **A product of copies of the structure sheaf is not locally quasi-coherent.** For any
topology `τ` coarser than the fppf topology, a product of countably many copies of the structure
sheaf of a category fibred in groupoids, with sections raised to the universe `u + 1`, is not
locally quasi-coherent as soon as some object lies over an affine scheme with a function `r`
admitting no equation `r^j (1 - r b) = 0`. -/
theorem not_isLocallyQuasicoherent_of_isLimit {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    {c : Fan fun _ : ℕ =>
      Stacks.SheafOfModules.uliftUnit.{u + 1} (ringStructureSheafCore B S hS p hp τ hτ)}
    (hc : IsLimit c) (x : 𝒳) (hx : IsAffine (p.obj x).left.1) (r : Γ((p.obj x).left.1, ⊤))
    (hr : ∀ (j : ℕ) (b : Γ((p.obj x).left.1, ⊤)), r ^ j * (1 - r * b) ≠ 0) :
    ¬ IsLocallyQuasicoherent B E h S hS p hp c.pt.val :=
  not_isLocallyQuasicoherent_of_forall_exists_app_eq B E h S hS p hp c.pt.val
    (fun j => (c.π.app ⟨j⟩).val) (fun z a => SheafOfModules.exists_app_eq_of_isLimit hc z a)
    x hx r hr

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- The coordinate function `x` on `Spec k[x]` admits no equation `x^j (1 - x b) = 0`. -/
theorem pow_mul_one_sub_mul_ne_zero_spec_polynomial {k : Type u} [CommRing k] [Nontrivial k]
    (j : ℕ) (b : Γ(Spec (CommRingCat.of (Polynomial k)), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X ^ j *
      (1 - (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X * b) ≠ 0 := by
  intro hzero
  apply Polynomial.pow_X_mul_one_sub_mul_ne_zero j
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).hom b)
  have := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).hom z) hzero
  simpa using this

/-- **The countable product of copies of the structure sheaf of the algebraic stack of
`Spec k[x]` is not locally quasi-coherent** (Stacks 06WJ), for `k` a nontrivial commutative
ring. The product is taken among the fppf modules with sections in the universe `u + 1`. This
is the degree zero cohomology sheaf of the derived pushforward in the counterexample of
Stacks 07DC. -/
theorem not_isLocallyQuasicoherent_pi_uliftUnit_polynomial (k : Type u) [CommRing k]
    [Nontrivial k] (hS : B.Contains (Spec (CommRingCat.of (Polynomial k)))) :
    ¬ IsLocallyQuasicoherent B E h _ hS
      (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))).val.val.p
      (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))).val.isFiberedInGroupoids
      (∏ᶜ fun _ : ℕ =>
        (Stacks.SheafOfModules.uliftUnit.{u + 1} _ :
          fppfModulesUnivLE.{u, w, u + 1} B _ hS
            (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))))).val :=
  not_isLocallyQuasicoherent_of_isLimit B E h _ hS
    (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))).val.val.p
    (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))).val.isFiberedInGroupoids
    (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf) (limit.isLimit _)
    (Over.mk (𝟙 (Over.mk (𝟙 (B.obj hS)))))
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial k)))))
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X)
    pow_mul_one_sub_mul_ne_zero_spec_polynomial

/-- **No fppf module isomorphic to the countable product of copies of the structure sheaf of
the algebraic stack of `Spec k[x]` lies in `LQCoh^fbc`**, at the module universe `u + 1`: it is
not even locally quasi-coherent. -/
theorem not_mem_locallyQuasicoherentFlatBaseChange_of_iso_pi (k : Type u) [CommRing k]
    [Nontrivial k] (hS : B.Contains (Spec (CommRingCat.of (Polynomial k))))
    (F : fppfModulesUnivLE.{u, w, u + 1} B _ hS
      (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))))
    (e : F ≅ ∏ᶜ fun _ : ℕ =>
      (Stacks.SheafOfModules.uliftUnit.{u + 1} _ :
          fppfModulesUnivLE.{u, w, u + 1} B _ hS
            (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))))) :
    ¬ locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, u + 1} B E h _ hS
      (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))) F := fun hF =>
  not_isLocallyQuasicoherent_of_isLimit B E h _ hS
    (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))).val.val.p
    (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))).val.isFiberedInGroupoids
    (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)
    (IsLimit.extendIso e.hom (limit.isLimit _))
    (Over.mk (𝟙 (Over.mk (𝟙 (B.obj hS)))))
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial k)))))
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X)
    pow_mul_one_sub_mul_ne_zero_spec_polynomial hF.1

end AlgebraicGeometry.Stack

end
