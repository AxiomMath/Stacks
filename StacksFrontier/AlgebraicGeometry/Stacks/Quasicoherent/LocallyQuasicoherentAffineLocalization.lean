module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RingedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty

/-!
# Sections of a locally quasi-coherent module on an affine scheme over a basic open

Let `S = Spec R` be an affine scheme in a big fppf site, and let `𝒴` be the algebraic stack
`(Sch/S)_{fppf}` itself (the scheme stack of the terminal object of the site over `S`). Its total
category has the terminal object `y₀ = (S, id)`, and every `r ∈ R` gives the object `y_r` for the
basic open `D(r) ⊆ S`, with its open immersion `ι_r : y_r ⟶ y₀`.

For a module `F` on the fppf site of `𝒴` which is locally quasi-coherent (Stacks 06WJ) with the
flat base change property, the sections `F(y_r)` are the localization of `F(y₀)` away from the
image `r₀` of `r` in the ring `𝒪(y₀) = Γ(S, 𝒪_S)`:

* `ρ_r r₀` is a unit of `𝒪(y_r)`, where `ρ_r : 𝒪(y₀) → 𝒪(y_r)` is restriction;
* every section over `y_r` becomes, after multiplication by a power of `ρ_r r₀`, the restriction
  of a section over `y₀`;
* a section over `y₀` restricting to zero over `y_r` is killed by a power of `r₀`.

## Main definitions

* `AlgebraicGeometry.Stack.affineSchemeStack`: the algebraic stack `(Sch/Spec R)_{fppf}`.
* `AlgebraicGeometry.Stack.affineSchemeStack.terminalObj`: its object `y₀`.
* `AlgebraicGeometry.Stack.affineSchemeStack.basicOpenObj`: the object `y_r` of `D(r)`, and
  `AlgebraicGeometry.Stack.affineSchemeStack.basicOpenι` the arrow `ι_r : y_r ⟶ y₀`.
* `AlgebraicGeometry.Stack.affineSchemeStack.sectionsRing`: the ring `𝒪(y)`, and
  `AlgebraicGeometry.Stack.affineSchemeStack.terminalSectionsRingEquiv` its identification with
  `R` at `y₀`.

## Main results

* `AlgebraicGeometry.Stack.affineSchemeStack.isLocalization_basicOpenRestriction`: `𝒪(y_r)` is
  the localization of `𝒪(y₀)` away from `r₀`.
* `AlgebraicGeometry.Stack.affineSchemeStack.isLocalizedModule_basicOpenRestriction`: for `F`
  in `LQCoh^fbc`, restriction `F(y₀) ⟶ F(y_r)` is the localization away from `r₀`.
* `AlgebraicGeometry.Stack.affineSchemeStack.exists_pow_smul_eq_map` and
  `AlgebraicGeometry.Stack.affineSchemeStack.exists_pow_smul_eq_zero_of_map_eq_zero`: the two
  halves of that localization, stated on elements.

## Implementation notes

Local quasi-coherence is read through
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange` (the
"(1) ⇔ (3)" of Stacks 0H0F): `ι_r` lies over the open immersion `D(r) → S` of affine schemes,
which is étale, so the base-change comparison `𝒪(y_r) ⊗_{𝒪(y₀)} F(y₀) ⟶ F(y_r)` is bijective.
Since `𝒪(y_r) = Γ(D(r), 𝒪)` is the localization away from `r₀` (Mathlib's
`AlgebraicGeometry.Γ_restrict_isLocalization`), base change along it is localization of modules
(`isLocalizedModule_iff_isBaseChange`). The flat base change part of the hypothesis is not used.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0H0F](https://stacks.math.columbia.edu/tag/0H0F)
* [Stacks Project, Tag 07DD](https://stacks.math.columbia.edu/tag/07DD)
-/

@[expose] public section

open CategoryTheory Opposite Stacks.PresheafOfModules

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (R : CommRingCat.{u}) (hS : B.Contains (Spec R))

/-- The algebraic stack `(Sch/Spec R)_{fppf}`: the scheme stack of the terminal object of the
big fppf site over `Spec R`. -/
noncomputable abbrev affineSchemeStack : AlgebraicStacks.{u, w} B (Spec R) hS :=
  schemeStack.{u, w} B (Spec R) hS (Over.mk (𝟙 (B.obj hS)))

namespace affineSchemeStack

/-- The terminal object `y₀ = (Spec R, id)` of the total category of
`AlgebraicGeometry.Stack.affineSchemeStack`. -/
noncomputable abbrev terminalObj : (affineSchemeStack.{u, w} B R hS).val.val.obj :=
  (Over.mk (𝟙 (Over.mk (𝟙 (B.obj hS)))) : Over (Over.mk (𝟙 (B.obj hS))))

/-- The global function on `Spec R` corresponding to an element `r` of `R`. -/
noncomputable abbrev globalElement (r : R) : Γ(Spec R, ⊤) :=
  (Scheme.ΓSpecIso R).inv.hom r

include hS in
/-- The basic open `D(r)` of `Spec R` is contained in the big fppf site. -/
theorem contains_basicOpen (r : R) :
    B.Contains ((Spec R).basicOpen (globalElement R r) : Scheme.{u}) :=
  BigFppfOver.contains_opens B hS _

/-- The object `y_r` of the total category of `AlgebraicGeometry.Stack.affineSchemeStack` given by
the basic open `D(r) ⊆ Spec R` with its open immersion. -/
noncomputable abbrev basicOpenObj (r : R) : (affineSchemeStack.{u, w} B R hS).val.val.obj :=
  (Over.mk (Over.homMk (BigFppfOver.opensObj B (Spec R) hS
      ((Spec R).basicOpen (globalElement R r))).hom :
      BigFppfOver.opensObj B (Spec R) hS ((Spec R).basicOpen (globalElement R r)) ⟶
        Over.mk (𝟙 (B.obj hS))) : Over (Over.mk (𝟙 (B.obj hS))))

/-- The arrow `ι_r : y_r ⟶ y₀` of the total category of
`AlgebraicGeometry.Stack.affineSchemeStack`, lying over the open immersion `D(r) → Spec R`. -/
noncomputable abbrev basicOpenι (r : R) :
    basicOpenObj.{u, w} B R hS r ⟶ terminalObj.{u, w} B R hS :=
  (Over.homMk (basicOpenObj.{u, w} B R hS r).hom :
    (basicOpenObj.{u, w} B R hS r : Over (Over.mk (𝟙 (B.obj hS)))) ⟶
      Over.mk (𝟙 (Over.mk (𝟙 (B.obj hS)))))

/-- The ring `𝒪(y)` of sections of the structure sheaf of
`AlgebraicGeometry.Stack.affineSchemeStack` at an object `y`: the global functions on the scheme
below `y`. Every module on the stack has its sections at `y` as a module over this ring. -/
noncomputable abbrev sectionsRing (y : (affineSchemeStack.{u, w} B R hS).val.val.obj) :
    CommRingCat.{u} :=
  (structureSheaf B (Spec R) hS (affineSchemeStack.{u, w} B R hS).val.val.p
    (affineSchemeStack.{u, w} B R hS).val.isFiberedInGroupoids (etaleTopology B)
    (etaleTopology_le_topology B)).obj.obj (op y)

/-- The ring `𝒪(y₀)` of the terminal object is `Γ(Spec R, 𝒪) ≅ R`. -/
noncomputable def terminalSectionsRingEquiv :
    sectionsRing.{u, w} B R hS (terminalObj.{u, w} B R hS) ≃+* R :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv

/-- The element `r₀ ∈ 𝒪(y₀)` corresponding to `r ∈ R`. -/
noncomputable abbrev terminalElement (r : R) :
    sectionsRing.{u, w} B R hS (terminalObj.{u, w} B R hS) :=
  globalElement R r

/-- `AlgebraicGeometry.Stack.affineSchemeStack.terminalElement` is the inverse of
`AlgebraicGeometry.Stack.affineSchemeStack.terminalSectionsRingEquiv` applied to `r`. -/
theorem terminalElement_eq (r : R) :
    terminalElement.{u, w} B R hS r = (terminalSectionsRingEquiv.{u, w} B R hS).symm r :=
  rfl

/-- The restriction `ρ_r : 𝒪(y₀) →+* 𝒪(y_r)` of the structure sheaf along `ι_r`. -/
noncomputable abbrev basicOpenRestriction (r : R) :
    sectionsRing.{u, w} B R hS (terminalObj.{u, w} B R hS) →+*
      sectionsRing.{u, w} B R hS (basicOpenObj.{u, w} B R hS r) :=
  ((structureSheaf B (Spec R) hS (affineSchemeStack.{u, w} B R hS).val.val.p
    (affineSchemeStack.{u, w} B R hS).val.isFiberedInGroupoids (etaleTopology B)
    (etaleTopology_le_topology B)).obj.map (basicOpenι.{u, w} B R hS r).op).hom

/-- **`𝒪(y_r)` is the localization of `𝒪(y₀)` away from `r₀`**, with restriction as the
structure map: Mathlib's `AlgebraicGeometry.Γ_restrict_isLocalization` for `Spec R`. -/
theorem isLocalization_basicOpenRestriction (r : R) :
    letI := (basicOpenRestriction.{u, w} B R hS r).toAlgebra
    IsLocalization.Away (terminalElement.{u, w} B R hS r)
      (sectionsRing.{u, w} B R hS (basicOpenObj.{u, w} B R hS r)) := by
  have halg : (basicOpenRestriction.{u, w} B R hS r).toAlgebra =
      ΓRestrictAlgebra ((Spec R).basicOpen (globalElement R r)) := rfl
  exact halg ▸ Γ_restrict_isLocalization (Spec R) (globalElement R r)

/-- A module on the fppf site of `AlgebraicGeometry.Stack.affineSchemeStack`, read as a presheaf
of modules over the commutative structure presheaf of Stacks 06TV. This is `F.val` itself: the
two presheaves of rings agree definitionally, and this reading puts the sections `F(y)` over the
commutative rings `AlgebraicGeometry.Stack.affineSchemeStack.sectionsRing`. -/
noncomputable abbrev etaleStructureModule
    (F : fppfModules B (Spec R) hS (affineSchemeStack.{u, w} B R hS)) :
    PresheafOfModules.{u} ((structureSheaf B (Spec R) hS
      (affineSchemeStack.{u, w} B R hS).val.val.p
      (affineSchemeStack.{u, w} B R hS).val.isFiberedInGroupoids (etaleTopology B)
      (etaleTopology_le_topology B)).obj ⋙ forget₂ CommRingCat RingCat) :=
  F.val

/-- **(L0)** `ρ_r r₀` is a unit of `𝒪(y_r)`. -/
theorem isUnit_basicOpenRestriction (r : R) :
    IsUnit (basicOpenRestriction.{u, w} B R hS r (terminalElement.{u, w} B R hS r)) := by
  let := (basicOpenRestriction.{u, w} B R hS r).toAlgebra
  have := isLocalization_basicOpenRestriction.{u, w} B R hS r
  exact IsLocalization.map_units
    (sectionsRing.{u, w} B R hS (basicOpenObj.{u, w} B R hS r))
    (⟨terminalElement.{u, w} B R hS r, 1, pow_one _⟩ :
      Submonoid.powers (terminalElement.{u, w} B R hS r))

/-- **(L3)** Restriction of sections of a module along `ι_r` is semilinear over `ρ_r`. -/
theorem map_basicOpenι_smul (F : fppfModules B (Spec R) hS (affineSchemeStack.{u, w} B R hS))
    (r : R) (a : sectionsRing.{u, w} B R hS (terminalObj.{u, w} B R hS))
    (m : (etaleStructureModule.{u, w} B R hS F).obj (op (terminalObj.{u, w} B R hS))) :
    (etaleStructureModule.{u, w} B R hS F).map (basicOpenι.{u, w} B R hS r).op (a • m) =
      basicOpenRestriction.{u, w} B R hS r a •
        (etaleStructureModule.{u, w} B R hS F).map (basicOpenι.{u, w} B R hS r).op m :=
  (etaleStructureModule.{u, w} B R hS F).map_smul (basicOpenι.{u, w} B R hS r).op a m

/-- **A module in `LQCoh^fbc` is cartesian along `ι_r`**: the base-change comparison
`𝒪(y_r) ⊗_{𝒪(y₀)} F(y₀) ⟶ F(y_r)` is bijective. The arrow `ι_r` lies over the open immersion
`D(r) → Spec R` of affine schemes, which is étale, so this is local quasi-coherence read through
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange`. -/
theorem bijective_restrictionBaseChange_basicOpenι
    (F : fppfModules B (Spec R) hS (affineSchemeStack.{u, w} B R hS))
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h (Spec R) hS
      (affineSchemeStack.{u, w} B R hS) F) (r : R) :
    Function.Bijective (restrictionBaseChange.{u + 1, u, u, u}
      (R := (structureSheaf B (Spec R) hS (affineSchemeStack.{u, w} B R hS).val.val.p
        (affineSchemeStack.{u, w} B R hS).val.isFiberedInGroupoids (etaleTopology B)
        (etaleTopology_le_topology B)).obj) (etaleStructureModule.{u, w} B R hS F)
        (basicOpenι.{u, w} B R hS r).op) := by
  let G : SheafOfModules.{u} (ringStructureSheafCore B (Spec R) hS
      (affineSchemeStack.{u, w} B R hS).val.val.p
      (affineSchemeStack.{u, w} B R hS).val.isFiberedInGroupoids (etaleTopology B)
      (etaleTopology_le_topology B)) := ⟨F.val, hF.1.1⟩
  have hy : IsAffine ((BigFppfOver.toScheme B (Spec R) hS).obj
      ((affineSchemeStack.{u, w} B R hS).val.val.p.obj (basicOpenObj.{u, w} B R hS r))) :=
    (isAffineOpen_top (Spec R)).basicOpen (globalElement R r)
  have hy' : IsAffine ((BigFppfOver.toScheme B (Spec R) hS).obj
      ((affineSchemeStack.{u, w} B R hS).val.val.p.obj (terminalObj.{u, w} B R hS))) :=
    inferInstanceAs (IsAffine (Spec R))
  have het : Etale (((affineSchemeStack.{u, w} B R hS).val.val.p ⋙
      BigFppfOver.toScheme B (Spec R) hS).map (basicOpenι.{u, w} B R hS r)) :=
    inferInstanceAs (Etale ((Spec R).basicOpen (globalElement R r)).ι)
  have := (isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange B E h (Spec R) hS
    (affineSchemeStack.{u, w} B R hS).val.val.p
    (affineSchemeStack.{u, w} B R hS).val.isFiberedInGroupoids G).1 hF.1
    (basicOpenι.{u, w} B R hS r) hy hy' het
  exact ConcreteCategory.bijective_of_isIso _

section Localization

variable (F : fppfModules B (Spec R) hS (affineSchemeStack.{u, w} B R hS)) (r : R)

/-- The `𝒪(y₀)`-module structure on `F(y_r)` through restriction of scalars along `ρ_r`. -/
noncomputable abbrev basicOpenSectionsModule :
    Module (sectionsRing.{u, w} B R hS (terminalObj.{u, w} B R hS))
      ((etaleStructureModule.{u, w} B R hS F).obj (op (basicOpenObj.{u, w} B R hS r))) :=
  Module.compHom _ (basicOpenRestriction.{u, w} B R hS r)

/-- Restriction of sections `F(y₀) ⟶ F(y_r)` along `ι_r`, as a map of `𝒪(y₀)`-modules. -/
noncomputable def basicOpenRestrictionLinear :
    letI := basicOpenSectionsModule.{u, w} B R hS F r
    (etaleStructureModule.{u, w} B R hS F).obj (op (terminalObj.{u, w} B R hS)) →ₗ[
      sectionsRing.{u, w} B R hS (terminalObj.{u, w} B R hS)]
      (etaleStructureModule.{u, w} B R hS F).obj (op (basicOpenObj.{u, w} B R hS r)) :=
  letI := basicOpenSectionsModule.{u, w} B R hS F r
  { toFun := (etaleStructureModule.{u, w} B R hS F).map (basicOpenι.{u, w} B R hS r).op
    map_add' := fun x y =>
      ((etaleStructureModule.{u, w} B R hS F).map (basicOpenι.{u, w} B R hS r).op).hom.map_add x y
    map_smul' := map_basicOpenι_smul.{u, w} B R hS F r }

/-- `AlgebraicGeometry.Stack.affineSchemeStack.basicOpenRestrictionLinear` is restriction of
sections. -/
theorem basicOpenRestrictionLinear_apply
    (m : (etaleStructureModule.{u, w} B R hS F).obj (op (terminalObj.{u, w} B R hS))) :
    basicOpenRestrictionLinear.{u, w} B R hS F r m =
      (etaleStructureModule.{u, w} B R hS F).map (basicOpenι.{u, w} B R hS r).op m :=
  rfl

/-- **For `F` in `LQCoh^fbc`, the sections over `y_r` are the localization away from `r₀` of the
sections over `y₀`**, with restriction of sections as the structure map. -/
theorem isLocalizedModule_basicOpenRestriction
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h (Spec R) hS
      (affineSchemeStack.{u, w} B R hS) F) :
    letI := basicOpenSectionsModule.{u, w} B R hS F r
    IsLocalizedModule.Away (terminalElement.{u, w} B R hS r)
      (basicOpenRestrictionLinear.{u, w} B R hS F r) := by
  let := (basicOpenRestriction.{u, w} B R hS r).toAlgebra
  let := basicOpenSectionsModule.{u, w} B R hS F r
  have := isLocalization_basicOpenRestriction.{u, w} B R hS r
  have htow : IsScalarTower (sectionsRing.{u, w} B R hS (terminalObj.{u, w} B R hS))
      (sectionsRing.{u, w} B R hS (basicOpenObj.{u, w} B R hS r))
      ((etaleStructureModule.{u, w} B R hS F).obj (op (basicOpenObj.{u, w} B R hS r))) :=
    ⟨fun a b n => mul_smul (basicOpenRestriction.{u, w} B R hS r a) b n⟩
  refine (isLocalizedModule_iff_isBaseChange (Submonoid.powers (terminalElement.{u, w} B R hS r))
    (sectionsRing.{u, w} B R hS (basicOpenObj.{u, w} B R hS r))
    (basicOpenRestrictionLinear.{u, w} B R hS F r)).mpr
    (IsBaseChange.of_equiv (LinearEquiv.ofBijective
      (restrictionBaseChange.{u + 1, u, u, u}
        (R := (structureSheaf B (Spec R) hS (affineSchemeStack.{u, w} B R hS).val.val.p
          (affineSchemeStack.{u, w} B R hS).val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).obj) (etaleStructureModule.{u, w} B R hS F)
          (basicOpenι.{u, w} B R hS r).op).hom
      (bijective_restrictionBaseChange_basicOpenι.{u, w} B E h R hS F hF r)) fun m => ?_)
  exact restrictionBaseChange_one_tmul (etaleStructureModule.{u, w} B R hS F) _ m

/-- **(L1)** For `F` in `LQCoh^fbc`, every section over `y_r` becomes, after multiplication by a
power of `ρ_r r₀`, the restriction of a section over `y₀`. -/
theorem exists_pow_smul_eq_map
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h (Spec R) hS
      (affineSchemeStack.{u, w} B R hS) F)
    (m' : (etaleStructureModule.{u, w} B R hS F).obj (op (basicOpenObj.{u, w} B R hS r))) :
    ∃ (m : (etaleStructureModule.{u, w} B R hS F).obj (op (terminalObj.{u, w} B R hS))) (n : ℕ),
      basicOpenRestriction.{u, w} B R hS r (terminalElement.{u, w} B R hS r) ^ n • m' =
        (etaleStructureModule.{u, w} B R hS F).map (basicOpenι.{u, w} B R hS r).op m := by
  let := basicOpenSectionsModule.{u, w} B R hS F r
  have := isLocalizedModule_basicOpenRestriction.{u, w} B E h R hS F r hF
  obtain ⟨⟨m, ⟨_, n, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj
    (Submonoid.powers (terminalElement.{u, w} B R hS r))
    (basicOpenRestrictionLinear.{u, w} B R hS F r) m'
  refine ⟨m, n, ?_⟩
  rw [← map_pow]
  exact hm

/-- **(L2)** For `F` in `LQCoh^fbc`, a section over `y₀` whose restriction to `y_r` vanishes is
killed by a power of `r₀`. -/
theorem exists_pow_smul_eq_zero_of_map_eq_zero
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h (Spec R) hS
      (affineSchemeStack.{u, w} B R hS) F)
    (m : (etaleStructureModule.{u, w} B R hS F).obj (op (terminalObj.{u, w} B R hS)))
    (hm : (etaleStructureModule.{u, w} B R hS F).map (basicOpenι.{u, w} B R hS r).op m = 0) :
    ∃ N : ℕ, terminalElement.{u, w} B R hS r ^ N • m = 0 := by
  let := basicOpenSectionsModule.{u, w} B R hS F r
  have := isLocalizedModule_basicOpenRestriction.{u, w} B E h R hS F r hF
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalizedModule.eq_zero_iff
    (Submonoid.powers (terminalElement.{u, w} B R hS r))
    (basicOpenRestrictionLinear.{u, w} B R hS F r)).1 hm
  exact ⟨N, hN⟩

end Localization

section Polynomial

variable {k : Type u} [Field k] (hk : B.Contains (Spec (CommRingCat.of (Polynomial k))))

/-- For `R = k[X]`, the ring `𝒪(y₀)` is a domain. -/
theorem isDomain_sectionsRing_terminalObj_polynomial :
    IsDomain (sectionsRing.{u, w} B (CommRingCat.of (Polynomial k)) hk
      (terminalObj.{u, w} B (CommRingCat.of (Polynomial k)) hk)) :=
  Function.Injective.isDomain
    (terminalSectionsRingEquiv.{u, w} B (CommRingCat.of (Polynomial k)) hk).toRingHom
    (terminalSectionsRingEquiv.{u, w} B (CommRingCat.of (Polynomial k)) hk).injective

/-- For `R = k[X]` and `r = X`, the element `r₀ ∈ 𝒪(y₀)` is nonzero. -/
theorem terminalElement_X_ne_zero :
    terminalElement.{u, w} B (CommRingCat.of (Polynomial k)) hk
      (Polynomial.X : Polynomial k) ≠ 0 := by
  rw [terminalElement_eq, ne_eq, map_eq_zero_iff _ (RingEquiv.injective _)]
  exact Polynomial.X_ne_zero

/-- For `R = k[X]` and `r = X`, the element `r₀ ∈ 𝒪(y₀)` is not a unit. -/
theorem not_isUnit_terminalElement_X :
    ¬ IsUnit (terminalElement.{u, w} B (CommRingCat.of (Polynomial k)) hk
      (Polynomial.X : Polynomial k)) := by
  intro hu
  apply Polynomial.not_isUnit_X (R := k)
  simpa [terminalElement_eq] using
    hu.map (terminalSectionsRingEquiv.{u, w} B (CommRingCat.of (Polynomial k)) hk)

end Polynomial

end affineSchemeStack

end AlgebraicGeometry.Stack

end
