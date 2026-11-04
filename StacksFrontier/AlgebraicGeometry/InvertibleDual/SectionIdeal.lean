module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.ImageIdealSupport
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic

/-!
# The sheaf of ideals cut out by a section of an invertible module

Let `M` be an invertible `𝒪_X`-module on a scheme `X` and `s ∈ Γ(X, M)` a global section.
Evaluation at `s` is a morphism `M^∨ ⟶ 𝒪_X` out of the dual `M^∨ = SheafHom(M, 𝒪_X)`, and its
image is a quasi-coherent sheaf of ideals whose vanishing locus is the complement of the
nonvanishing locus `X_s`.  The dual is again invertible ([Stacks, Tag 01CT] (2)), hence finite
locally free, so this sheaf of ideals is a finite type quotient of a finite locally free module.
This is the sheaf of ideals with which the proof of [Stacks, Tag 0GMM] enters
[Stacks, Tag 0F89].

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.dual`: the dual `M^∨`, as an object of `X.Modules`.
* `AlgebraicGeometry.Scheme.Modules.evalGlobalHom`: evaluation at a global section,
  `M^∨ ⟶ 𝒪_X`.
* `AlgebraicGeometry.Scheme.Modules.trivializationDual`: the section of `M^∨` over `V` given by
  a sectionwise trivialization of `M` over `V`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_dual`: the dual of an invertible module
  is finite locally free.
* `AlgebraicGeometry.Scheme.Modules.coe_support_idealSheafDataOfHom_evalGlobalHom`: the vanishing
  locus of the image of evaluation at `s` is the complement of `X_s`.

## The argument

On an open `V` over which `M` is sectionwise trivial, write `s|_V = r · b` for the basis section
`b` (`Stacks.NonvanishingOpen.eq_triv_smul_basis`); a point `x ∈ V` lies in `X_s` exactly when
`r` is a unit at `x` (`Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit`).  The
trivialization is itself a section of `M^∨` over `V` whose value at `s` is `r`, so every point of
`X_s` lies outside the vanishing locus.  Conversely, if a local functional `λ` has `λ(s)` a unit
at `x`, then on a trivializing open around `x` the identity `λ(s) = r · λ(b)` makes `r` a unit
at `x`.

## References

* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0GMM](https://stacks.math.columbia.edu/tag/0GMM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/-- The dual `M^∨ = SheafHom(M, 𝒪_X)` of an `𝒪_X`-module, as an object of `X.Modules`. -/
noncomputable abbrev dual : X.Modules :=
  dualSheaf X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M

/-- Evaluation of a local section of `M^∨` over `U` at the restriction of a global section. -/
noncomputable def evalGlobal (s : Γ(M, ⊤)) {U : X.Opens} (lam : Γ(dual M, U)) : Γ(X, U) :=
  (lam.app (op (Over.mk (𝟙 U)))).hom (M.presheaf.map (homOfLE le_top).op s)

/-- Evaluation at a global section is additive in the functional. -/
theorem evalGlobal_add (s : Γ(M, ⊤)) {U : X.Opens} (lam mu : Γ(dual M, U)) :
    evalGlobal M s (lam + mu) = evalGlobal M s lam + evalGlobal M s mu := rfl

/-- Evaluation at a global section is linear in the functional. -/
theorem evalGlobal_smul (s : Γ(M, ⊤)) {U : X.Opens} (a : Γ(X, U)) (lam : Γ(dual M, U)) :
    evalGlobal M s (a • lam) = a * evalGlobal M s lam := by
  have h : evalGlobal M s (a • lam) = X.presheaf.map (𝟙 (op U)) a * evalGlobal M s lam := rfl
  rw [h, X.presheaf.map_id]
  rfl

/-- Evaluation at a global section commutes with restriction. -/
theorem evalGlobal_map (s : Γ(M, ⊤)) {U V : X.Opens} (hVU : V ≤ U) (lam : Γ(dual M, U)) :
    evalGlobal M s ((dual M).presheaf.map (homOfLE hVU).op lam) =
      X.presheaf.map (homOfLE hVU).op (evalGlobal M s lam) :=
  (congrArg (lam.app (op (Over.mk (homOfLE hVU)))).hom
    (M.presheaf.map_comp_apply (homOfLE (le_top : U ≤ ⊤)).op (homOfLE hVU).op s)).trans
    (internalHom_app_restrict X.presheaf M.val
      (SheafOfModules.unit (TensorSheafification.structureSheaf X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))).val U lam
      (op (Over.mk (homOfLE hVU))) (M.presheaf.map (homOfLE le_top).op s))

/-- **Evaluation at a global section, `M^∨ ⟶ 𝒪_X`.** On sections over `U` it sends a local
functional `λ` on `M|_U` to `λ(s|_U)`. -/
noncomputable def evalGlobalHom (s : Γ(M, ⊤)) : dual M ⟶ structureModule X where
  val :=
    { app U := ModuleCat.homAddEquiv.symm
        { toFun lam := evalGlobal M s (U := U.unop) lam
          map_add' lam mu := evalGlobal_add M s lam mu
          map_smul' a lam := evalGlobal_smul M s a lam }
      naturality {U V} i := by
        ext lam
        exact evalGlobal_map M s (leOfHom i.unop) lam }

/-- The components of `evalGlobalHom M s` are evaluation at `s`. -/
theorem structureAppₗ_evalGlobalHom [(dual M).IsQuasicoherent] (s : Γ(M, ⊤)) (U : X.Opens)
    (lam : Γ(dual M, U)) : structureAppₗ (evalGlobalHom M s) U lam = evalGlobal M s lam := rfl


/-- The value of a local section `lam` of `M^∨` over `U` on a local section `x` of `M` over `U`. -/
noncomputable def pairing {U : X.Opens} (lam : Γ(dual M, U)) (x : Γ(M, U)) : Γ(X, U) :=
  (lam.app (op (Over.mk (𝟙 U)))).hom x

/-- Evaluation at a global section is the pairing with its restriction. -/
theorem evalGlobal_eq_pairing (s : Γ(M, ⊤)) {U : X.Opens} (lam : Γ(dual M, U)) :
    evalGlobal M s lam = pairing M lam (M.presheaf.map (homOfLE le_top).op s) := rfl

/-- The pairing is linear in the section of `M`. -/
theorem pairing_smul_right {U : X.Opens} (lam : Γ(dual M, U)) (a : Γ(X, U)) (x : Γ(M, U)) :
    pairing M lam (a • x) = a * pairing M lam x :=
  (lam.app (op (Over.mk (𝟙 U)))).hom.map_smul a x

variable {M} in
/-- The morphism `M|_V ⟶ 𝒪_V` given by a sectionwise trivialization of `M` over `V`: at an open
`W ≤ V` it is the trivializing isomorphism `Γ(M, W) ≅ Γ(X, W)`. -/
noncomputable def trivializationDualHom {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) :
    (restrFun X.presheaf V).obj M.val ⟶
      (restrFun X.presheaf V).obj (SheafOfModules.unit (TensorSheafification.structureSheaf
        X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))).val where
  app W := ModuleCat.homAddEquiv.symm (t.θ W.unop.left W.unop.hom).toLinearMap
  naturality {W W'} g := by
    ext m
    exact t.θ_naturality W.unop.hom g.unop.left m

variable {M} in
/-- The section of `M^∨` over `V` given by a sectionwise trivialization of `M` over `V`. -/
noncomputable def trivializationDual {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) : Γ(dual M, V) :=
  trivializationDualHom t

/-- The value at a global section of the functional given by a trivialization is the
trivializing function of the section. -/
theorem evalGlobal_trivializationDual {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) (s : Γ(M, ⊤)) :
    evalGlobal M s (U := V) (trivializationDual t) = Stacks.NonvanishingOpen.trivTop t s := rfl

/-- The dual of an invertible module is invertible. -/
instance isInvertibleModule_dual [Stacks.Ample.IsInvertibleModule X M] :
    Stacks.Ample.IsInvertibleModule X (dual M) :=
  Invertible.isInvertible_dualSheaf X.presheaf _ M

/-- The dual of an invertible module is finite locally free. -/
theorem isFiniteLocallyFree_dual [Stacks.Ample.IsInvertibleModule X M] :
    SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (dual M) :=
  have := Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule X
    (dual M)
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (dual M) 1

/-- The dual of an invertible module is quasi-coherent. -/
instance isQuasicoherent_dual [Stacks.Ample.IsInvertibleModule X M] : (dual M).IsQuasicoherent :=
  have := isFiniteLocallyFree_dual M
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree (dual M)

/-- **The vanishing locus of the ideal cut out by a section of an invertible module.** For a
global section `s` of an invertible `𝒪_X`-module `M`, the image of evaluation at `s`,
`M^∨ ⟶ 𝒪_X`, vanishes exactly off the nonvanishing locus `X_s`. -/
theorem coe_support_idealSheafDataOfHom_evalGlobalHom [Stacks.Ample.IsInvertibleModule X M]
    (s : Γ(M, ⊤)) :
    ((idealSheafDataOfHom (dual M) (evalGlobalHom M s)).support : Set X) =
      (Stacks.Ample.nonvanishingLocus M s)ᶜ := by
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 M
  ext x
  rw [Set.mem_compl_iff, ← not_iff_not, not_not, SetLike.mem_coe,
    notMem_support_idealSheafDataOfHom_iff]
  obtain ⟨z, hz⟩ : ∃ z : X, x ∈ V z := Opens.mem_iSup.mp (hV ▸ Opens.mem_top x)
  obtain ⟨t⟩ := htriv z
  constructor
  · rintro ⟨W, lam, hx⟩
    have hxW : x ∈ W := X.basicOpen_le _ hx
    have hxW' : x ∈ W ⊓ V z := ⟨hxW, hz⟩
    let t' := t.comp (homOfLE inf_le_right : W ⊓ V z ⟶ V z)
    rw [Scheme.mem_basicOpen X _ x hxW, structureAppₗ_evalGlobalHom,
      ← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x hxW',
      ← evalGlobal_map M s inf_le_left, evalGlobal_eq_pairing,
      Stacks.NonvanishingOpen.eq_triv_smul_basis t'
        (M.presheaf.map (homOfLE (le_top : W ⊓ V z ≤ ⊤)).op s),
      pairing_smul_right, map_mul] at hx
    exact (Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit t' s hxW').mpr
      (isUnit_of_mul_isUnit_left hx)
  · refine fun hx ↦ ⟨V z, trivializationDual t, ?_⟩
    rw [structureAppₗ_evalGlobalHom, evalGlobal_trivializationDual, Scheme.mem_basicOpen X _ x hz]
    exact (Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit t s hz).mp hx

end AlgebraicGeometry.Scheme.Modules
