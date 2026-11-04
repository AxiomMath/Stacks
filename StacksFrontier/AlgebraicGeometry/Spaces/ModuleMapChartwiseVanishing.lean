module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapFibreOverBasePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# Vanishing of a map of modules on an algebraic space is étale local

Let `X` be an algebraic space over `S` and let `φ : M ⟶ N` be a map of `𝒪_X`-modules. Then `φ`
is zero exactly when each of its maps on sections over an étale chart is zero; it is enough that
every étale chart be covered by étale charts on which the maps on sections vanish, and it is
enough to test the étale charts with affine underlying scheme. The same criteria are stated for
the base-changed map of an `AlgebraicGeometry.Space.ModuleMapSituation` and for the map `u_s` on
the fibre `X_s` of an `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation`.

## Main results

* `AlgebraicGeometry.Space.Modules.eq_zero_iff_forall_app_eq_zero`: a map of `𝒪_X`-modules is
  zero exactly when its map on sections over every étale chart is zero.
* `AlgebraicGeometry.Space.Modules.eq_zero_of_locally`: **vanishing is étale local.**  A map of
  `𝒪_X`-modules whose map on sections vanishes on a covering sieve of every étale chart is zero.
* `AlgebraicGeometry.Space.Modules.eq_zero_of_ofArrows`: the same with the covering sieves
  presented by generating families.
* `AlgebraicGeometry.Space.Modules.eq_zero_of_forall_app_isAffine_eq_zero`: **the affine étale
  charts suffice.**
* `AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_iff_forall_app_eq_zero` and
  `AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_of_forall_app_isAffine_eq_zero`: the same
  two statements for the vanishing locus of a map of modules at a test scheme.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.fibreMapEqZero_iff_forall_app_eq_zero`
  and `.fibreMapEqZero_of_forall_app_isAffine_eq_zero`: the same for `u_s = 0` on the fibre over
  a point of an affine base.

## References

* [Stacks Project, Tag 0CWB](https://stacks.math.columbia.edu/tag/0CWB)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Modules

/-- The map on sections over an étale chart of the zero map of `𝒪_X`-modules is zero. -/
theorem app_eq_zero_of_eq_zero {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, m} B S hS X.1 X.2} {φ : M ⟶ N} (hφ : φ = 0)
    (U : SmallEtale B S hS X.1) : φ.val.app (op U) = 0 := by
  subst hφ
  rfl

/-- If the map on sections of a map of `𝒪_X`-modules vanishes over an étale chart `V`, then the
image of any section over a chart `U` receiving a morphism from `V` restricts to zero on `V`. -/
theorem map_app_eq_zero {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N)
    {U V : SmallEtale B S hS X.1} (f : V ⟶ U) (hf : φ.val.app (op V) = 0)
    (a : M.val.obj (op U)) : (N.val.map f.op) ((φ.val.app (op U)) a) = 0 := by
  have happ : (φ.val.app (op V)) ((M.val.map f.op) a) = 0 := by rw [hf]; rfl
  exact (PresheafOfModules.naturality_apply φ.val f.op a).symm.trans happ

/-- `AlgebraicGeometry.Space.Modules.map_app_eq_zero`, with the restriction read on the
underlying presheaf of abelian groups. -/
theorem presheaf_map_app_eq_zero {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N)
    {U V : SmallEtale B S hS X.1} (f : V ⟶ U) (hf : φ.val.app (op V) = 0)
    (a : M.val.obj (op U)) : (N.val.presheaf.map f.op) ((φ.val.app (op U)) a) = 0 :=
  map_app_eq_zero B S hS φ f hf a

/-- **A map of `𝒪_X`-modules whose map on sections over every étale chart vanishes is zero.** -/
theorem eq_zero_of_forall_app_eq_zero {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : ∀ U : SmallEtale B S hS X.1, φ.val.app (op U) = 0) : φ = 0 :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => h U.unop)

/-- **A map of `𝒪_X`-modules is zero exactly when all its maps on sections over étale charts
are.** -/
theorem eq_zero_iff_forall_app_eq_zero {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N) :
    φ = 0 ↔ ∀ U : SmallEtale B S hS X.1, φ.val.app (op U) = 0 :=
  ⟨fun hφ U => app_eq_zero_of_eq_zero B S hS hφ U, eq_zero_of_forall_app_eq_zero B S hS φ⟩

/-- The map on sections over `U` vanishes if it does so over every member of a presieve on `U`
along which sections of the target are separated. -/
private theorem app_eq_zero_of_separated {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N) (U : SmallEtale B S hS X.1)
    (R : Presieve U)
    (hsep : ∀ x y : N.val.obj (op U),
      (∀ ⦃V : SmallEtale B S hS X.1⦄ (f : V ⟶ U), R f →
        N.val.presheaf.map f.op x = N.val.presheaf.map f.op y) → x = y)
    (h : ∀ ⦃V : SmallEtale B S hS X.1⦄ (f : V ⟶ U), R f → φ.val.app (op V) = 0) :
    φ.val.app (op U) = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun a => hsep _ 0 fun _ f hf =>
    (presheaf_map_app_eq_zero B S hS φ f (h f hf) a).trans (map_zero _).symm)

/-- **Vanishing of a map of `𝒪_X`-modules is étale local.**  If every étale chart of `X` carries
a covering sieve of the small étale site whose members all have vanishing map on sections, then
the map is zero. -/
theorem eq_zero_of_locally {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : ∀ U : SmallEtale B S hS X.1, ∃ Sv : Sieve U,
      Sv ∈ SmallEtale.topology B S hS X.1 U ∧
        ∀ ⦃V : SmallEtale B S hS X.1⦄ (f : V ⟶ U), Sv.arrows f → φ.val.app (op V) = 0) :
    φ = 0 := by
  refine eq_zero_of_forall_app_eq_zero B S hS φ fun U => ?_
  obtain ⟨Sv, hSv, hvan⟩ := h U
  exact app_eq_zero_of_separated B S hS φ U Sv
    (fun x y hxy => N.isSheaf.isSeparated U Sv hSv x y fun _ f hf => hxy f hf) hvan

/-- **Vanishing of a map of `𝒪_X`-modules is étale local**, with the covering sieves presented
by generating families of étale charts: if every étale chart carries a family of étale charts over
it which generates a covering sieve and whose members all have vanishing map on sections, then the
map is zero. -/
theorem eq_zero_of_ofArrows {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : ∀ U : SmallEtale B S hS X.1, ∃ (I : Type (u + 1)) (Y : I → SmallEtale B S hS X.1)
      (π : ∀ j, Y j ⟶ U), Sieve.ofArrows Y π ∈ SmallEtale.topology B S hS X.1 U ∧
        ∀ j, φ.val.app (op (Y j)) = 0) :
    φ = 0 := by
  refine eq_zero_of_forall_app_eq_zero B S hS φ fun U => ?_
  obtain ⟨I, Y, π, hcov, hvan⟩ := h U
  refine app_eq_zero_of_separated B S hS φ U (Presieve.ofArrows Y π) (fun x y hxy => ?_) ?_
  · exact ((Presieve.isSeparatedFor_iff_generate (R := Presieve.ofArrows Y π)).2
      (Stacks.SheafOfModules.isSeparated_presheaf N _ hcov)).ext hxy
  · rintro V f ⟨j⟩
    exact hvan j

/-- **The affine étale charts suffice.**  A map of `𝒪_X`-modules whose map on sections vanishes
over every étale chart with affine underlying scheme is zero. -/
theorem eq_zero_of_forall_app_isAffine_eq_zero {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : ∀ U : SmallEtale B S hS X.1, IsAffine (chartScheme U) → φ.val.app (op U) = 0) :
    φ = 0 := by
  refine eq_zero_of_ofArrows B S hS φ fun U => ?_
  obtain ⟨I, Y, a, haff, hcov, -⟩ :=
    SmallEtale.exists_affine_etale_ofArrows B S hS X.1 U
  exact ⟨I, Y, a, hcov, fun j => h (Y j) (haff j)⟩

end Modules

namespace ModuleMapSituation

variable {B S hS} (D : ModuleMapSituation.{u, m} B S hS)
    (P : ModulePullbackSystem.{u, m} B S hS)

/-- **The vanishing locus, chartwise.**  The base change of the map of modules to
a test scheme is zero exactly when its map on sections over every étale chart of the base-change
space is zero. -/
theorem isZeroAt_iff_forall_app_eq_zero (T : D.SchemesOver) :
    D.IsZeroAt P T ↔
      ∀ U : SmallEtale B S hS (D.baseChangeSpace T).1,
        (D.baseChangeHom P T).val.app (op U) = 0 :=
  Modules.eq_zero_iff_forall_app_eq_zero B S hS (D.baseChangeHom P T)

/-- **The vanishing locus is étale local on the base-change space.**  If the map
on sections of the base-changed map vanishes over every étale chart of `X ×_Y T` with affine
underlying scheme, then the base-changed map is zero. -/
theorem isZeroAt_of_forall_app_isAffine_eq_zero (T : D.SchemesOver)
    (h : ∀ U : SmallEtale B S hS (D.baseChangeSpace T).1, IsAffine (chartScheme U) →
      (D.baseChangeHom P T).val.app (op U) = 0) :
    D.IsZeroAt P T :=
  Modules.eq_zero_of_forall_app_isAffine_eq_zero B S hS (D.baseChangeHom P T) h

end ModuleMapSituation

namespace ModuleMapFlatTargetSituation

variable [IsAffine S] (D : ModuleMapFlatTargetSituation B S hS)

/-- **`u_s = 0`, chartwise.**  For a `ModuleMapFlatTargetSituation` over an affine `S`, the
pullback of the map of modules to the fibre over a point `s` of the base is zero exactly when its
map on sections over every étale chart of the fibre `X_s` is zero. -/
theorem fibreMapEqZero_iff_forall_app_eq_zero (s : S) :
    D.FibreMapEqZero B S hS s ↔
      ∀ U : SmallEtale B S hS (D.fibreSpace B S hS s).1,
        ((D.toModuleMapSituation B S hS).baseChangeHom (modulePullbackSystem B S hS)
          (D.fibreTest B S hS s)).val.app (op U) = 0 :=
  (D.toModuleMapSituation B S hS).isZeroAt_iff_forall_app_eq_zero
    (modulePullbackSystem B S hS) (D.fibreTest B S hS s)

/-- **Whether `u_s = 0` is étale local on the fibre `X_s`.**  For a
`ModuleMapFlatTargetSituation` over an affine `S`, if the map on sections of `u_s` vanishes over
the étale charts of the fibre with affine underlying scheme, then `u_s = 0`. -/
theorem fibreMapEqZero_of_forall_app_isAffine_eq_zero (s : S)
    (h : ∀ U : SmallEtale B S hS (D.fibreSpace B S hS s).1, IsAffine (chartScheme U) →
      ((D.toModuleMapSituation B S hS).baseChangeHom (modulePullbackSystem B S hS)
        (D.fibreTest B S hS s)).val.app (op U) = 0) :
    D.FibreMapEqZero B S hS s :=
  (D.toModuleMapSituation B S hS).isZeroAt_of_forall_app_isAffine_eq_zero
    (modulePullbackSystem B S hS) (D.fibreTest B S hS s) h

end ModuleMapFlatTargetSituation

end AlgebraicGeometry.Space

end
