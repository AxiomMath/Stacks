module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperSupportModel.Support
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsFunctorialModel
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsChainModel
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperSupportGlobalSectionsPerfect
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
import StacksCore.Tactic.StacksAttribute

/-!
# One finite projective complex computing `RΓ(X_{R'}, G_{R'})`, functorially in `R'`

Let `R` be a ring, `X` a scheme of finite presentation over `R` and `G` a finitely presented
`𝒪_X`-module, flat over `R`, with support proper over `R`. [Stacks, Tag 0A1I] draws from
[Stacks, Tag 0A1H] a finite complex `M` of finite projective `R`-modules with

`RΓ(X_{R'}, G_{R'}) = M ⊗_R R'`  functorially in the `R`-algebra `R'`.

This file proves that statement, with no hypothesis beyond the source's: in particular `X` is
**not** assumed separated over `R`, and the pseudo-coherence of `RΓ(X, G)` is not carried.

## Main results

* `…ProperSupportModel.exists_finiteProjectiveModel_derivedGlobalSections_functorial`:
  **[Stacks, Tag 0A1I]**.
* `…ProperSupportModel.isPerfect_derivedGlobalSectionsOverBase_supportModule`: `RΓ(Z, G')` is
  perfect in `D(R)`, `Z` the scheme-theoretic support of `G` and `G' = ι^* G`.
* `…ProperSupportModel.baseChangeChainComparison_congr`: the chain-level comparison of
  [Stacks, Tag 07VL] is insensitive to replacing the projection of a base change by an equal one.

## The proof

**Perfection.** `RΓ(X, G)` is perfect in `D(R)`: this is [Stacks, Tag 0A1H] for `E = 𝒪_X` and the
one-term complex `G`, read over the affine base, which is
`ProperSupportGlobalSectionsPerfect.isPerfect_derivedGlobalSectionsOverBase_of_properSupport`.
This gives `M`.

**Base change, without separatedness.** The source obtains the identification from the base
change half of [Stacks, Tag 0A1H] and the canonical base change maps. Here it is computed by a
Čech model, and the obstruction that the finite intersections of an affine cover of `X` need not
be affine is removed by passing to the **scheme-theoretic support** `ι : Z ⟶ X` of `G`, with
`G' = ι^* G` and `ι_* G' ≅ G` ([Stacks, Tag 0CYS]). Since the support of `G` is proper over `R`,
so is `Z` ([Stacks, Tag 0CYS] (1) ⟺ (2)); in particular `Z` is separated over `R`, `G'` is
quasi-coherent and flat over `R` ([Stacks, Tag 0FLM]). For a base change `X' = X ×_R R'`, the
base change of `Z` is `Z' = Z ×_X X'`, a closed subscheme of `X'` with
`g^* G ≅ ι'_* (g_Z^* G')` ([Stacks, Tag 02KG]), and

`RΓ(X', g^* G) ≅ RΓ(Z', g_Z^* G')`

by `supportComparisonIso`, which is [Stacks, Tag 089W] in `D(R')` for the affine morphism
`ι' : Z' ⟶ X'`. On the separated `Z` everything is the existing development of
[Stacks, Tag 07VK] (2) and [Stacks, Tag 07VL]: a finite affine cover `U` of `Z` with affine
intersections, a chain-level model `u : M ⟶ Č_alt(U, G')` (a quasi-isomorphism, `M` being
K-projective), and for every base change the chain-level comparison

`Θ(φ, square) : M ⊗_R R' ⟶ Č_alt(g_Z⁻¹ U, g_Z^* G')`,

the termwise base change of `u` followed by the Čech base-change isomorphism. It is a
quasi-isomorphism, and it satisfies the cocycle square of [Stacks, Tag 07VL] for two successive
base changes. The identification `c(φ, square)` of `RΓ(X', g^* G)` with `M ⊗_R R'` is the one
`Θ(φ, square)` induces.

## Implementation notes

**What "functorially in `R'`" is.** Exactly as in [Stacks, Tag 07VL]
(`ProperFlatGlobalSections.exists_finiteProjectiveModel_homology_iso_functorial`),
the functoriality is the cocycle square of the chain-level comparisons `Θ`, and the derived
identifications `c` are pinned to `Θ`, so that the family `c` has a single origin over `R` and is
not a choice per `R'`. The difference is that here `Θ` lands in the Čech complex of the support
`Z'` rather than of `X'`, and that the pin passes through the canonical comparison
`supportComparisonIso`. The cocycle is stated for two successive base changes of `X`: the
support of the composite base change is `Z ×_X X''`, which is the base change of `Z'` along
`Spec R'' ⟶ Spec R'` through `supportTowerMap`, and `cechCongrIso` identifies the two Čech models
of `Z ×_X X''` that arise, along the equality `supportTowerMap_fst`.

**The cover is bound inside the existential**, as in [Stacks, Tag 07VL]: properness of `Z`
supplies it (`exists_finiteAffineCover_of_isProper`), so the statement is about `f` and `G`.

**The derived-category model.** Everything runs under `CategoryTheory.HasDerivedCategory.standard`
at priority `10000`, as the other files on derived global sections over an affine base do.

## References

* [Stacks Project, Tag 0A1I](https://stacks.math.columbia.edu/tag/0A1I)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 07VL](https://stacks.math.columbia.edu/tag/07VL)
* [Stacks Project, Tag 0CYS](https://stacks.math.columbia.edu/tag/0CYS)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportModel

attribute [local instance 10000] HasDerivedCategory.standard

section Congr

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  {Y Y' : Scheme.{u}} {p : Y ⟶ Spec (.of A)} [IsSeparated p] {p' : Y' ⟶ Spec (.of A')}
  (F : Y.Modules) [F.IsQuasicoherent] {I : Type u} [Finite I]
  (U : I → Y.Opens) (hU : (⊤ : Y.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

/-- The `A'`-linear Čech models of the inverse-image covers along two equal morphisms
`q₁ = q₂ : Y' ⟶ Y` agree. -/
def cechCongrIso {q₁ q₂ : Y' ⟶ Y} (h : q₁ = q₂) :
    baseAlternatingCechComplex p' (fun j => q₁ ⁻¹ᵁ U j) (top_eq_iSup_preimage q₁ U hU)
        ((Scheme.Modules.pullback q₁).obj F) ≅
      baseAlternatingCechComplex p' (fun j => q₂ ⁻¹ᵁ U j) (top_eq_iSup_preimage q₂ U hU)
        ((Scheme.Modules.pullback q₂).obj F) :=
  eqToIso (by subst h; rfl)

/-- The chain-level comparison of [Stacks, Tag 07VL] along two equal morphisms agree, through
`cechCongrIso`. -/
theorem baseChangeChainComparison_congr {q₁ q₂ : Y' ⟶ Y} (h : q₁ = q₂)
    (hsq₁ : IsPullback q₁ p' p (Spec.map (CommRingCat.ofHom φ)))
    (hsq₂ : IsPullback q₂ p' p (Spec.map (CommRingCat.ofHom φ)))
    {M : CochainComplex (ModuleCat.{u} A) ℤ} (u : M ⟶ baseAlternatingCechComplex p U hU F) :
    baseChangeChainComparison φ hsq₁ F U hU hUaff u ≫ (cechCongrIso F U hU h).hom =
      baseChangeChainComparison φ hsq₂ F U hU hUaff u := by
  subst h
  simp [cechCongrIso]

end Congr

section Model

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- A perfect object of `D(R)` stays perfect under isomorphism. -/
theorem isPerfect_of_iso {K L : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ L)
    (h : StacksDraft.Perfect.IsPerfect L) : StacksDraft.Perfect.IsPerfect K := by
  obtain ⟨P, a, b, h1, h2, h3, h4, ⟨e'⟩⟩ := h
  exact ⟨P, a, b, h1, h2, h3, h4, ⟨e ≪≫ e'⟩⟩

variable (G : X.Modules) [G.IsQuasicoherent] [G.IsFiniteType]

/-- **`RΓ(Z, G')` is perfect**, `Z` the scheme-theoretic support of `G` and `G' = ι^* G`, when `f`
is of finite presentation and `G` is of finite presentation, flat over `R`, with proper support:
it is `RΓ(X, G)` (`derivedGlobalSectionsOverBasePushforwardIso` and `ι_* G' ≅ G`), which is perfect
by [Stacks, Tag 0A1H]. -/
theorem isPerfect_derivedGlobalSectionsOverBase_supportModule
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] [G.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom G)
    (hsupp : ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp G ⊆ (Z : Set X)) :
    StacksDraft.Perfect.IsPerfect
      (derivedGlobalSectionsOverBase (supportι G ≫ f) (supportModule G)) :=
  isPerfect_of_iso
    (derivedGlobalSectionsOverBasePushforwardIso f (supportι G) (supportModule G) ≪≫
      derivedGlobalSectionsOverBaseMapIso f (supportModuleIso G))
    (ProperSupportGlobalSectionsPerfect.isPerfect_derivedGlobalSectionsOverBase_of_properSupport
      f G hflat hsupp)

end Model

section Tag

/-- **[Stacks, Tag 0A1I].** Let `R` be a ring, let `X` be a scheme of finite presentation over `R`
and let `G` be a finitely presented `𝒪_X`-module, flat over `R`, whose support is proper over `R`.
Then there is a finite complex `M` of finite projective `R`-modules and, for every ring map
`φ : R ⟶ R'` and every cartesian square exhibiting `X'` as `X ×_R R'`, an identification

`c(φ, square) : RΓ(X_{R'}, G_{R'}) ≅ M ⊗_R R'`  in `D(R')`,

functorial in `R'`: there are a finite affine open cover `U` of the scheme-theoretic support `Z`
of `G` and chain-level comparisons

`Θ(φ, square) : M ⊗_R R' ⟶ Č_alt(Z_{R'}, U_{R'}, G'_{R'})`,

`G' = G|_Z`, such that

* every `Θ(φ, square)` is a quasi-isomorphism;
* `c(φ, square)` is the identification `Θ(φ, square)` induces, through the Čech model of
  `RΓ(Z_{R'}, G'_{R'})` and the canonical `RΓ(Z_{R'}, G'_{R'}) ≅ RΓ(X_{R'}, G_{R'})`
  (`supportComparisonIso`);
* **the comparisons are functorial in `R'`**: for a second ring map `ψ : R' ⟶ R''` and a second
  cartesian square, the extension of scalars along `ψ` of `Θ(φ, square)`, followed by the Čech
  base-change isomorphism of [Stacks, Tag 07VK] (2) for `Z_{R''} = Z_{R'} ×_{R'} R''` and by the
  identifications of the modules and covers, is `Θ(ψ ∘ φ, pasted square)` read through
  `(M ⊗_R R') ⊗_{R'} R'' ≅ M ⊗_R R''`.

The hypotheses are exactly the source's: `X` is not assumed separated, and nothing about
`RΓ(X, G)` is assumed. `M` comes from the perfection of `RΓ(X, G)`, which is [Stacks, Tag 0A1H];
the identifications and their functoriality are computed on the support `Z`, which is proper and
hence separated over `R`; see the module docstring. -/
@[stacks 0A1I "the remark in full: one finite complex M of finite projective R-modules, the \
identification RGamma(X_{R'}, G_{R'}) = M tensor_R R' in D(R') for every base change, as a family \
of isomorphisms indexed by the ring map and the cartesian square and pinned to a single \
chain-level model over R, and the functoriality in R' as the cocycle square of the chain-level \
comparisons for two successive base changes; under exactly the source's hypotheses (X of finite \
presentation over R, not assumed separated; G finitely presented, flat over R, with proper \
support). The comparisons are Čech models of the scheme-theoretic support of G, which is proper \
over R; the cover is bound inside the existential"]
theorem exists_finiteProjectiveModel_derivedGlobalSections_functorial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (hf : FinitePresentation f) (G : X.Modules) (hGfp : G.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom G)
    (hsupp : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp G ⊆ (Z : Set X)) :
    haveI : G.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation G
    haveI : G.IsFiniteType := Stacks.StalkFiniteType.isFiniteType_of_isFinitePresentation G
    letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
    haveI : IsProper (supportι G ≫ f) := isProper_supportι_comp G f hsupp
    ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite R (M.X i)) ∧ (∀ i : ℤ, Module.Projective R (M.X i)) ∧
        ∃ (c : ∀ {R' : Type u} [CommRing R'] (φ : R →+* R') {X' : Scheme.{u}}
              {f' : X' ⟶ Spec (.of R')} {g : X' ⟶ X},
              IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)) →
                (derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj G) ≅
                  DerivedCategory.Q.obj (extendScalarsComplex φ M)))
          (I : Type u) (hIfin : Finite I) (hIlin : LinearOrder I)
          (U : I → (supportScheme G).Opens) (hU : (⊤ : (supportScheme G).Opens) = ⨆ i, U i)
          (hUaff : ∀ i, IsAffineOpen (U i)),
          haveI : Finite I := hIfin
          letI : LinearOrder I := hIlin
          ∃ (_haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
            (Θ : ∀ {R' : Type u} [CommRing R'] (φ : R →+* R') {X' : Scheme.{u}}
                {f' : X' ⟶ Spec (.of R')} {g : X' ⟶ X},
                IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)) →
                  (extendScalarsComplex φ M ⟶
                    baseAlternatingCechComplex (supportSnd G g ≫ f')
                      (fun j => supportFst G g ⁻¹ᵁ U j) (top_eq_iSup_preimage _ U hU)
                      ((Scheme.Modules.pullback (supportFst G g)).obj (supportModule G)))),
            (∀ {R' : Type u} [CommRing R'] (φ : R →+* R') {X' : Scheme.{u}}
                {f' : X' ⟶ Spec (.of R')} {g : X' ⟶ X}
                (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))),
                QuasiIso (Θ φ hsq)) ∧
              (∀ {R' : Type u} [CommRing R'] (φ : R →+* R') {X' : Scheme.{u}}
                  {f' : X' ⟶ Spec (.of R')} {g : X' ⟶ X}
                  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))),
                  (c φ hsq).inv =
                    (DerivedCategory.Q.map (Θ φ hsq) ≫
                      (alternatingCechIsoDerivedGlobalSectionsOverBase (supportSnd G g ≫ f')
                        (fun j => supportFst G g ⁻¹ᵁ U j) (top_eq_iSup_preimage _ U hU)
                        ((Scheme.Modules.pullback (supportFst G g)).obj (supportModule G))
                        (iInf_preimage_isAffineOpen φ (isPullback_support G g f φ hsq) U
                          hUaff)).hom) ≫
                      (supportComparisonIso G g f').hom) ∧
              (∀ {R' R'' : Type u} [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'')
                  {X' X'' : Scheme.{u}} {f' : X' ⟶ Spec (.of R')} {f'' : X'' ⟶ Spec (.of R'')}
                  {g : X' ⟶ X} {g' : X'' ⟶ X'}
                  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
                  (hsq' : IsPullback g' f'' f' (Spec.map (CommRingCat.ofHom ψ))),
                  haveI : IsSeparated (supportSnd G g ≫ f') :=
                    isSeparated_of_isPullback φ (isPullback_support G g f φ hsq)
                  ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
                          (ComplexShape.up ℤ)).map (Θ φ hsq) ≫
                      (baseAlternatingCechComplexBaseChangeIso ψ
                          (isPullback_supportTower G g g' ψ hsq')
                          ((Scheme.Modules.pullback (supportFst G g)).obj (supportModule G))
                          (fun j => supportFst G g ⁻¹ᵁ U j) (top_eq_iSup_preimage _ U hU)
                          (isAffineOpen_preimage φ (isPullback_support G g f φ hsq) U
                            hUaff)).hom ≫
                      (baseAlternatingCechComplexMapIso (supportSnd G (g' ≫ g) ≫ f'')
                        (fun j => (supportTowerMap G g g' ≫ supportFst G g) ⁻¹ᵁ U j)
                        (top_eq_iSup_preimage _ U hU)
                        ((Scheme.Modules.pullbackComp (supportTowerMap G g g')
                          (supportFst G g)).app (supportModule G))).hom ≫
                      (cechCongrIso (supportModule G) U hU (supportTowerMap_fst G g g')).hom =
                    (extendScalarsComplexCompIso φ ψ).hom.app M ≫
                      Θ (ψ.comp φ) (Stacks.Cech.isPullback_comp_specMap φ ψ f f' f'' g g' hsq
                        hsq')) := by
  classical
  have : G.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation G
  have : G.IsFiniteType := Stacks.StalkFiniteType.isFiniteType_of_isFinitePresentation G
  have : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have : IsProper (supportι G ≫ f) := isProper_supportι_comp G f hsupp
  have : QuasiCompact f := hf.quasiCompact
  have : QuasiSeparated f := hf.quasiSeparated
  have hflatZ := isFlatOver_supportModule G f hflat
  obtain ⟨I, hIfin, hIlin, U, hU, hUaff, haff⟩ :=
    exists_finiteAffineCover_of_isProper (supportι G ≫ f)
  obtain ⟨M, a, b, hGE, hLE, hfin, hproj, ⟨eM⟩⟩ :=
    isPerfect_derivedGlobalSectionsOverBase_supportModule f G hflat hsupp
  have : M.IsStrictlyLE b := hLE
  have hprojX : ∀ n : ℤ, CategoryTheory.Projective (M.X n) := fun n =>
    have := hproj n
    inferInstance
  have hKP : M.IsKProjective := CochainComplex.isKProjective_of_projective M b
  obtain ⟨u, hu⟩ := StacksDraft.PseudoCoherence.exists_chainMap_of_isKProjective M
    (baseAlternatingCechComplex (supportι G ≫ f) U hU (supportModule G))
    (eM.inv ≫ (alternatingCechIsoDerivedGlobalSectionsOverBase (supportι G ≫ f) U hU
      (supportModule G) haff).inv)
  have hqu : QuasiIso u :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 (by rw [hu]; infer_instance)
  have : ∀ n : ℤ, Module.Flat R (M.X n) := fun n =>
    have := hproj n
    Module.Flat.of_projective
  refine ⟨M, a, b, hGE, hLE, hfin, hproj,
    fun {R'} [CommRing R'] φ {X'} {f'} {g} hsq =>
      (supportComparisonIso G g f').symm ≪≫
        (@asIso _ _ _ _
          (DerivedCategory.Q.map (baseChangeChainComparison φ (isPullback_support G g f φ hsq)
              (supportModule G) U hU hUaff u) ≫
            (alternatingCechIsoDerivedGlobalSectionsOverBase (supportSnd G g ≫ f')
              (fun j => supportFst G g ⁻¹ᵁ U j) (top_eq_iSup_preimage _ U hU)
              ((Scheme.Modules.pullback (supportFst G g)).obj (supportModule G))
              (iInf_preimage_isAffineOpen φ (isPullback_support G g f φ hsq) U hUaff)).hom)
          (isIso_baseChangeChainComparisonDerived φ (isPullback_support G g f φ hsq)
            (supportModule G) U hU hUaff u hflatZ b)).symm,
    I, Finite.of_fintype I, hIlin, U, hU, hUaff, haff,
    fun {R'} [CommRing R'] φ {X'} {f'} {g} hsq =>
      baseChangeChainComparison φ (isPullback_support G g f φ hsq) (supportModule G) U hU hUaff u,
    fun {R'} [CommRing R'] φ {X'} {f'} {g} hsq =>
      quasiIso_baseChangeChainComparison φ (isPullback_support G g f φ hsq) (supportModule G)
        U hU hUaff u hflatZ b,
    fun {R'} [CommRing R'] φ {X'} {f'} {g} hsq => rfl,
    fun {R'} {R''} [CommRing R'] [CommRing R''] φ ψ {X'} {X''} {f'} {f''} {g} {g'} hsq hsq' => ?_⟩
  have : IsSeparated (supportSnd G g ≫ f') :=
    isSeparated_of_isPullback φ (isPullback_support G g f φ hsq)
  have h := baseChangeChainComparison_comp φ ψ (isPullback_support G g f φ hsq)
    (isPullback_supportTower G g g' ψ hsq') (supportModule G) U hU hUaff u
  beta_reduce
  rw [← baseChangeChainComparison_congr (ψ.comp φ) (supportModule G) U hU hUaff
    (supportTowerMap_fst G g g')
    (Stacks.Cech.isPullback_comp_specMap φ ψ (supportι G ≫ f) (supportSnd G g ≫ f')
      (supportSnd G (g' ≫ g) ≫ f'') (supportFst G g) (supportTowerMap G g g')
      (isPullback_support G g f φ hsq) (isPullback_supportTower G g g' ψ hsq')) _ u]
  conv_rhs => rw [← Category.assoc, ← h]
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) (Category.assoc _ _ _).symm

end Tag

end Stacks.AlgebraicGeometry.ProperSupportModel
