module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.LocallyConstantCoefficients.UnibranchExtensionByZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.IrreducibleOpensReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.LocallyConstantOpens
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.RestrictToDenseOpenCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.NormalizationReduction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.CoefficientHypotheses
import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the cohomology of the extension by zero of a locally constant sheaf on a curve

Let `Λ` be a Noetherian ring, let `k` be an algebraically closed field, let `X` be a separated
scheme of finite type over `k` of dimension at most one, let `j : U → X` be an open immersion
with `U` connected, let `ℓ` be a prime number, let `n > 0` and let `𝒢` be a finite type, locally
constant sheaf of `Λ`-modules on `U_étale` annihilated by `ℓ ^ n`. [Stacks, Tag 0GJH] says that
`H^q_étale(X, j_!𝒢)` is a finite `Λ`-module (1) if `ℓ` is prime to the characteristic of `k`, and
(2) if `X` is proper.

## Main results

* `module_finite_cohomology_extensionByZero_of_isFiniteTypeLocallyConstant`
  — both cases together, for an arbitrary open immersion `j`.
* `module_finite_cohomology_extensionByZero_of_isFiniteTypeLocallyConstant_of_coprime`
  — **Stacks Tag 0GJH, part (1)**.
* `module_finite_cohomology_extensionByZero_of_isFiniteTypeLocallyConstant_of_isProper`
  — **Stacks Tag 0GJH, part (2)**.

## Implementation notes

**The source's proof needs `U` geometrically unibranch.** The proof of the source applies Lemma
0GJ0 to `U`, and Lemma 0GJ0 is stated (and true) only for an irreducible geometrically unibranch
scheme: on a connected but not unibranch `U` (a nodal curve, say) a locally constant sheaf of
modules over an infinite ring can have infinite monodromy and is then not trivialized by any
finite étale cover. The statement itself holds for every `U`, and the source's argument is
completed here by a reduction to that case:

* the étale cohomology does not see nilpotents, so `X` may be replaced by its reduction
  (`j_! 𝒢 ≅ i_* j_{red!} i_U^{-1} 𝒢` for the reduction `i : X_red ⟶ X`, by Tag 0GJ1 for the
  closed immersion `i` and the open-closed sequence of Tag 095L with empty open part, and
  `H^q(X, i_* -) = H^q(X_red, -)` by Lemma 0GJD);
* on a reduced `X`, `j_! 𝒢` is constructible and the reduction of the proof of Theorem 0GJI
  (`Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_of_forall_isIrreducible_opens`,
  Lemmas 0GJE and 0GJG) reduces to `j_{W!}(𝒢')` for irreducible opens `W` on which the sheaf
  `𝒢'` is finite type and locally constant;
* for such a `W`, Lemma 0GJE on the dense open `W₀ ⊆ X` over which the normalization of `X` is an
  isomorphism replaces `W` by `W ∩ W₀`, which is irreducible and normal, hence geometrically
  unibranch, and there the source's proof applies
  (`module_finite_cohomology_extensionByZero_of_isGeometricallyUnibranch`).

In particular the connectedness of `U` is not used; it is kept in the two tagged statements
because the source states it.

## References

* [Stacks Project, Tag 0GJH](https://stacks.math.columbia.edu/tag/0GJH)
* [Stacks Project, Tag 0GJ0](https://stacks.math.columbia.edu/tag/0GJ0)
* [Stacks Project, Tag 0GJE](https://stacks.math.columbia.edu/tag/0GJE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u r

namespace Stacks.EtaleCohomology.TorsionModules

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- **A finite type, locally constant sheaf of modules over a Noetherian ring is constructible**,
in the model `Stacks.EtaleCohomology.EtaleModules`: on the canonical big étale site this is
`AlgebraicGeometry.isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant`. -/
theorem isConstructibleEtaleModule_of_isFiniteTypeLocallyConstantModuleSheaf {X : Scheme.{u}}
    (G : EtaleModules.{u, r} Λ X)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      X.smallEtaleTopology Λ G) :
    IsConstructibleEtaleModule Λ G :=
  have : ∀ (T : (BigEtaleSite.containing X).Scheme) (V : SmallEtale _ T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology _ T.obj T.property).over V)
        (ModuleCat.{max (u + 1) r} Λ) :=
    fun T V => SmallEtale.hasWeakSheafify_over_moduleCat _ Λ T V
  isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant (BigEtaleSite.containing X)
    ((BigEtaleSite.containing X).obj X (BigEtaleSite.contains_containing X)) Λ _
    ((isFiniteTypeLocallyConstantModuleSheaf_etaleModuleToBoundedSite_iff Λ
      (BigEtaleSite.containing X) (BigEtaleSite.contains_containing X) G).2 hG)

/-- A scheme of finite type over a field is Noetherian. -/
private theorem isNoetherian_of_finiteType {k : Type u} [Field k] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] [QuasiCompact π] :
    AlgebraicGeometry.IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian π
  have := QuasiCompact.compactSpace_of_compactSpace π
  ⟨⟩

/-- Applying an additive functor to a sheaf killed by `m` gives a sheaf killed by `m`. -/
private theorem nsmul_id_obj_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {G : C} {m : ℕ} (h : m • 𝟙 G = 0) :
    m • 𝟙 (F.obj G) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, h, Functor.map_zero]

/-- A reduced separated scheme of finite type over an algebraically closed field has a dense open
which is normal: one over which the normalization is an isomorphism. -/
theorem exists_dense_opens_isNormal_of_isReduced
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [IsReduced X] :
    ∃ W₀ : X.Opens, Dense (W₀ : Set X) ∧ IsNormal W₀.toScheme := by
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated π
  have := isNoetherian_of_finiteType π
  -- the dense normal open `W₀` over which the normalization is an isomorphism
  set ν := normalizationOverField k π
  have : IsFinite ν := isFinite_normalizationOverField k π
  have : IsNormal (normalizationSchemeOverField k π) :=
    Scheme.isNormal_normalizationScheme X (finite_irreducibleComponents_of_locallyOfFiniteType k π)
  -- supplied explicitly: instance search for `LocallyOfFiniteType (ν ≫ π)` times out
  have : LocallyOfFiniteType ν := IsFinite.instLocallyOfFiniteType ν
  have : LocallyOfFiniteType (ν ≫ π) := locallyOfFiniteType_comp ν π
  have := isNoetherian_of_finiteType (ν ≫ π)
  have : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have : Finite (irreducibleComponents (normalizationSchemeOverField k π)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  obtain ⟨W₀, hW₀d, hW₀iso⟩ := exists_dense_open_isIso_morphismRestrict_of_isIntegralHom ν
    (Scheme.isBirational_normalization X _) (Or.inl ⟨inferInstance, inferInstance⟩)
  exact ⟨W₀, hW₀d, isNormal_of_iso (asIso (ν ∣_ W₀)).symm⟩

/-- **The case of an irreducible open of a reduced curve.** Let `X` be a reduced separated scheme
of finite type over an algebraically closed field `k` of dimension at most one, `W ⊆ X` an
irreducible open and `𝒢` a finite type, locally constant sheaf of `Λ`-modules on `W_étale` killed
by `ℓ ^ n` for a prime `ℓ`. If `ℓ` is prime to the characteristic of `k`, or `X` is proper, then
`H^q(X, j_{W!} 𝒢)` is a finite `Λ`-module.

The normalization of `X` is an isomorphism over a dense open `W₀`, which is therefore normal;
Lemma 0GJE for `W₀` replaces `j_{W!} 𝒢` by the extension by zero from `W ∩ W₀`, which is
irreducible and normal, hence geometrically unibranch, and there the source's proof applies. -/
theorem module_finite_cohomology_extensionByZero_of_isIrreducible_of_isReduced
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [IsReduced X]
    (hX : topologicalKrullDim X ≤ 1) (W : X.Opens) (hW : IsIrreducible (W : Set X))
    (G : EtaleModules.{u, r} Λ W)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      W.toScheme.smallEtaleTopology Λ G)
    {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 0 < n) (hGn : ℓ ^ n • 𝟙 G = 0)
    (h : ℓ.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ W.ι).obj G)) := by
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated π
  have := isNoetherian_of_finiteType π
  obtain ⟨W₀, hW₀d, _⟩ := exists_dense_opens_isNormal_of_isReduced π
  -- the open `P = W ∩ W₀`
  let P := pullback W.ι W₀.ι
  let p₁ : P ⟶ W := pullback.fst W.ι W₀.ι
  let p₂ : P ⟶ W₀ := pullback.snd W.ι W₀.ι
  have : IsNormal P := isNormal_of_isOpenImmersion p₂
  have : IrreducibleSpace W := Subtype.irreducibleSpace hW
  have : Nonempty P := by
    obtain ⟨x, hxW, hxW₀⟩ := hW₀d.inter_open_nonempty (W : Set X) W.isOpen hW.nonempty
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.ι) (g := W₀.ι)
      ⟨x, hxW⟩ ⟨x, hxW₀⟩ (by simp)
    exact ⟨z⟩
  have : IrreducibleSpace P := p₁.isOpenEmbedding.irreducibleSpace
  have hP : IsGeometricallyUnibranch P := isGeometricallyUnibranch_of_isNormal
  -- Lemma 0GJE for the dense open `W₀`
  set F := (etaleModuleExtensionByZero.{u, r} Λ W.ι).obj G
  have hc : IsConstructibleEtaleModule Λ F :=
    isConstructibleEtaleModule_etaleModuleExtensionByZero Λ W.ι G
      (isConstructibleEtaleModule_of_isFiniteTypeLocallyConstantModuleSheaf Λ G hG)
  let B := BigEtaleSite.containing X
  have hXB : B.Contains X := BigEtaleSite.contains_containing X
  refine (module_finite_cohomology_iff_extensionByZero_of_dense B Λ (B.obj X hXB) π hX F
    ((isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hXB F).1 hc) W₀.ι
    (by rwa [Scheme.Opens.range_ι]) q).2 ?_
  -- `j_{W₀!} j_{W₀}^{-1} j_{W!} 𝒢` is the extension by zero from `P`
  let e : (etaleModuleExtensionByZero.{u, r} Λ W₀.ι).obj
      ((etaleModuleRestriction.{u, r} Λ W₀.ι).obj F) ≅
      (etaleModuleExtensionByZero.{u, r} Λ (p₂ ≫ W₀.ι)).obj
        ((etaleModuleInverseImage.{u, r} Λ p₁).obj G) :=
    (etaleModuleExtensionByZero.{u, r} Λ W₀.ι).mapIso
        (((etaleModuleInverseImageRestrictionIso.{u, r} Λ W₀.ι).app F).symm ≪≫
          ((etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ
            (IsPullback.of_hasPullback W.ι W₀.ι)).app G).symm) ≪≫
      ((etaleModuleExtensionByZeroCompIso.{u, r} Λ p₂ W₀.ι).app _).symm
  have hfin := module_finite_cohomology_extensionByZero_of_isGeometricallyUnibranch Λ π hX
    (p₂ ≫ W₀.ι) hP _ (isFiniteTypeLocallyConstantModuleSheaf_etaleModuleInverseImage Λ p₁ G hG)
    hℓ hn
    (nsmul_id_obj_eq_zero (etaleModuleInverseImage.{u, r} Λ p₁) hGn) h q
  exact Module.Finite.equiv (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).mapIso
    e).symm.toLinearEquiv

/-- **The case of a reduced curve.** Let `X` be a reduced separated scheme of finite type over an
algebraically closed field `k` of dimension at most one, `j : U ⟶ X` an open immersion and `𝒢` a
finite type, locally constant sheaf of `Λ`-modules on `U_étale` killed by `ℓ ^ n` for a prime
`ℓ`. If `ℓ` is prime to the characteristic of `k`, or `X` is proper, then `H^q(X, j_! 𝒢)` is a
finite `Λ`-module. The sheaf `j_! 𝒢` is constructible, and the reduction of the proof of
Theorem 0GJI to irreducible opens
(`Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_of_forall_isIrreducible_opens`)
leads to `module_finite_cohomology_extensionByZero_of_isIrreducible_of_isReduced`. -/
theorem module_finite_cohomology_extensionByZero_of_isReduced
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [IsReduced X]
    (hX : topologicalKrullDim X ≤ 1) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : EtaleModules.{u, r} Λ U)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      U.smallEtaleTopology Λ G)
    {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 0 < n) (hGn : ℓ ^ n • 𝟙 G = 0)
    (h : ℓ.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj G)) := by
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated π
  obtain ⟨⟩ := isNoetherian_of_finiteType π
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  refine module_finite_cohomology_of_forall_isIrreducible_opens Λ π hX _
    (isConstructibleEtaleModule_etaleModuleExtensionByZero Λ j G
      (isConstructibleEtaleModule_of_isFiniteTypeLocallyConstantModuleSheaf Λ G hG)) q
    fun W hW hloc => ?_
  refine module_finite_cohomology_extensionByZero_of_isIrreducible_of_isReduced Λ π hX W hW _
    hloc hℓ hn ?_ h q
  exact nsmul_id_obj_eq_zero _ (nsmul_id_obj_eq_zero _ hGn)

/-- **[Stacks, Tag 0GJH], both cases, for an arbitrary open immersion.** Let `Λ` be a Noetherian
ring, `k` an algebraically closed field, `X` a separated scheme of finite type over `k` of
dimension at most one, `j : U ⟶ X` an open immersion, `ℓ` a prime, `n > 0` and `𝒢` a finite
type, locally constant sheaf of `Λ`-modules on `U_étale` annihilated by `ℓ ^ n`. If `ℓ` is prime
to the characteristic of `k`, or `X` is proper over `k`, then `H^q_étale(X, j_! 𝒢)` is a finite
`Λ`-module.

The reduction `i : X_red ⟶ X` reduces to `X` reduced: `𝒢 ≅ i'_* i'^{-1} 𝒢` for the base change
`i' : U ×_X X_red ⟶ U` (the open-closed sequence of Tag 095L with empty open part), Tag 0GJ1 for
the closed immersion `i` gives `j_! i'_* ≅ i_* j_{red!}`, and Lemma 0GJD gives
`H^q(X, i_* -) = H^q(X_red, -)`. -/
theorem module_finite_cohomology_extensionByZero_of_isFiniteTypeLocallyConstant
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    (hX : topologicalKrullDim X ≤ 1) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : EtaleModules.{u, r} Λ U)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      U.smallEtaleTopology Λ G)
    {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 0 < n) (hGn : ℓ ^ n • 𝟙 G = 0)
    (h : ℓ.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj G)) := by
  let i := X.reductionι
  have : Surjective i := ⟨X.surjective_reductionι⟩
  let i' : pullback j i ⟶ U := pullback.fst j i
  let j' : pullback j i ⟶ X.reduction := pullback.snd j i
  -- `𝒢 ≅ i'_* i'^{-1} 𝒢`
  let o := (⊥ : U.Opens).ι
  have ho : Set.range o.base = (Set.range i'.base)ᶜ := by
    rw [Scheme.Opens.range_ι, Set.range_eq_univ.2 (Surjective.surj (f := i')), Set.compl_univ]
    rfl
  have hN : IsZero ((etaleModuleRestriction.{u, r} Λ o).obj G) :=
    isZero_etaleModule_of_forall_isZero_sections Λ _ fun V =>
      isZero_etaleModule_sections_of_isEmpty Λ _ V ⟨fun x => (V.hom.base x).2⟩
  have hu := isIso_etaleModuleInverseImageAdj_unit_app_of_isZero Λ i' o ho G hN
  let e : (etaleModuleExtensionByZero.{u, r} Λ j).obj G ≅
      (etaleModuleDirectImage.{u, r} Λ i).obj ((etaleModuleExtensionByZero.{u, r} Λ j').obj
        ((etaleModuleInverseImage.{u, r} Λ i').obj G)) :=
    (etaleModuleExtensionByZero.{u, r} Λ j).mapIso
        (asIso ((etaleModuleInverseImageAdj.{u, r} Λ i').unit.app G)) ≪≫
      (etaleModuleExtensionByZeroDirectImageIso.{u, r} Λ i' j' j i
        (IsPullback.of_hasPullback j i)).app _
  -- the reduced curve
  have hXr : topologicalKrullDim X.reduction ≤ 1 :=
    (topologicalKrullDim_le_of_isIntegralHom i).trans hX
  -- supplied explicitly: instance search for `LocallyOfFiniteType (i ≫ π)` times out
  have : LocallyOfFiniteType i := IsFinite.instLocallyOfFiniteType i
  have : LocallyOfFiniteType (i ≫ π) := locallyOfFiniteType_comp i π
  have hfin := module_finite_cohomology_extensionByZero_of_isReduced Λ (i ≫ π) hXr j'
    ((etaleModuleInverseImage.{u, r} Λ i').obj G)
    (isFiniteTypeLocallyConstantModuleSheaf_etaleModuleInverseImage Λ i' G hG) hℓ hn
    (nsmul_id_obj_eq_zero (etaleModuleInverseImage.{u, r} Λ i') hGn)
    (h.imp id fun hp => by
      have := hp
      have : IsFinite i := inferInstanceAs (IsFinite X.reductionι)
      infer_instance) q
  exact Module.Finite.equiv ((moduleEtaleCohomology_isIntegralHom_iso.{u, r} Λ i q _) ≪≫
    ((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).mapIso e.symm).toLinearEquiv

/-- **Stacks Project, Tag 0GJH, part (1).** Let `Λ` be a Noetherian ring, let `k` be an
algebraically closed field, let `X` be a separated scheme of finite type over `k` of dimension at
most one, let `j : U ⟶ X` be an open immersion with `U` connected, let `ℓ` be a prime number
prime to the characteristic of `k`, let `n > 0` and let `𝒢` be a finite type, locally constant
sheaf of `Λ`-modules on `U_étale` annihilated by `ℓ ^ n`. Then `H^q_étale(X, j_! 𝒢)` is a finite
`Λ`-module for every `q`.

"Separated of finite type over `k`" is `IsSeparated π`, `LocallyOfFiniteType π` and
`QuasiCompact π` for the structure morphism `π : X ⟶ Spec k`, and "of dimension at most one" is
`topologicalKrullDim X ≤ 1`. "Prime to the characteristic" is read with the exponential
characteristic, so it is no condition in characteristic zero. `H^q_étale(X, -)` is the `q`-th
right derived functor of global sections of sheaves of `Λ`-modules on `X_étale`. The connectedness
of `U` is a hypothesis of the source and is kept; the proof does not use it. -/
@[stacks 0GJH "part (1): ℓ prime to char(k)"]
theorem module_finite_cohomology_extensionByZero_of_isFiniteTypeLocallyConstant_of_coprime
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    (hX : topologicalKrullDim X ≤ 1) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [ConnectedSpace U] {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 0 < n) (hℓk : ℓ.Coprime (ringExpChar k))
    (G : EtaleModules.{u, r} Λ U)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      U.smallEtaleTopology Λ G)
    (hGn : ℓ ^ n • 𝟙 G = 0) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj G)) :=
  module_finite_cohomology_extensionByZero_of_isFiniteTypeLocallyConstant Λ π hX j G hG hℓ hn hGn
    (Or.inl hℓk) q

/-- **Stacks Project, Tag 0GJH, part (2).** Let `Λ` be a Noetherian ring, let `k` be an
algebraically closed field, let `X` be a proper scheme over `k` of dimension at most one (proper
implies separated and of finite type), let `j : U ⟶ X` be an open immersion with `U` connected,
let `ℓ` be a prime number, let `n > 0` and let `𝒢` be a finite type, locally constant sheaf of
`Λ`-modules on `U_étale` annihilated by `ℓ ^ n`. Then `H^q_étale(X, j_! 𝒢)` is a finite
`Λ`-module for every `q`.

The encoding is that of part (1),
`module_finite_cohomology_extensionByZero_of_isFiniteTypeLocallyConstant_of_coprime`, with the
coprimality hypothesis replaced by `IsProper π`. -/
@[stacks 0GJH "part (2): X proper over k"]
theorem module_finite_cohomology_extensionByZero_of_isFiniteTypeLocallyConstant_of_isProper
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [IsProper π]
    (hX : topologicalKrullDim X ≤ 1) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [ConnectedSpace U] {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 0 < n) (G : EtaleModules.{u, r} Λ U)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      U.smallEtaleTopology Λ G)
    (hGn : ℓ ^ n • 𝟙 G = 0) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj G)) :=
  module_finite_cohomology_extensionByZero_of_isFiniteTypeLocallyConstant Λ π hX j G hG hℓ hn hGn
    (Or.inr inferInstance) q

end Stacks.EtaleCohomology.TorsionModules

end
