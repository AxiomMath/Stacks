module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardBound
import StacksCore.Tactic.StacksAttribute

/-!
# The right adjoint of `Rf_*` preserves bounded-below objects, for algebraic spaces

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated algebraic spaces and `a` the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` (Stacks 0E55). There is an integer `N` such
that `a` carries an object in degrees `≥ c` to an object in degrees `≥ c - N`; in particular `a`
maps `D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)` (Stacks 0E56).

The proof is the source's: by Stacks 08FA, `Rf_*` raises upper bounds by at most `N`, so for
`T = τ_{≤ c - N - 1} a(K)` every map `Rf_*T ⟶ K` vanishes, hence so does `T ⟶ a(K)`.

## Main results

* `AlgebraicGeometry.Space.exists_isLE_derivedModulePushforward_obj`: the uniform bound of
  Stacks 08FA, for arbitrary upper bounds.
* `AlgebraicGeometry.Space.isGE_quasicoherentDerivedRightAdjoint_obj`: the bound for `a`.
* `AlgebraicGeometry.Space.quasicoherentDerivedRightAdjoint_boundedBelow`: **Stacks 0E56**.

## References

* [Stacks Project, Tag 0E56](https://stacks.math.columbia.edu/tag/0E56)
* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The uniform bound of Stacks 08FA.** Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces with `Y` quasi-compact. There is an integer `N`
such that `Rf_*E` lies in degrees `≤ c + N` for every `E` in `D_QCoh(𝒪_X)` in degrees `≤ c`. -/
theorem exists_isLE_derivedModulePushforward_obj {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsQuasiCompactSpace B S hS Y.1) :
    ∃ N : ℤ, ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), QcohDerived B S hS X E →
      ∀ c : ℤ, E.IsLE c → ((derivedModulePushforward B S hS f).obj E).IsLE (c + N) := by
  obtain ⟨N, hN⟩ := exists_pushforwardRaisesBoundBy_baseChange B S hS f hfqc hfqs hY
  refine ⟨N, fun E hE c hEc => ?_⟩
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso_modules B S hS E
  have hqc : ∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite := by
    rw [← qcohDerived_Q_obj_iff]
    exact (QcohDerived B S hS X).prop_of_iso e hE
  have hc : (DerivedCategory.Q.obj I).IsLE c := DerivedCategory.TStructure.t.isLE_of_iso e c
  have hle := hN Y X (𝟙 Y) (𝟙 X) f IsPullback.of_id_fst I hI hqc c hc
  obtain ⟨e'⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS f
    (derivedModulePushforward B S hS f) (derivedModulePushforwardUnit B S hS f) I hI
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((derivedModulePushforward B S hS f).mapIso e ≪≫ e').symm (c + N)

variable (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)

/-- **The right adjoint of `Rf_*` lowers lower bounds by at most `N`**, for `N` a bound by which
`Rf_*` raises upper bounds on `D_QCoh(𝒪_X)`. -/
theorem isGE_quasicoherentDerivedRightAdjoint_obj (N : ℤ)
    (hN : ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), QcohDerived B S hS X E →
      ∀ c : ℤ, E.IsLE c → ((derivedModulePushforward B S hS f).obj E).IsLE (c + N))
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) (c : ℤ) (hK : K.obj.IsGE c) :
    ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj.IsGE (c - N) := by
  have hfqc := isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom
  have hfqs := isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom
  let a := quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs
  let adj := quasicoherentDerivedRightAdjointAdjunction hZ f hXqc hXqs hYqs hfqc hfqs
  obtain ⟨d, hd⟩ : ∃ d : ℤ, c - N = d + 1 := ⟨c - N - 1, by omega⟩
  let T : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
    ⟨(DerivedCategory.TStructure.t.truncLE d).obj (a.obj K).obj,
      qcohDerived_truncLE _ d (a.obj K).property⟩
  have hRLE : ((derivedModulePushforward B S hS f).obj T.obj).IsLE (d + N) :=
    hN T.obj T.property d inferInstance
  have hzero : ∀ g₁ g₂ : (quasicoherentDerivedPushforward B S hS f hfqc hfqs).obj T ⟶ K,
      g₁ = g₂ := by
    intro g₁ g₂
    refine ObjectProperty.hom_ext _ ?_
    rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g₁.hom (d + N) c (by omega) hRLE hK,
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g₂.hom (d + N) c (by omega) hRLE hK]
  have hsub : ∀ g₁ g₂ : T ⟶ a.obj K, g₁ = g₂ := fun g₁ g₂ =>
    (adj.homEquiv T K).symm.injective (hzero _ _)
  have hι : (DerivedCategory.TStructure.t.truncLTι (d + 1)).app (a.obj K).obj = 0 :=
    congrArg InducedCategory.Hom.hom
      (hsub (ObjectProperty.homMk
        ((DerivedCategory.TStructure.t.truncLEι d).app (a.obj K).obj))
        (ObjectProperty.homMk 0))
  rw [hd]
  refine (DerivedCategory.TStructure.t.isGE_iff_orthogonal d (d + 1) rfl _).2 fun Z g _ => ?_
  rw [← DerivedCategory.TStructure.t.liftTruncLT_ι g d (d + 1) rfl, hι, comp_zero]

/-- **Stacks 0E56.** Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated
algebraic spaces and `a` the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Then `a` maps
`D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)`. In fact there is an integer `N` such that `H^i(K) = 0`
for `i ≤ c` implies `H^i(a(K)) = 0` for `i ≤ c - N`. -/
theorem quasicoherentDerivedRightAdjoint_boundedBelow (hYqc : IsQuasiCompactSpace B S hS Y.1) :
    (∀ K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2,
      DerivedCategoryB.IsBoundedBelow K.obj →
        DerivedCategoryB.IsBoundedBelow
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj) ∧
    ∃ N : ℤ, ∀ (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) (c : ℤ),
      (∀ i : ℤ, i ≤ c → IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj)) →
        ∀ i : ℤ, i ≤ c - N → IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedModulePushforward_obj f
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom) hYqc
  have key : ∀ (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) (c : ℤ),
      (∀ i : ℤ, i < c → IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj)) →
        ∀ i : ℤ, i < c - N → IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj) := by
    intro K c hK i hi
    have hGE : K.obj.IsGE c := (DerivedCategory.isGE_iff _ _).2 hK
    have := isGE_quasicoherentDerivedRightAdjoint_obj hZ f hXqc hXqs hYqs N hN K c hGE
    exact DerivedCategory.isZero_of_isGE _ (c - N) i hi
  refine ⟨fun K ⟨n₀, hn₀⟩ => ⟨n₀ - N, key K n₀ hn₀⟩, N, fun K c hK i hi =>
    key K (c + 1) (fun j hj => hK j (by omega)) i (by omega)⟩

end AlgebraicGeometry.Space

end
