module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniRationalMember
public import StacksFrontier.AlgebraicGeometry.VanishingSystemImmersion.Basic

/-!
# Cutting by a smooth member of the linear system of sections vanishing on a subscheme

Let `k` be an infinite field, `X` a scheme over `k`, `ℒ` an invertible `𝒪_X`-module and `I` a
quasi-coherent sheaf of ideals with closed subscheme `Z`. Suppose that the linear system
`V = V_n ⊆ Γ(X, ℒ^{⊗ n})` of sections vanishing on `Z` generates `ℒ^{⊗ n}` on `X ∖ Z` and that
`X ∖ Z → 𝐏(V)` is an immersion — the conclusion of [Stacks, Tag 0FD5].

For a closed subscheme `T ⊆ X` whose trace `T ∩ (X ∖ Z)` is smooth over `k`, the restriction of
`V` to `T ∩ (X ∖ Z)` satisfies the three hypotheses of [Stacks, Tag 0FD6], so a general member of
`V` cuts `T ∩ (X ∖ Z)` in a scheme smooth over `k`. Here the member is a vector of `V` itself,
chosen off finitely many prescribed hyperplanes.

## Main definitions

* `Stacks.SectionsVanishingOnSubscheme.pullbackSectionsLinear`: pulling back global sections
  along a morphism of `k`-schemes, as a `k`-linear map.
* `Stacks.SectionsVanishingOnSubscheme.cutFamily`: the linear system `V` restricted along a
  morphism to `X ∖ Z`, as a standing situation of [Stacks, Tag 0G47].
* `Stacks.SectionsVanishingOnSubscheme.SmoothOffSupport`: the trace of a closed subscheme of `X`
  on `X ∖ Z` is smooth over `k`.

## Main results

* `Stacks.SectionsVanishingOnSubscheme.generates_cutFamily` and
  `Stacks.SectionsVanishingOnSubscheme.isImmersive_cutFamily`: hypotheses (2) and (3) of
  [Stacks, Tag 0FD6] for the restricted system.
* `Stacks.SectionsVanishingOnSubscheme.exists_smoothOffSupport_sup_zeroScheme`: if `T ∩ (X ∖ Z)`
  is smooth then so is `(T ∩ H_v) ∩ (X ∖ Z)` for a vector `v ∈ V` avoiding finitely many
  hyperplanes.

## References

* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample Stacks.ProjectiveFromSections

universe u

namespace Stacks.SectionsVanishingOnSubscheme

attribute [local instance] Stacks.InvertiblePullback.isInvertibleModule_pullback

/-- An invertible module in the sense of `Stacks.Ample.IsInvertibleModule` is invertible in the
sense of `AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
theorem isInvertible_of_isInvertibleModule {X : Scheme.{u}} (M : X.Modules)
    [h : IsInvertibleModule X M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M := h

attribute [local instance] isInvertible_of_isInvertibleModule

section Linear

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Pulling back global sections along a morphism of schemes over `k`, as a `k`-linear map.** -/
def pullbackSectionsLinear {Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) :
    Stacks.Bertini.globalSections k f M →ₗ[k]
      Stacks.Bertini.globalSections k (g ≫ f) ((Scheme.Modules.pullback g).obj M) where
  toFun s := pullbackGlobalSections g M s
  map_add' s t := map_add (ConcreteCategory.hom (pullbackGlobalSections g M)) s t
  map_smul' c s := by
    refine (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul g M
      (Stacks.Bertini.baseRingHom k f c) s).trans ?_
    have h : g.appTop (Stacks.Bertini.baseRingHom k f c) =
        Stacks.Bertini.baseRingHom k (g ≫ f) c := by
      change g.appTop (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) =
        (g ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)
      rw [Scheme.Hom.comp_appTop]
      rfl
    rw [h]
    rfl

/-- `pullbackSectionsLinear k f g M` sends a global section to its pullback along `g`. -/
@[simp]
theorem pullbackSectionsLinear_apply {Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    (s : Stacks.Bertini.globalSections k f M) :
    pullbackSectionsLinear k f g M s = pullbackGlobalSections g M s :=
  rfl

end Linear

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  {I : X.IdealSheafData} {L : X.Modules} [IsInvertibleModule X L] {m : ℤ}
  [FiniteDimensional k (vanishingSections k f I L m)]

/-! ### The restricted linear system -/

/-- **The linear system `V_n` restricted along a morphism `g : Y ⟶ X ∖ Z`**, as a standing
situation of [Stacks, Tag 0G47]: the scheme is `Y`, the invertible module is the pullback of
`ℒ^{⊗ n}|_{X ∖ Z}`, and a vector of `V_n` gives its pulled-back section. -/
def cutFamily (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (L : X.Modules) [IsInvertibleModule X L] (m : ℤ)
    [FiniteDimensional k (vanishingSections k f I L m)] {Y : Scheme.{u}}
    (g : Y ⟶ (openComplement I).toScheme) :
    Stacks.Bertini.FamilyDivisors.{u, u} where
  k := k
  V := vanishingSections k f I L m
  X := Y
  toBase := g ≫ ((openComplement I).ι ≫ f)
  L := (Scheme.Modules.pullback g).obj (restrictedPow I (L := L) (m := m))
  isInvertible := Stacks.InvertiblePullback.isInvertibleModule_pullback g _
  ψ := (pullbackSectionsLinear k ((openComplement I).ι ≫ f) g
      (restrictedPow I (L := L) (m := m))).comp
    ((pullbackSectionsLinear k f (openComplement I).ι (tensorPowModule X L m)).comp
      (vanishingSections k f I L m).subtype)
  basis := Module.finBasis k _

/-- The section of the restricted system given by a vector `v` of `V_n` is the pullback along `g`
of the restriction of `v` to `X ∖ Z`. -/
theorem cutFamily_sectionOf {Y : Scheme.{u}} (g : Y ⟶ (openComplement I).toScheme)
    (v : vanishingSections k f I L m) :
    (cutFamily k f I L m g).sectionOf v =
      pullbackGlobalSections g (restrictedPow I (L := L) (m := m))
        (restrictSection I (v : Stacks.Bertini.globalSections k f (tensorPowModule X L m))) :=
  rfl

/-- **Hypothesis (2) of [Stacks, Tag 0FD6] for the restricted system**: off `Z` some member of
`V_n` does not vanish at the image of each point of `Y`, so the pulled-back members generate. -/
theorem generates_cutFamily {Y : Scheme.{u}} (g : Y ⟶ (openComplement I).toScheme)
    (h : GeneratesOffSupport k f I L m) : (cutFamily k f I L m g).Generates := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun (y : Y) => ?_
  obtain ⟨v, hv⟩ := Stacks.StalkwiseGeneration.exists_mem_nvOpen_of_span_eq_top
    (tensorPowModule X L m)
    (fun v : vanishingSections k f I L m =>
      (v : Stacks.Bertini.globalSections k f (tensorPowModule X L m)))
    ((openComplement I).ι (g y)) (h _ (g y).2)
  refine ⟨v, ?_⟩
  have hy : y ∈ nvOpen ((Scheme.Modules.pullback g).obj (restrictedPow I (L := L) (m := m)))
      (pullbackGlobalSections g _ (pullbackGlobalSections (openComplement I).ι _
        (v : Stacks.Bertini.globalSections k f (tensorPowModule X L m)))) := by
    rw [Stacks.RatioPullback.nvOpen_pullbackGlobalSections]
    exact (congrArg (g y ∈ ·) (Stacks.RatioPullback.nvOpen_pullbackGlobalSections
      (openComplement I).ι (tensorPowModule X L m) _)).mpr hv
  exact hy

/-- **Hypothesis (3) of [Stacks, Tag 0FD6] for the restricted system**: if `g` is an immersion
then so is `Y → X ∖ Z → 𝐏(V_n)`, and that composite is the morphism of the restricted system. -/
theorem isImmersive_cutFamily {Y : Scheme.{u}} (g : Y ⟶ (openComplement I).toScheme)
    [IsImmersion g] (h : GeneratesOffSupport k f I L m)
    (himm : ∀ (N : ℕ) (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m)),
      IsImmersion (toProjectiveSpaceOfVanishingSections k f b h))
    (N : ℕ) (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m)) :
    (cutFamily k f I L m g).IsImmersive b
      ((cutFamily k f I L m g).generatesBy_basis (generates_cutFamily g h) b) := by
  have h1 := himm N b
  rw [toProjectiveSpaceOfVanishingSections_eq] at h1
  have h2 : IsImmersion (g ≫ toProjectiveSpaceOfModule b (restrictedBasisSection k f I b)
      (generatesStalks_restrictedBasisSection k f I b h) ((openComplement I).ι ≫ f)) :=
    inferInstance
  rw [toProjectiveSpaceOfModule, ← Category.assoc,
    comp_toProjectiveSpaceOver_self g (restrictedBasisSection k f I b)
      (generatesStalks_restrictedBasisSection k f I b h) ((openComplement I).ι ≫ f)
      (by exact (cutFamily k f I L m g).generatesBy_basis (generates_cutFamily g h) b)] at h2
  exact h2

/-! ### Smoothness off the support, and the Bertini step -/

/-- **The trace of the closed subscheme `T` on `X ∖ Z` is smooth over `k`.** -/
def SmoothOffSupport {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (T : X.IdealSheafData) : Prop :=
  Smooth ((T.comap (openComplement I).ι).subschemeι ≫ ((openComplement I).ι ≫ f))

/-- `X ∖ Z` itself is smooth over `k` when `X` is. -/
theorem smoothOffSupport_bot {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) [Smooth f] : SmoothOffSupport f I (⊥ : X.IdealSheafData) := by
  rw [SmoothOffSupport, Scheme.IdealSheafData.comap_bot]
  have : IsIso (⊥ : (openComplement I).toScheme.IdealSheafData).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).mpr rfl
  infer_instance

/-- **The Bertini step for the linear system of sections vanishing on `Z`.** Over an infinite
field, if `V_n` generates `ℒ^{⊗ n}` off `Z`, every basis of `V_n` gives an immersion of `X ∖ Z`,
and the trace of `T` on `X ∖ Z` is smooth over `k`, then for every finite family of nonzero linear
forms `ℓ` on `V_n` there is `v ∈ V_n` with `ℓ(v) ≠ 0` for each of them such that the trace of
`T ∩ Z(v)` on `X ∖ Z` is smooth over `k` as well. -/
theorem exists_smoothOffSupport_sup_zeroScheme [Infinite k] (T : X.IdealSheafData)
    (hT : SmoothOffSupport f I T) (h : GeneratesOffSupport k f I L m)
    (himm : ∀ (N : ℕ) (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m)),
      IsImmersion (toProjectiveSpaceOfVanishingSections k f b h))
    {ι : Type*} [Finite ι] (ℓ : ι → vanishingSections k f I L m →ₗ[k] k) (hℓ : ∀ c, ℓ c ≠ 0) :
    ∃ v : vanishingSections k f I L m,
      SmoothOffSupport f I (T ⊔ Stacks.Divisors.zeroScheme X (tensorPowModule X L m)
        (v : Stacks.Bertini.globalSections k f (tensorPowModule X L m))) ∧
      ∀ c, ℓ c v ≠ 0 := by
  set U := openComplement I
  set T' := T.comap U.ι
  set g := T'.subschemeι
  set D := cutFamily k f I L m g
  have : Smooth D.toBase := hT
  have : Infinite D.k := ‹Infinite k›
  obtain ⟨v, hv, hℓv⟩ := D.exists_smooth_zeroScheme_sectionOf (generates_cutFamily g h)
    (fun N b => isImmersive_cutFamily g h himm N b) ℓ hℓ
  let v' : vanishingSections k f I L m := v
  refine ⟨v', ?_, hℓv⟩
  set s : Γ(tensorPowModule X L m, ⊤) :=
    (v' : Stacks.Bertini.globalSections k f (tensorPowModule X L m))
  set E := Stacks.Divisors.zeroScheme X (tensorPowModule X L m) s
  have hdiv : Stacks.Divisors.zeroScheme D.X D.L (D.sectionOf v) = (E.comap U.ι).comap g := by
    show Stacks.Divisors.zeroScheme _ _
      (pullbackGlobalSections g _ (pullbackGlobalSections U.ι _ s)) = _
    rw [Stacks.Divisors.zeroScheme_pullback, Stacks.Divisors.zeroScheme_pullback]
  rw [hdiv] at hv
  obtain ⟨e', he'⟩ := Stacks.ChernCap42.exists_iso_comap_sup T' (E.comap U.ι) g (Iso.refl _)
    (by simp [g])
  rw [SmoothOffSupport, Scheme.IdealSheafData.comap_sup]
  have : Smooth ((((E.comap U.ι).comap g).subschemeι ≫ g) ≫ (U.ι ≫ f)) := by
    rw [Category.assoc]; exact hv
  have heq : (T' ⊔ E.comap U.ι).subschemeι ≫ (U.ι ≫ f) =
      e'.inv ≫ (((E.comap U.ι).comap g).subschemeι ≫ g) ≫ (U.ι ≫ f) := by
    rw [← he']
    simp
  rw [heq]
  infer_instance

end Stacks.SectionsVanishingOnSubscheme

end
