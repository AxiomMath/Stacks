module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExtCyclesBoundaries
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianExact
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneFlasqueVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of an abelian sheaf supported on a closed subset of small dimension

Let `X` be a Noetherian topological space, let `Z ⊆ X` be a closed subset of Krull dimension at
most `k`, and let `ℰ` be an abelian sheaf on `X` whose stalks vanish at every point outside `Z`.
Then `H^p(X, ℰ) = 0` for every `p > k`. This is Grothendieck's vanishing theorem
([Stacks, Tag 02UZ]) applied on `Z`, transported to `X` along the pushforward of the closed
inclusion: `ℰ` is the pushforward of a sheaf `ℰ'` on `Z` ([Stacks, Tag 01AX]), the pushforward
of an injective resolution of `ℰ'` is a flasque resolution of `ℰ`, and flasque sheaves are
acyclic, so both cohomologies are computed by the same complex of global sections.

## Main results

* `Stacks.SupportedVanishing.homConstAddEquiv`: morphisms out of the constant sheaf `ℤ` are
  global sections.
* `Stacks.SupportedVanishing.subsingleton_ext_of_isFlasque`: a flasque abelian sheaf has no
  higher cohomology.
* `Stacks.SupportedVanishing.subsingleton_ext_of_isZero_stalk`: the vanishing above the
  dimension of the support.

## Implementation notes

Cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext` groups out of the constant sheaf
`ℤ`. The acyclicity of flasque sheaves is proved here directly in that spelling, by
embedding a flasque sheaf in an injective one: the quotient is flasque and global sections
are exact on the resulting short exact sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Abelian

universe u

namespace Stacks.SupportedVanishing

variable {X : TopCat.{u}}

/-- The constant sheaf `ℤ` on a space. -/
abbrev constZ (X : TopCat.{u}) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))

/-- Morphisms out of the constant sheaf `ℤ` are global sections. -/
def homConstAddEquiv (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (constZ X ⟶ B) ≃+ B.obj.obj (op ⊤) :=
  ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    Limits.isTerminalTop).homAddEquiv _ B).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- The identification of morphisms out of `ℤ` with global sections is natural. -/
theorem homConstAddEquiv_comp {B B' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : constZ X ⟶ B) (g : B ⟶ B') :
    homConstAddEquiv B' (φ ≫ g) = g.hom.app (op ⊤) (homConstAddEquiv B φ) := by
  simp only [homConstAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_naturality_right]
  rfl

/-- An injective hull `F ⟶ I` and its cokernel form a short exact sequence. -/
theorem shortExact_injective_ι {C : Type*} [Category C] [Abelian C] [EnoughInjectives C] (F : C) :
    (ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

/-- Pushing a complex of sheaves forward along `i` transports the property that every cycle of
global sections in degree `n + 1` is a boundary. -/
theorem forall_cycle_boundary_pushforward {Y : TopCat.{u}} (i : Y ⟶ X)
    (Φ : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hΦ : Φ = closedInclusionPushforward Y X i) [Φ.PreservesZeroMorphisms]
    (L : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ℕ) (n : ℕ)
    (hL : ∀ φ : constZ Y ⟶ L.X (n + 1), φ ≫ L.d (n + 1) (n + 2) = 0 →
      ∃ ψ : constZ Y ⟶ L.X n, ψ ≫ L.d n (n + 1) = φ)
    (φ : constZ X ⟶ ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).X (n + 1))
    (hφ : φ ≫ ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).d (n + 1) (n + 2) = 0) :
    ∃ ψ : constZ X ⟶ ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).X n,
      ψ ≫ ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).d n (n + 1) = φ := by
  have hsurj :=
    (homConstAddEquiv (((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).X n)).surjective
  subst hΦ
  let φZ := (homConstAddEquiv (L.X (n + 1))).symm (homConstAddEquiv _ φ :)
  have hφZ' : homConstAddEquiv (L.X (n + 1)) φZ = (homConstAddEquiv _ φ :) :=
    AddEquiv.apply_symm_apply _ _
  have hφZ : φZ ≫ L.d (n + 1) (n + 2) = 0 := by
    apply (homConstAddEquiv _).injective
    rw [homConstAddEquiv_comp, hφZ', map_zero]
    have h := congrArg (homConstAddEquiv _) hφ
    rwa [homConstAddEquiv_comp, map_zero] at h
  obtain ⟨ψZ, hψZ⟩ := hL φZ hφZ
  obtain ⟨ψ, hψ⟩ := hsurj (homConstAddEquiv (L.X n) ψZ)
  refine ⟨ψ, (homConstAddEquiv _).injective ?_⟩
  rw [homConstAddEquiv_comp, hψ]
  have h := congrArg (homConstAddEquiv _) hψZ
  rwa [homConstAddEquiv_comp, hφZ'] at h

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **Flasque abelian sheaves are acyclic**: `H^{k+1}(X, ℱ) = 0` for a flasque `ℱ`. -/
@[sga "2 I 2.12" "special case", sga "4 V 4.6" "partial"]
theorem subsingleton_ext_of_isFlasque (k : ℕ) :
    ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [TopCat.Sheaf.IsFlasque F],
      Subsingleton (Ext.{u} (constZ X) F (k + 1)) := by
  have : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  have hU (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [TopCat.Sheaf.IsFlasque F] :
      TopCat.Sheaf.IsFlasque (Injective.under F) :=
    @Stacks.Cohomology.CechOne.isFlasque_of_injective X (Injective.under F)
      (Injective.injective_under F)
  induction k with
  | zero =>
    intro F _
    have hS := shortExact_injective_ι F
    refine subsingleton_of_forall_eq 0 fun z => ?_
    obtain ⟨z₃, hz₃⟩ := Ext.covariant_sequence_exact₁ (constZ X) hS z
      ((Ext.subsingleton_of_injective (constZ X) (Injective.under F) 0).elim _ _) rfl
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (constZ X) _).2 z₃
    obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective _).1
      (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) hS) (homConstAddEquiv _ g)
    have hg : (homConstAddEquiv _).symm t ≫ cokernel.π (Injective.ι F) = g :=
      (homConstAddEquiv _).injective <| by
        rwa [homConstAddEquiv_comp, AddEquiv.apply_symm_apply]
    rw [← hz₃, ← hg, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
      Ext.comp_zero]
  | succ k ih =>
    intro F _
    have hS := shortExact_injective_ι F
    have := hU F
    have : TopCat.Sheaf.IsFlasque (cokernel (Injective.ι F)) :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    exact Stacks.ExtCycles.subsingleton_ext_X₁ (constZ X) hS (@ih _ this)
      (Ext.subsingleton_of_injective (constZ X) (Injective.under F) (k + 1))

/-- On a Noetherian space of dimension at most `k`, every cycle of degree `n + 1 > k` in the
global sections of an injective resolution is a boundary. -/
theorem cycle_boundary_of_topologicalKrullDim_le (Y : TopCat.{u}) [NoetherianSpace Y] {k : ℕ}
    (hdim : topologicalKrullDim Y ≤ k)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
    {E' : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}} (J : InjectiveResolution E')
    (n : ℕ) (hn : k < n + 1) (φ : constZ Y ⟶ J.cocomplex.X (n + 1))
    (hφ : φ ≫ J.cocomplex.d (n + 1) (n + 2) = 0) :
    ∃ ψ : constZ Y ⟶ J.cocomplex.X n, ψ ≫ J.cocomplex.d n (n + 1) = φ :=
  (Stacks.ExtCycles.subsingleton_ext_iff_forall_cycle_boundary_of_isLimit
    (constZ Y) J.cocomplex (hw := J.ι_f_zero_comp_complex_d) J.isLimitKernelFork
    J.cocomplex_exactAt_succ (fun _ _ => Ext.subsingleton_of_injective _ _ _) n).1
    (Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
      (X := Y) hdim hn E') φ hφ

/-- **Cohomology of a sheaf supported on a closed subset vanishes above its dimension.** Let
`X` be a Noetherian space, `Z ⊆ X` a closed subset of Krull dimension at most `k` and `ℰ` an
abelian sheaf on `X` whose stalks vanish outside `Z`. Then `H^{n+1}(X, ℰ) = 0` whenever
`k < n + 1`. -/
theorem subsingleton_ext_of_isZero_stalk [NoetherianSpace X] (Z : Set X) (hZ : IsClosed Z)
    {k : ℕ} (hdim : topologicalKrullDim Z ≤ k)
    (E : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hE : ∀ x : X, x ∉ Z → IsZero (TopCat.Presheaf.stalk E.obj x)) (n : ℕ) (hn : k < n + 1) :
    Subsingleton (Ext.{u} (constZ X) E (n + 1)) := by
  let habX : Abelian (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  let Zt : TopCat.{u} := TopCat.of Z
  let habZ : Abelian (Sheaf (Opens.grothendieckTopology Zt) AddCommGrpCat.{u}) := inferInstance
  let i : Zt ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hi : Topology.IsClosedEmbedding i.hom := hZ.isClosedEmbedding_subtypeVal
  obtain ⟨E₀, ⟨e⟩⟩ :=
    (Stacks.ClosedImmersion.essImage_closedInclusionPushforward_iff_forall_stalk_isZero i hi
      E).2 (fun x hx => hE x (fun hxZ => hx ⟨⟨x, hxZ⟩, rfl⟩))
  let E' : Sheaf (Opens.grothendieckTopology Zt) AddCommGrpCat.{u} := E₀
  let Φ : Sheaf (Opens.grothendieckTopology Zt) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    closedInclusionPushforward Zt X i
  let e' : Φ.obj E' ≅ E := e
  have hex := Stacks.ClosedImmersion.exactFunctor_closedInclusionPushforward i hi
  have : PreservesFiniteLimits Φ := hex.1
  have : PreservesFiniteColimits Φ := hex.2
  have : EnoughInjectives (Sheaf (Opens.grothendieckTopology Zt) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  have : HasExt.{u} (Sheaf (Opens.grothendieckTopology Zt) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  let J := injectiveResolution E'
  have hJ := cycle_boundary_of_topologicalKrullDim_le Zt (k := k) hdim J n hn
  let K := (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  have hKexact : ∀ q : ℕ, K.ExactAt (q + 1) := fun q =>
    (HomologicalComplex.exactAt_iff' K q (q + 1) (q + 2) (by simp) (by simp)).2
      ((J.exact_succ q).map Φ)
  have hKacyc : ∀ q k : ℕ, Subsingleton (Ext.{u} (constZ X) (K.X q) (k + 1)) := fun q k =>
    have : TopCat.Sheaf.IsFlasque (J.cocomplex.X q) :=
      @Stacks.Cohomology.CechOne.isFlasque_of_injective Zt (J.cocomplex.X q) (J.injective q)
    have : TopCat.Sheaf.IsFlasque (K.X q) :=
      TopCat.Sheaf.IsFlasque.pushforward_isFlasque (J.cocomplex.X q) i
    subsingleton_ext_of_isFlasque k (K.X q)
  have hlim : IsLimit (KernelFork.ofι (f := K.d 0 1) (Φ.map (J.ι.f 0))
      (by rw [show K.d 0 1 = Φ.map (J.cocomplex.d 0 1) from rfl, ← Φ.map_comp,
        J.ι_f_zero_comp_complex_d, Φ.map_zero])) :=
    KernelFork.mapIsLimit _ J.isLimitKernelFork Φ
  have hX := (Stacks.ExtCycles.subsingleton_ext_iff_forall_cycle_boundary_of_isLimit
    (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (constZ X) K hlim hKexact hKacyc
    n).2 (forall_cycle_boundary_pushforward i Φ rfl J.cocomplex n hJ)
  exact Stacks.ExtCycles.subsingleton_ext_of_iso
    (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (constZ X) e' hX

end Stacks.SupportedVanishing

end
