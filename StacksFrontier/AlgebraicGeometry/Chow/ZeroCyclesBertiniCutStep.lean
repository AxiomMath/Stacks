module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesBertiniChainDefs
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGeneratingSystem

/-!
# One step of the iterated Bertini cut in the proof of Stacks 0FH5

Let `X` be a smooth proper scheme over an infinite field `k`, `ℒ` an invertible `𝒪_X`-module and
`I` a quasi-coherent sheaf of ideals with closed subscheme `Z`, and suppose that the linear system
`V_n ⊆ Γ(X, ℒ^{⊗ n})` of sections vanishing on `Z` generates `ℒ^{⊗ n}` on `X ∖ Z` and embeds
`X ∖ Z` into `𝐏(V_n)`. Let `T ⊆ X` be a closed subscheme whose trace on `X ∖ Z` is smooth and
all of whose points off `Z` have `δ`-dimension at most `e`.

Then a general `v ∈ V_n`, chosen outside any prescribed finite family of proper subspaces, has
three properties: the trace of `T ∩ Z(v)` on `X ∖ Z` is smooth, `v` does not vanish at the generic
points of `T` off `Z`, and every point of `T ∩ Z(v)` off `Z` has `δ`-dimension at most `e - 1`.
Moreover `V_n` is finite dimensional, and the members of `V_n` vanishing at a point off `Z` form a
proper subspace.

## Main results

* `Stacks.Chow.BertiniChain.finiteDimensional_vanishingSections`: `V_n` is finite dimensional.
* `Stacks.Chow.BertiniChain.vanishingAtSubmodule_ne_top`: off `Z`, not every member of `V_n`
  vanishes at a given point.
* `Stacks.Chow.BertiniChain.exists_cut_step`: one step of the iterated Bertini cut.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Stacks.Ample
open Stacks.SectionsVanishingOnSubscheme

universe u

namespace Stacks.Chow.BertiniChain

attribute [local instance] Stacks.SectionsVanishingOnSubscheme.isInvertible_of_isInvertibleModule

/-- The two ring maps `k → Γ(X, 𝒪_X)` induced by the structure morphism, through `appTop` and
through `appLE ⊤ ⊤`, agree. -/
theorem baseRingHom_apply_eq (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (c : k) : Stacks.Bertini.baseRingHom k f c =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c := by
  rw [Stacks.Bertini.baseRingHom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

/-- The global sections of an `𝒪_X`-module as a `k`-vector space in the spelling of
`Stacks.Bertini.globalSections` and in that of `AlgebraicGeometry.globalSectionsOverField` are
the same vector space. -/
def globalSectionsLinearEquiv (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (F : X.Modules) :
    Stacks.Bertini.globalSections k f F ≃ₗ[k] globalSectionsOverField k f F where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' c x := by
    let x' : F.val.obj (op ⊤) := x
    exact congrArg (fun a => a • x') (baseRingHom_apply_eq k f c)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The global sections of a power of an invertible module on a proper `k`-scheme which vanish on
a closed subscheme form a finite dimensional `k`-vector space. -/
theorem finiteDimensional_vanishingSections (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (I : X.IdealSheafData) (L : X.Modules)
    [IsInvertibleModule X L] (m : ℤ) : FiniteDimensional k (vanishingSections k f I L m) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPowModule X L m) := isInvertibleModule_tensorPowModule X L m
  have : (tensorPowModule X L m).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X _
  have : FiniteDimensional k (Stacks.Bertini.globalSections k f (tensorPowModule X L m)) :=
    LinearEquiv.finiteDimensional (globalSectionsLinearEquiv k f _).symm
  infer_instance

/-- A global section of an invertible module vanishes at `y`, i.e. `y` lies outside its
nonvanishing open, exactly when its germ at `y` lies in `𝔪_y · M_y`. -/
theorem notMem_nvOpen_iff {X : Scheme.{u}} (M : X.Modules) [IsInvertibleModule X M]
    (s : Γ(M, ⊤)) (y : X) :
    y ∉ Stacks.ProjectiveFromSections.nvOpen M s ↔
      (M.presheaf.Γgerm y).hom s ∈ Stacks.StalkwiseGeneration.maximalSmulRing M y := by
  rw [Stacks.ProjectiveFromSections.nvOpen, Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff,
    not_not]
  rfl

/-- The members of `V_n` vanishing at a point `y`, that is, whose germ `s_y` lies in
`𝔪_y · ℒ^{⊗ n}_y`, as a `k`-subspace. -/
def vanishingAtSubmodule (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (L : X.Modules) [IsInvertibleModule X L] (m : ℤ) (y : X) :
    Submodule k (vanishingSections k f I L m) where
  carrier := {v | y ∉ Stacks.ProjectiveFromSections.nvOpen (tensorPowModule X L m)
    ((v : Stacks.Bertini.globalSections k f (tensorPowModule X L m)) : Γ(tensorPowModule X L m, ⊤))}
  add_mem' {_ _} ha hb := (notMem_nvOpen_iff _ _ y).2
    ((germSubmodule k f (I := I) (L := L) (m := m) y
      (Stacks.StalkwiseGeneration.maximalSmulRing _ y)).add_mem
      ((notMem_nvOpen_iff _ _ y).1 ha) ((notMem_nvOpen_iff _ _ y).1 hb))
  zero_mem' := (notMem_nvOpen_iff _ _ y).2
    (germSubmodule k f (I := I) (L := L) (m := m) y
      (Stacks.StalkwiseGeneration.maximalSmulRing _ y)).zero_mem
  smul_mem' c _ ha := (notMem_nvOpen_iff _ _ y).2
    ((germSubmodule k f (I := I) (L := L) (m := m) y
      (Stacks.StalkwiseGeneration.maximalSmulRing _ y)).smul_mem c
      ((notMem_nvOpen_iff _ _ y).1 ha))

/-- Off the support of `I`, if `V_n` generates `ℒ^{⊗ n}` there, not every member of `V_n` vanishes
at a given point. -/
theorem vanishingAtSubmodule_ne_top (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (L : X.Modules) [IsInvertibleModule X L]
    (m : ℤ) (h : GeneratesOffSupport k f I L m) {y : X} (hy : y ∉ I.support) :
    vanishingAtSubmodule k f I L m y ≠ ⊤ := by
  obtain ⟨v, hv⟩ := Stacks.StalkwiseGeneration.exists_mem_nvOpen_of_span_eq_top
    (tensorPowModule X L m)
    (fun v : vanishingSections k f I L m =>
      ((v : Stacks.Bertini.globalSections k f (tensorPowModule X L m)) :
        Γ(tensorPowModule X L m, ⊤))) y (h y hy)
  intro htop
  have : v ∈ vanishingAtSubmodule k f I L m y := htop ▸ Submodule.mem_top
  exact this hv

/-- **One step of the iterated Bertini cut.** If the trace of `T` on `X ∖ Z` is smooth and the
points of `T` off `Z` have `δ`-dimension at most `e`, then outside any finite family of proper
subspaces of `V_n` there is `v` such that the trace of `T ∩ Z(v)` on `X ∖ Z` is smooth, the points
of `T ∩ Z(v)` off `Z` have `δ`-dimension at most `e - 1`, and `v` does not vanish at the generic
points of `T` off `Z`. -/
theorem exists_cut_step {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f] (I : X.IdealSheafData) (L : X.Modules)
    [IsInvertibleModule X L] (m : ℤ) [FiniteDimensional k (vanishingSections k f I L m)]
    (T : X.IdealSheafData) (hT : SmoothOffSupport f I T) (e : ℤ) (hdim : DimBoundOff f I T e)
    (h : GeneratesOffSupport k f I L m)
    (himm : ∀ (N : ℕ) (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m)),
      IsImmersion (toProjectiveSpaceOfVanishingSections k f b h))
    {ι : Type*} [Finite ι] (P : ι → Submodule k (vanishingSections k f I L m))
    (hP : ∀ c, P c ≠ ⊤) :
    ∃ v : vanishingSections k f I L m, (∀ c, v ∉ P c) ∧
      SmoothOffSupport f I (T ⊔ Stacks.Divisors.zeroScheme X (tensorPowModule X L m)
        ((v : Stacks.Bertini.globalSections k f (tensorPowModule X L m)) :
          Γ(tensorPowModule X L m, ⊤))) ∧
      DimBoundOff f I (T ⊔ Stacks.Divisors.zeroScheme X (tensorPowModule X L m)
        ((v : Stacks.Bertini.globalSections k f (tensorPowModule X L m)) :
          Γ(tensorPowModule X L m, ⊤))) (e - 1) ∧
      NonvanishingAtGenericOff I T (tensorPowModule X L m)
        ((v : Stacks.Bertini.globalSections k f (tensorPowModule X L m)) :
          Γ(tensorPowModule X L m, ⊤)) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace T.subscheme := QuasiCompact.compactSpace_of_compactSpace T.subschemeι
  have : IsLocallyNoetherian T.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (T.subschemeι ≫ f)
  have : IsNoetherian T.subscheme := {}
  let G : Set T.subscheme := {η | η ∈ genericPoints T.subscheme ∧ T.subschemeι η ∉ I.support}
  have : Finite G := ((genericPoints.finite
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).subset
      fun η hη => hη.1).to_subtype
  let Q : ι ⊕ G → Submodule k (vanishingSections k f I L m) :=
    Sum.elim P fun η => vanishingAtSubmodule k f I L m (T.subschemeι η.1)
  have hQ : ∀ c, Q c ≠ ⊤ := by
    rintro (c | η)
    · exact hP c
    · exact vanishingAtSubmodule_ne_top k f I L m h η.2.2
  choose ℓ hℓ hQℓ using fun c => (Q c).exists_le_ker_of_lt_top (hQ c).lt_top
  obtain ⟨v, hsmooth, hv⟩ := exists_smoothOffSupport_sup_zeroScheme T hT h himm ℓ hℓ
  have hvQ : ∀ c, v ∉ Q c := fun c hc => hv c (LinearMap.mem_ker.1 (hQℓ c hc))
  set s : Γ(tensorPowModule X L m, ⊤) :=
    ((v : Stacks.Bertini.globalSections k f (tensorPowModule X L m)) :
      Γ(tensorPowModule X L m, ⊤))
  have hnv : NonvanishingAtGenericOff I T (tensorPowModule X L m) s := fun η hη hηI =>
    Classical.byContradiction (hvQ (Sum.inr ⟨η, hη, hηI⟩))
  refine ⟨v, fun c => hvQ (Sum.inl c), hsmooth, ?_, hnv⟩
  intro y hy hyI
  rw [Scheme.IdealSheafData.support_sup] at hy
  obtain ⟨hyT, hyZ⟩ := hy
  obtain ⟨w, rfl⟩ : y ∈ Set.range T.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  set η := (genericPoints.ofComponent ⟨irreducibleComponent w,
    irreducibleComponent_mem_irreducibleComponents w⟩).1
  have hηgen : η ∈ genericPoints T.subscheme := (genericPoints.ofComponent _).2
  have hsp : η ⤳ w := (genericPoints.isGenericPoint_ofComponent _).specializes
    mem_irreducibleComponent
  have hsp' : T.subschemeι η ⤳ T.subschemeι w := hsp.map T.subschemeι.continuous
  by_cases hηw : η = w
  · exfalso
    rw [← hηw] at hyZ hyI
    exact AlgebraicGeometry.notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen _ s
      (hnv η hηgen hyI) (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2 hyZ)
  · have hne : T.subschemeι w ≠ T.subschemeι η := fun he =>
      hηw (T.subschemeι.isClosedEmbedding.injective he).symm
    have hηI : T.subschemeι η ∉ I.support := fun hm =>
      hyI (hsp'.mem_closed I.support.isClosed hm)
    have hηT : T.subschemeι η ∈ T.support := by
      show T.subschemeι η ∈ (T.support : Set X)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨η, rfl⟩
    have h1 := hdim _ hηT hηI
    have h2 := relativeDimension_lt_of_mem_closure_of_ne (fieldChowSituation k) f
      (specializes_iff_mem_closure.1 hsp') hne
    omega

end Stacks.Chow.BertiniChain

end
