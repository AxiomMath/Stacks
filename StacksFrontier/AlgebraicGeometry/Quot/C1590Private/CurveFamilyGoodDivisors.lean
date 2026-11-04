module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePositivePower.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafGeneral
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ZeroSchemeOpenNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallySeparatedOverBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGeneratingSystem
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeChart
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.TensorSectionProduct.Basic

/-!
# Good divisors on the closed fibres of a family of curves

Let `X ⟶ S` be a family of curves and `s` a closed point of `S`, with fibre `X_s` presented by a
scheme `V`. This file shows that `V` carries two effective Cartier divisors `E₁, E₂` with finite
disjoint supports, each of which is *good*: the complement `V ∖ E` is affine,
`H¹(V, 𝒪_V(E)) = 0`, and the ring of functions on `V ∖ E` is generated over `Γ(V, 𝒪_V)` by
finitely many ratios `t / 1_E` of global sections `t` of `𝒪_V(E)` by the canonical section.

## Main definitions

* `AlgebraicGeometry.C1590Private.IsGoodDivisor`: the goodness condition on an effective Cartier
  divisor of a scheme.
* `AlgebraicGeometry.C1590Private.IsGoodFibreDivisor`: the same, on the scheme underlying an
  object of the big fppf site.
* `AlgebraicGeometry.C1590Private.IsAmpleDivisor`: an effective Cartier divisor whose invertible
  sheaf is ample; `AlgebraicGeometry.C1590Private.IsAmpleGoodFibreDivisor` is
  `IsGoodFibreDivisor` together with it.
* `AlgebraicGeometry.C1590Private.FibreGoodDivisorPair`: the fibre of a family of curves at a
  closed point carries two good divisors with finite disjoint supports.

## Main results

* `AlgebraicGeometry.C1590Private.exists_isGoodDivisor_isAmpleDivisor`: a proper scheme of
  dimension at most one over a Noetherian ring carries a good ample divisor with finite support
  avoiding any finite set; `AlgebraicGeometry.C1590Private.exists_isGoodDivisor` forgets the
  ampleness.
* `AlgebraicGeometry.C1590Private.fibreGoodDivisorPair_isAmple`: the predicate
  `FibreGoodDivisorPair` holds at `Good = IsAmpleGoodFibreDivisor`.
* `AlgebraicGeometry.C1590Private.fibreGoodDivisorPair`: the predicate `FibreGoodDivisorPair`
  holds at `Good = IsGoodFibreDivisor`.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.C1590Private

universe u

/-- An effective Cartier divisor `E` of a scheme `X` is *good* when the complement `U = X ∖ E` is
affine, `H¹(X, 𝒪_X(E)) = 0`, and `Γ(U, 𝒪_X)` is generated as a ring by the restrictions of the
global functions together with finitely many ratios `f` of global sections `t` of `𝒪_X(E)` by
the canonical section `1_E`, that is, `t|_U = f • 1_E|_U`. -/
def IsGoodDivisor (X : Scheme.{u}) (E : X.IdealSheafData) : Prop :=
  Stacks.Divisors.IsEffectiveCartierDivisor E ∧ IsAffineOpen E.support.compl ∧
    IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Stacks.Divisors.divisorSheaf E)) ∧
    ∃ (n : ℕ) (f : Fin n → Γ(X, E.support.compl)),
      (∀ i, ∃ t : Γ(Stacks.Divisors.divisorSheaf E, ⊤),
        (Stacks.Divisors.divisorSheaf E).presheaf.map
            (homOfLE (le_top : E.support.compl ≤ ⊤)).op t =
          f i • (Stacks.Divisors.divisorSheaf E).presheaf.map
            (homOfLE (le_top : E.support.compl ≤ ⊤)).op
            (Stacks.Divisors.divisorSheafGlobalSection E)) ∧
      Subring.closure (Set.range (X.presheaf.map (homOfLE (le_top : E.support.compl ≤ ⊤)).op) ∪
        Set.range f) = ⊤

/-- An effective Cartier divisor `E` of a scheme `X` is *ample* when its invertible sheaf
`𝒪_X(E)` is ample. -/
def IsAmpleDivisor (X : Scheme.{u}) (E : X.IdealSheafData) : Prop :=
  ∃ _ : Stacks.Divisors.IsEffectiveCartierDivisor E,
    haveI := Stacks.Divisors.isInvertible_divisorSheaf E
    Stacks.Ample.IsAmple X (Stacks.Divisors.divisorSheaf E)

/-- A global section of an invertible module on a locally Noetherian scheme which does not vanish
at any associated point cuts out an effective Cartier divisor `E` whose support is the vanishing
locus of the section, and `𝒪_X(E)` is identified with the module carrying `1_E` to the
section. -/
theorem exists_divisor_of_nonvanishing {X : Scheme.{u}} [IsLocallyNoetherian X] (N : X.Modules)
    [Stacks.Ample.IsInvertibleModule X N] (δ : Γ(N, ⊤))
    (hAss : Stacks.Divisors.schemeAssociatedPoints X ⊆ Stacks.Ample.nonvanishingLocus N δ) :
    ∃ (E : X.IdealSheafData) (e : Stacks.Divisors.divisorSheaf E ≅ N),
      Stacks.Divisors.IsEffectiveCartierDivisor E ∧
      e.hom.app ⊤ (Stacks.Divisors.divisorSheafGlobalSection E) = δ ∧
      (E.support : Set X) = (Stacks.Ample.nonvanishingLocus N δ)ᶜ := by
  have := InvertibleSheafGeneral.isInvertible_of_isInvertibleModule N
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv X N).symm δ with hs
  have hsδ : s.eval (op ⊤) = δ := (Stacks.NonvanishingSpelling.sectionsEquiv X N).apply_symm_apply δ
  have hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s :=
    (Stacks.Divisors.isRegularSection_iff_forall_associatedPoint_notMem_maximalSmul N s).2
      fun x hx => by rw [hsδ]; exact hAss hx
  obtain ⟨e, he, -⟩ := existsUnique_invertibleSheafIso_zeroScheme X N s hreg
  refine ⟨_, e, (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X N s).2 hreg,
    he.trans hsδ, ?_⟩
  ext x
  rw [hsδ]
  constructor
  · intro hx hxN
    exact notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen N δ hxN hx
  · intro hx
    by_contra hxs
    exact hx (Stacks.Algebraization.mem_nonvanishingOpen_of_notMem_support_zeroScheme N δ hxs)

/-- The closure of a point, as an irreducible closed subset. -/
abbrev closurePt {X : Type*} [TopologicalSpace X] (x : X) : IrreducibleCloseds X :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- In a space of Krull dimension at most one, a point which is not a generic point of the
irreducible component through it is closed. -/
theorem isClosed_singleton_of_ne_genericPoint {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] (hdim : topologicalKrullDim X ≤ 1) (z : X)
    (hz : z ≠ (isIrreducible_irreducibleComponent (x := z)).genericPoint) : IsClosed {z} := by
  set η := (isIrreducible_irreducibleComponent (x := z)).genericPoint
  have hη : IsGenericPoint η (irreducibleComponent z) :=
    isIrreducible_irreducibleComponent.isGenericPoint_genericPoint isClosed_irreducibleComponent
  by_contra hcl
  obtain ⟨w, hw, hwz⟩ : ∃ w ∈ closure ({z} : Set X), w ≠ z := by
    by_contra! h
    exact hcl (closure_subset_iff_isClosed.mp fun w hw => h w hw)
  have hzw : z ⤳ w := specializes_iff_mem_closure.mpr hw
  have hηz : η ⤳ z := hη.specializes mem_irreducibleComponent
  have key : ∀ a b : X, a ⤳ b → b ≠ a → closurePt b < closurePt a := fun a b hab hne => by
    refine lt_of_le_of_ne (fun y hy => ?_) fun h => hne ?_
    · exact specializes_iff_mem_closure.mp (hab.trans (specializes_iff_mem_closure.mpr hy))
    · have h' : closure ({b} : Set X) = closure {a} := congrArg SetLike.coe h
      exact (hab.antisymm (specializes_iff_mem_closure.mpr (h' ▸ subset_closure rfl))).eq.symm
  have h1 := key z w hzw hwz
  have h2 := key η z hηz hz
  let p : LTSeries (IrreducibleCloseds X) :=
    ((RelSeries.singleton _ (closurePt w)).snoc (closurePt z) h1).snoc (closurePt η)
      (by simp only; exact h2)
  have hp : (p.length : WithBot ℕ∞) ≤ 1 := (Order.LTSeries.length_le_krullDim p).trans hdim
  exact absurd (show ((2 : ℕ) : WithBot ℕ∞) ≤ 1 from hp) (by decide)

/-- On a Noetherian scheme of dimension at most one, a closed subset containing no associated
point is finite. -/
theorem finite_of_isClosed_of_disjoint_schemeAssociatedPoints {X : Scheme.{u}} [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hAss : Disjoint Z (Stacks.Divisors.schemeAssociatedPoints X)) : Z.Finite := by
  have hcl : ∀ z ∈ Z, IsClosed ({z} : Set X) := fun z hz =>
    isClosed_singleton_of_ne_genericPoint hdim z fun h => Set.disjoint_left.mp hAss (h ▸ hz)
      (mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent X
        (irreducibleComponent_mem_irreducibleComponents z)
        (isIrreducible_irreducibleComponent.isGenericPoint_genericPoint
          isClosed_irreducibleComponent))
  obtain ⟨S, hS, hZS⟩ := NoetherianSpace.exists_finset_irreducible (⟨Z, hZ⟩ : Closeds X)
  have hZeq : Z = ⋃ k ∈ S, (k : Set X) := by
    simpa [Closeds.coe_finset_sup] using congrArg (fun C : Closeds X => (C : Set X)) hZS
  rw [hZeq]
  refine S.finite_toSet.biUnion fun k hk => ?_
  have hirr := hS ⟨k, hk⟩
  have hgen := hirr.isGenericPoint_genericPoint k.isClosed
  have hkZ : (k : Set X) ⊆ Z := hZeq ▸ Set.subset_biUnion_of_mem (u := fun k : Closeds X =>
    (k : Set X)) hk
  have hg := hcl _ (hkZ hgen.mem)
  refine (Set.finite_singleton hirr.genericPoint).subset fun y hy => ?_
  rw [← hg.closure_eq, hgen.def]
  exact hy

/-- An effective Cartier divisor `E` whose complement is an affine open `U` is good when
`H¹(X, 𝒪_X(E)) = 0` and `Γ(U, 𝒪_X)` is generated as a ring by the restrictions of the global
functions together with a finite family `g` of ratios of global sections of `𝒪_X(E)` by the
canonical section `1_E`. -/
theorem isGoodDivisor_of_eq {X : Scheme.{u}} (E : X.IdealSheafData)
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E) (U : X.Opens)
    (hU : E.support.compl = U) (haff : IsAffineOpen U)
    (hH : IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Stacks.Divisors.divisorSheaf E)))
    {ι : Type*} [Finite ι] (g : ι → Γ(X, U))
    (hg : ∀ i, ∃ t : Γ(Stacks.Divisors.divisorSheaf E, ⊤),
      (Stacks.Divisors.divisorSheaf E).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t =
        g i • (Stacks.Divisors.divisorSheaf E).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (Stacks.Divisors.divisorSheafGlobalSection E))
    (hgen : Subring.closure (Set.range (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) ∪
      Set.range g) = ⊤) :
    IsGoodDivisor X E := by
  subst hU
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine ⟨hE, haff, hH, n, g ∘ e.symm, fun i => hg _, ?_⟩
  rwa [Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]

/-- The ring of functions on an affine open of a scheme locally of finite type over an affine
scheme is generated, over the restrictions of the global functions, by finitely many
elements. -/
theorem exists_finite_closure_eq_top {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (κ : Type u) (_ : Finite κ) (g : κ → Γ(X, U)),
      Subring.closure (Set.range (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) ∪
        Set.range g) = ⊤ := by
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance
    ⟨⊤, isAffineOpen_top Y⟩ ⟨U, hU⟩ le_top
  let := (f.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, ⊤) Γ(X, U) := hft
  obtain ⟨S, hS⟩ := this.out
  refine ⟨S, inferInstance, fun x => x.1, eq_top_iff.mpr fun x _ => ?_⟩
  have hx : x ∈ (Algebra.adjoin Γ(Y, ⊤) (S : Set Γ(X, U))).toSubring := by
    rw [hS]; trivial
  rw [Algebra.adjoin_eq_ring_closure] at hx
  refine Subring.closure_mono (Set.union_subset_union ?_ ?_) hx
  · rintro _ ⟨y, rfl⟩
    refine ⟨f.appTop y, ?_⟩
    show _ = (f.app ⊤ ≫ X.presheaf.map (homOfLE le_top).op).hom y
    rfl
  · intro y hy
    exact ⟨⟨y, hy⟩, rfl⟩

section Core

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

/-- Let `X` be proper over a Noetherian ring and of dimension at most one, and let `T ⊆ X` be
finite. Then `X` carries a good effective Cartier divisor `E` with finite support disjoint from
`T` whose invertible sheaf `𝒪_X(E)` is ample. -/
theorem exists_isGoodDivisor_isAmpleDivisor {X : Scheme.{u}} {R : Type u} [CommRing R]
    [IsNoetherianRing R] (f : X ⟶ Spec (.of R)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    {T : Set X} (hT : T.Finite) :
    ∃ E : X.IdealSheafData, IsGoodDivisor X E ∧ IsAmpleDivisor X E ∧ (E.support : Set X).Finite ∧
      Disjoint T E.support := by
  classical
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : X.IsSeparated := Scheme.IsSeparated.of_isSeparated f
  obtain ⟨L, hLinv, hLamp⟩ :=
    Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one
      X hdim
  have : Stacks.Ample.IsInvertibleModule X L := hLinv
  have hL : Stacks.Ample.IsAmple X L := (Stacks.AmpleBridge.isAmple_iff_isAmple X L).2 hLamp
  obtain ⟨m₀, hm₀⟩ := Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase
    X (Spec (.of R)) f inferInstance inferInstance inferInstance L hL
  set L' := Stacks.Ample.tensorPowModule X L ((m₀ + 1 : ℕ) : ℤ) with hL'def
  have hL' : Stacks.Ample.IsAmple X L' :=
    Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L (m₀ + 1) (by omega) hL
  have hassoc : (Stacks.Divisors.schemeAssociatedPoints X).Finite := by
    simpa [Stacks.Divisors.schemeAssociatedPoints] using
      associatedPoints_inter_finite (SheafOfModules.unit X.ringCatSheaf) ⊤
        (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  obtain ⟨n, hn, s, haff, hTs, -⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite L' hL'
      (hT.union hassoc) ⊤ (fun _ _ => trivial)
  set U := Stacks.AmpleTheory.powNonvanishingOpen X L' n s with hUdef
  obtain ⟨κ, _, g, hgen⟩ := exists_finite_closure_eq_top f U haff
  have := Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L' (n : ℤ)
  obtain ⟨p, σ, τ, -, hUσ, heq⟩ :=
    Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_family_of_isAmple L' hL'
      (Stacks.Ample.tensorPowModule X L' (n : ℤ)) hn s (κ := κ)
      (fun l => g l • Stacks.SectionExtension.resTop U s)
  let M₀ := Stacks.Ample.tensorPowModule X L' (n : ℤ)
  let M := Stacks.Ample.tensorPowModule X L' (p : ℤ)
  let δ := Stacks.SectionTensorFormula.tensorSection M₀ M s σ
  have hδ : Stacks.Ample.nonvanishingLocus (M₀ ⊗ M) δ = U := by
    rw [Stacks.TensorSectionProduct.nonvanishingLocus_tensorSection,
      ← Stacks.AmpleTheory.coe_powNonvanishingOpen, ← Stacks.AmpleTheory.coe_powNonvanishingOpen,
      ← hUσ, Set.inter_self]
  obtain ⟨E, e, hE, he, hsupp⟩ := exists_divisor_of_nonvanishing (M₀ ⊗ M) δ
    (fun x hx => hδ ▸ hTs (Or.inr hx))
  have hEU : (E.support : Set X) = (U : Set X)ᶜ := by rw [hsupp, hδ]
  let e' := e ≪≫ Stacks.AmpleEventualGeneration.tensorPowAdd (L := L') (a := n) (b := p)
    (c := ((n + p : ℕ) : ℤ)) (by push_cast; rfl)
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · refine isGoodDivisor_of_eq E hE U (Opens.ext ?_) haff ?_ g (fun i => ?_) hgen
    · show ((E.support : Set X))ᶜ = U
      rw [hEU, compl_compl]
    · have hk : m₀ ≤ (m₀ + 1) * (n + p) := by nlinarith
      let i : Stacks.Divisors.divisorSheaf E ≅
          Stacks.Ample.tensorPowModule X L (((m₀ + 1) * (n + p) : ℕ) : ℤ) :=
        e' ≪≫ Stacks.RelativeVeryAmple.tensorPowModulePowIso X L ((m₀ + 1 : ℕ) : ℤ) (n + p) ≪≫
          Stacks.RelativeVeryAmple.tensorPowModuleCongr X L (by push_cast; ring)
      exact (hm₀ _ hk 1 one_pos).of_iso ((Hfunctor X.ringCatSheaf ⊤ 1).mapIso i)
    · refine ⟨e.inv.app ⊤ (τ i), ?_⟩
      have hτ : Stacks.SectionExtension.resTop U (τ i) =
          g i • Stacks.SectionExtension.resTop U δ := by
        rw [heq i, Stacks.SectionTensorFormula.tensorSection_smul_left]
        congr 1
        exact (Stacks.SectionTensorFormula.map_tensorSection M₀ M (homOfLE le_top) s σ).symm
      have h1 := Stacks.SectionExtension.resTop_app_of_res_eq e.inv (g i) (τ i) δ hτ
      have h2 : e.inv.app ⊤ δ = Stacks.Divisors.divisorSheafGlobalSection E := by
        rw [← he]; exact Scheme.Modules.app_inv_app e ⊤ _
      rwa [h2] at h1
  · refine ⟨hE, ?_⟩
    have := Stacks.Divisors.isInvertible_divisorSheaf E
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e').mpr
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L' (n + p) (by omega) hL')
  · exact finite_of_isClosed_of_disjoint_schemeAssociatedPoints hdim E.support.isClosed
      (Set.disjoint_left.mpr fun x hx hxA => by
        rw [hEU] at hx; exact hx (hTs (Or.inr hxA)))
  · exact Set.disjoint_left.mpr fun x hx hxE => by
      rw [hEU] at hxE; exact hxE (hTs (Or.inl hx))

/-- Let `X` be proper over a Noetherian ring and of dimension at most one, and let `T ⊆ X` be
finite. Then `X` carries a good effective Cartier divisor with finite support disjoint from
`T`. -/
theorem exists_isGoodDivisor {X : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
    (f : X ⟶ Spec (.of R)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) {T : Set X}
    (hT : T.Finite) :
    ∃ E : X.IdealSheafData, IsGoodDivisor X E ∧ (E.support : Set X).Finite ∧
      Disjoint T E.support :=
  (exists_isGoodDivisor_isAmpleDivisor f hdim hT).imp fun _ h => ⟨h.1, h.2.2⟩

end Core

/-! ### The fibres of a family of curves -/

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- `AlgebraicGeometry.C1590Private.IsGoodDivisor` on the scheme underlying an object of the big
fppf site. -/
abbrev IsGoodFibreDivisor (V : BigFppfOver B integerBase hZ)
    (E : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData) : Prop :=
  IsGoodDivisor ((BigFppfOver.toScheme B integerBase hZ).obj V) E

/-- The fibre of a family of curves at the residue point of a closed point carries two `Good`
effective Cartier divisors with finite disjoint supports. -/
def FibreGoodDivisorPair
    (Good : ∀ V : BigFppfOver B integerBase hZ,
      ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData → Prop) : Prop :=
  ∀ (X : CurveFamily B hZ)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (_ : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (_ : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value)),
    ∃ E₁ E₂ : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData,
      Stacks.Divisors.IsEffectiveCartierDivisor E₁ ∧ Stacks.Divisors.IsEffectiveCartierDivisor E₂ ∧
      (E₁.support : Set ((BigFppfOver.toScheme B integerBase hZ).obj V)).Finite ∧
      (E₂.support : Set ((BigFppfOver.toScheme B integerBase hZ).obj V)).Finite ∧
      Disjoint (E₁.support : Set ((BigFppfOver.toScheme B integerBase hZ).obj V)) E₂.support ∧
      Good V E₁ ∧ Good V E₂

variable {B hZ} in
/-- A scheme presenting the fibre of a family of curves at a field-valued point has dimension at
most one. -/
theorem topologicalKrullDim_le_one_of_isPullback {X : CurveFamily B hZ}
    {K V : BigFppfOver B integerBase hZ}
    [Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj K)]
    (t : K ⟶ X.base) (v : V ⟶ K) (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yoneda.map t))
    (k : (BigFppfOver.toScheme B integerBase hZ).obj K) :
    topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) ≤ 1 := by
  have h := isPullback_homMk_of_isPullback t v q hV
  let Y := curveFamilyOfIsPullback X t _ _ h
  have hid : schemeSpaceMap (𝟙 K) = 𝟙 (schemeSpace K) :=
    (schemeSpaceFunctor B integerBase hZ).map_id _
  have sq : IsPullback (𝟙 (schemeSpace V)) (schemeSpaceMap v) (schemeSpaceMap v)
      (schemeSpaceMap (𝟙 K)) := by
    have : IsIso (schemeSpaceMap (𝟙 K)) := by rw [hid]; infer_instance
    exact IsPullback.of_horiz_isIso ⟨by rw [hid, Category.id_comp, Category.comp_id]⟩
  have het : Etale ((BigFppfOver.toScheme B integerBase hZ).map (𝟙 K)) := by
    rw [CategoryTheory.Functor.map_id]; infer_instance
  have hfib := Y.topologicalKrullDim_fiber_toScheme_map_le_of_isPullback (p := 𝟙 _)
    (q := v) sq het k
  rwa [Scheme.Hom.topologicalKrullDim_fiber_of_subsingleton] at hfib

/-- `AlgebraicGeometry.C1590Private.IsGoodFibreDivisor` together with ampleness of the
invertible sheaf of the divisor (`AlgebraicGeometry.C1590Private.IsAmpleDivisor`). -/
abbrev IsAmpleGoodFibreDivisor (V : BigFppfOver B integerBase hZ)
    (E : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData) : Prop :=
  IsGoodFibreDivisor B hZ V E ∧ IsAmpleDivisor ((BigFppfOver.toScheme B integerBase hZ).obj V) E

variable {B hZ} in
/-- `AlgebraicGeometry.C1590Private.FibreGoodDivisorPair` is monotone in the predicate. -/
theorem FibreGoodDivisorPair.mono
    {Good Good' : ∀ V : BigFppfOver B integerBase hZ,
      ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData → Prop}
    (h : FibreGoodDivisorPair B hZ Good) (hG : ∀ V E, Good V E → Good' V E) :
    FibreGoodDivisorPair B hZ Good' := by
  intro X P hP V v q hq
  obtain ⟨E₁, E₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h X P hP V v q hq
  exact ⟨E₁, E₂, h₁, h₂, h₃, h₄, h₅, hG _ _ h₆, hG _ _ h₇⟩

/-- The fibre of a family of curves at a closed point carries two good effective Cartier divisors
with finite disjoint supports, whose invertible sheaves are ample. -/
theorem fibreGoodDivisorPair_isAmple : FibreGoodDivisorPair B hZ
    (IsAmpleGoodFibreDivisor B hZ) := by
  intro X P _ V v q hq
  rw [yonedaEquiv_symm_value] at hq
  have h := isPullback_homMk_of_isPullback _ v q hq
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) :=
    X.isProper_toScheme_map_of_isPullback_schemeSpaceMap h
  have : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj P.siteObject) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum P.carrier))
  have hdim := topologicalKrullDim_le_one_of_isPullback _ v q hq
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum P.carrier)
  obtain ⟨E₁, hE₁, hA₁, hf₁, -⟩ := exists_isGoodDivisor_isAmpleDivisor (R := P.carrier)
    ((BigFppfOver.toScheme B integerBase hZ).map v) hdim Set.finite_empty
  obtain ⟨E₂, hE₂, hA₂, hf₂, hd⟩ := exists_isGoodDivisor_isAmpleDivisor (R := P.carrier)
    ((BigFppfOver.toScheme B integerBase hZ).map v) hdim hf₁
  exact ⟨E₁, E₂, hE₁.1, hE₂.1, hf₁, hf₂, hd, ⟨hE₁, hA₁⟩, ⟨hE₂, hA₂⟩⟩

/-- The fibre of a family of curves at a closed point carries two good effective Cartier divisors
with finite disjoint supports. -/
theorem fibreGoodDivisorPair : FibreGoodDivisorPair B hZ (IsGoodFibreDivisor B hZ) :=
  (fibreGoodDivisorPair_isAmple B hZ).mono fun _ _ h => h.1


end AlgebraicGeometry.C1590Private

end
