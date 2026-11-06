module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.PUnit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroTor
public import StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroCriterion
public import StacksFrontier.RingTheory.Flat.LocalCriteria.FibreCriteria
import all StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroTor
import all StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroCriterion
import all StacksFrontier.RingTheory.Flat.LocalCriteria.FibreCriteria

/-!
# Tor against finite length modules, the away-and-quotient criterion and nilpotent descent

Stacks 00MJ (`Tor₁` against the residue field controls `Tor₁` against finite length modules),
Stacks 0H7N (flatness glued from `M_f` and `M/fM`), Stacks 051J (the local criterion along an
injective ring map with nilpotent ideal) and flatness of reductions along a localization.
-/

section

universe u v w

@[expose] public section

/-! ### Stacks 00MJ -/

section

open CategoryTheory Limits MonoidalCategory


namespace Stacks.CategoryHomology.LeftDerivedVanishing

section LeftDerived

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]

/-- Exactness of `X ⟶ Y ⟶ Z` only depends on the second map through its value. -/
private lemma exact_iff_exact_of_eq {X Y Z : C} {f : X ⟶ Y} {g g' : Y ⟶ Z} (hg : g = g')
    {h : f ≫ g = 0} {h' : f ≫ g' = 0} :
    (ShortComplex.mk f g h).Exact ↔ (ShortComplex.mk f g' h').Exact := by
  subst hg
  rfl

/-- Exactness of `X ⟶ Y ⟶ W` is unchanged when the second map is factored as a map to `Z`
followed by a monomorphism `Z ⟶ W`. -/
lemma exact_iff_exact_of_eq_comp_mono {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ Z} {g' : Y ⟶ W}
    (i : Z ⟶ W) [Mono i] (hg : g' = g ≫ i) {h : f ≫ g = 0} {h' : f ≫ g' = 0} :
    (ShortComplex.mk f g' h').Exact ↔ (ShortComplex.mk f g h).Exact := by
  subst hg
  simp only [ShortComplex.exact_iff_exact_up_to_refinements]
  refine ⟨fun H A x hx => H x ?_, fun H A x hx => H x ?_⟩
  · rw [← Category.assoc, hx, zero_comp]
  · rw [← cancel_mono i, zero_comp, Category.assoc]
    exact hx

/-- If `X ⟶ Y ⟶ Z` is exact with `Y ⟶ Z` an epimorphism, then for `i : Z ⟶ W` the complex
`X ⟶ Y ⟶ W` is exact if and only if `i` is a monomorphism. -/
private lemma exact_comp_iff_mono {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ Z} (i : Z ⟶ W) [Epi g]
    {h : f ≫ g = 0} (hex : (ShortComplex.mk f g h).Exact) (h' : f ≫ (g ≫ i) = 0) :
    (ShortComplex.mk f (g ≫ i) h').Exact ↔ Mono i := by
  refine ⟨fun hE => ?_, fun _ => (exact_iff_exact_of_eq_comp_mono i rfl).mpr hex⟩
  rw [Preadditive.mono_iff_cancel_zero]
  intro T y hy
  obtain ⟨T', e, he, x, hx⟩ := surjective_up_to_refinements_of_epi g y
  have hxz : x ≫ (g ≫ i) = 0 := by
    rw [← Category.assoc, ← hx, Category.assoc, hy, comp_zero]
  obtain ⟨T'', e', he', z, hz⟩ := hE.exact_up_to_refinements x hxz
  have hzero : (e' ≫ e) ≫ y = 0 := by
    rw [Category.assoc, hx, ← Category.assoc, hz, Category.assoc, h, comp_zero]
  exact zero_of_epi_comp (e' ≫ e) hzero

/-- If `G` is injective along `a` and `v ≫ a = b ≫ c`, then `x ≫ G.map b = 0` forces
`x ≫ G.map v = 0`. -/
private lemma comp_map_eq_zero_of_mono {E : Type*} [Category* E] {G : E ⥤ D} {X Y Z W : E}
    {v : X ⟶ Y} {a : Y ⟶ Z} {b : X ⟶ W} {c : W ⟶ Z} (hv : v ≫ a = b ≫ c) [Mono (G.map a)]
    {T : D} {x : T ⟶ G.obj X} (hx : x ≫ G.map b = 0) : x ≫ G.map v = 0 :=
  (Preadditive.mono_iff_cancel_zero (G.map a)).mp ‹_› _ _ (by
    rw [Category.assoc, ← G.map_comp, hv, G.map_comp, ← Category.assoc, hx, zero_comp])

omit [PreservesFiniteColimits F] in
/-- Whether a right exact additive functor `F` remains injective on the kernel of a presentation
of `X` by a projective object does not depend on the presentation. -/
lemma mono_map_of_mono_map {X K P K' P' : C} {ι : K ⟶ P} {π : P ⟶ X} {ι' : K' ⟶ P'}
    {π' : P' ⟶ X} [Projective P] [Projective P'] [Mono ι] [Mono ι']
    {h : ι ≫ π = 0} {h' : ι' ≫ π' = 0} (hπ : Epi π) (hπ' : Epi π')
    (hex : (ShortComplex.mk ι π h).Exact) (hex' : (ShortComplex.mk ι' π' h').Exact)
    (hm : Mono (F.map ι)) : Mono (F.map ι') := by
  have := hπ
  have := hπ'
  obtain ⟨u', hu'⟩ : ∃ u' : P' ⟶ P, u' ≫ π = π' :=
    ⟨Projective.factorThru π' π, Projective.factorThru_comp _ _⟩
  obtain ⟨u, hu⟩ : ∃ u : P ⟶ P', u ≫ π' = π :=
    ⟨Projective.factorThru π π', Projective.factorThru_comp _ _⟩
  obtain ⟨v', hv'⟩ := hex.lift' (ι' ≫ u') (by rwa [Category.assoc, hu'])
  obtain ⟨v, hv⟩ := hex'.lift' (ι ≫ u) (by rwa [Category.assoc, hu])
  obtain ⟨w, hw⟩ := hex'.lift' (𝟙 P' - u' ≫ u) (by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hu, hu', sub_self])
  have hvv : 𝟙 K' = v' ≫ v + ι' ≫ w := by
    have hcomp : (v' ≫ v) ≫ ι' = ι' ≫ (u' ≫ u) := by
      rw [Category.assoc, hv, ← Category.assoc, hv', Category.assoc]
    rw [← cancel_mono ι', Category.id_comp, Preadditive.add_comp, hcomp, Category.assoc, hw,
      Preadditive.comp_sub, Category.comp_id]
    abel
  rw [Preadditive.mono_iff_cancel_zero]
  intro T x hx
  have h1 : x ≫ F.map v' = 0 := comp_map_eq_zero_of_mono hv' hx
  calc x = x ≫ F.map (𝟙 K') := by simp
    _ = x ≫ (F.map v' ≫ F.map v) + x ≫ (F.map ι' ≫ F.map w) := by
        rw [hvv, F.map_add, F.map_comp, F.map_comp, Preadditive.comp_add]
    _ = 0 := by rw [← Category.assoc, h1, ← Category.assoc, hx, zero_comp, zero_comp, add_zero]

variable [EnoughProjectives C]

/-- The syzygy criterion, for the presentation of `X` by the degree zero term of a projective
resolution: the first left derived functor of a right exact additive functor `F` vanishes at `X`
if and only if `F` remains injective on the first syzygy of the resolution. -/
private lemma isZero_leftDerived_one_iff_mono_kernel_ι {X : C} (P : ProjectiveResolution X) :
    IsZero ((F.leftDerived 1).obj X) ↔ Mono (F.map (kernel.ι (P.π.f 0))) := by
  have hz0 : P.complex.d 1 0 ≫ P.π.f 0 = 0 := P.complex_d_comp_π_f_zero
  set q := kernel.lift (P.π.f 0) (P.complex.d 1 0) hz0 with hqdef
  have hqι : q ≫ kernel.ι (P.π.f 0) = P.complex.d 1 0 := kernel.lift_ι _ _ _
  have hex₀ : (ShortComplex.mk (P.complex.d 1 0) (P.π.f 0) hz0).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ P.isColimitCokernelCofork
  have hq : Epi q := hex₀.epi_kernelLift
  have hd2q : P.complex.d 2 1 ≫ q = 0 := by
    rw [← cancel_mono (kernel.ι (P.π.f 0)), Category.assoc, hqι, zero_comp]
    simp
  have hex₁ : (ShortComplex.mk (P.complex.d 2 1) q hd2q).Exact :=
    (exact_iff_exact_of_eq_comp_mono _ hqι.symm).mp (P.exact_succ 0)
  have hFex₁ := hex₁.map_of_epi_of_preservesCokernel F hq inferInstance
  have hFd : F.map (P.complex.d 1 0) = F.map q ≫ F.map (kernel.ι (P.π.f 0)) := by
    rw [← F.map_comp, hqι]
  have hz1 : F.map (P.complex.d 2 1) ≫ (F.map q ≫ F.map (kernel.ι (P.π.f 0))) = 0 := by
    rw [← hFd, ← F.map_comp]
    simp
  rw [Iso.isZero_iff (P.isoLeftDerivedObj F 1)]
  simp only [HomologicalComplex.homologyFunctor_obj]
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  exact Iff.trans (exact_iff_exact_of_eq (h' := hz1) hFd)
    (exact_comp_iff_mono (F.map (kernel.ι (P.π.f 0))) hFex₁ hz1)

/-- The syzygy criterion: for any presentation `0 → K → P → X → 0` of `X` by a projective object
`P`, the first left derived functor of a right exact additive functor `F` vanishes at `X` if and
only if `F` remains injective on `K ⟶ P`. -/
private lemma isZero_leftDerived_one_iff_mono {X K P : C} {ι : K ⟶ P} {π : P ⟶ X} [Projective P]
    [Mono ι] [Epi π] {h : ι ≫ π = 0} (hex : (ShortComplex.mk ι π h).Exact) :
    IsZero ((F.leftDerived 1).obj X) ↔ Mono (F.map ι) := by
  have PR := projectiveResolution X
  have hepi : Epi (PR.π.f 0) := inferInstance
  have hex₀ := ShortComplex.exact_kernel (PR.π.f 0)
  rw [isZero_leftDerived_one_iff_mono_kernel_ι F PR]
  exact ⟨fun hm => mono_map_of_mono_map F hepi ‹Epi π› hex₀ hex hm,
    fun hm => mono_map_of_mono_map F ‹Epi π› hepi hex hex₀ hm⟩

/-- The long exact sequence of `L₁F` in the resolved variable, in the only degree used here: the
class of objects at which the first left derived functor of a right exact additive functor
vanishes is closed under extensions. -/
private lemma isZero_leftDerived_one_X₂ {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : IsZero ((F.leftDerived 1).obj S.X₁)) (h₃ : IsZero ((F.leftDerived 1).obj S.X₃)) :
    IsZero ((F.leftDerived 1).obj S.X₂) := by
  have := hS.mono_f
  have := hS.epi_g
  obtain ⟨PA, α, hαepi, hαproj⟩ : ∃ (PA : C) (α : PA ⟶ S.X₁), Epi α ∧ Projective PA :=
    ⟨Projective.over S.X₁, Projective.π S.X₁, inferInstance, inferInstance⟩
  obtain ⟨PC, γ, hγepi, hγproj⟩ : ∃ (PC : C) (γ : PC ⟶ S.X₃), Epi γ ∧ Projective PC :=
    ⟨Projective.over S.X₃, Projective.π S.X₃, inferInstance, inferInstance⟩
  have := hαepi; have := hαproj; have := hγepi; have := hγproj
  obtain ⟨s, hs⟩ : ∃ s : PC ⟶ S.X₂, s ≫ S.g = γ :=
    ⟨Projective.factorThru γ S.g, Projective.factorThru_comp _ _⟩
  obtain ⟨β, hβdef⟩ : ∃ β : PA ⊞ PC ⟶ S.X₂, β = biprod.desc (α ≫ S.f) s := ⟨_, rfl⟩
  have hinl : biprod.inl ≫ β = α ≫ S.f := by rw [hβdef, biprod.inl_desc]
  have hβg : β ≫ S.g = biprod.snd ≫ γ := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [← Category.assoc, hinl, ← Category.assoc, biprod.inl_snd, Category.assoc, S.zero,
        comp_zero, zero_comp]
    · rw [← Category.assoc, hβdef, biprod.inr_desc, ← Category.assoc, biprod.inr_snd,
        Category.id_comp, hs]
  have hmα := (isZero_leftDerived_one_iff_mono F (ShortComplex.exact_kernel α)).mp h₁
  have hmγ := (isZero_leftDerived_one_iff_mono F (ShortComplex.exact_kernel γ)).mp h₃
  -- the horseshoe map `β` is an epimorphism
  have hβepi : Epi β := by
    rw [epi_iff_surjective_up_to_refinements]
    intro T y
    obtain ⟨T₁, e₁, he₁, c, hc⟩ := surjective_up_to_refinements_of_epi γ (y ≫ S.g)
    obtain ⟨a, ha⟩ := hS.exact.lift' (e₁ ≫ y - c ≫ s) (by
      have haux : (e₁ ≫ y) ≫ S.g = (c ≫ s) ≫ S.g := by
        rw [Category.assoc, Category.assoc, hc, hs]
      rw [Preadditive.sub_comp, haux, sub_self])
    obtain ⟨T₂, e₂, he₂, p, hp⟩ := surjective_up_to_refinements_of_epi α a
    refine ⟨T₂, e₂ ≫ e₁, epi_comp _ _, biprod.lift p (e₂ ≫ c), ?_⟩
    have hkey : p ≫ (α ≫ S.f) = e₂ ≫ e₁ ≫ y - e₂ ≫ c ≫ s := by
      rw [← Category.assoc, ← hp, Category.assoc, ha, Preadditive.comp_sub]
    rw [hβdef, biprod.lift_desc, hkey]
    simp only [Category.assoc]
    abel
  -- the kernels of `α`, `β`, `γ` form a short exact sequence
  have hzj : (kernel.ι α ≫ biprod.inl) ≫ β = 0 := by
    rw [Category.assoc, hinl, ← Category.assoc, kernel.condition, zero_comp]
  have hzr : (kernel.ι β ≫ biprod.snd) ≫ γ = 0 := by
    rw [Category.assoc, ← hβg, ← Category.assoc, kernel.condition, zero_comp]
  obtain ⟨j, hj⟩ : ∃ j : kernel α ⟶ kernel β, j ≫ kernel.ι β = kernel.ι α ≫ biprod.inl :=
    ⟨kernel.lift β _ hzj, kernel.lift_ι _ _ _⟩
  obtain ⟨r, hr⟩ : ∃ r : kernel β ⟶ kernel γ, r ≫ kernel.ι γ = kernel.ι β ≫ biprod.snd :=
    ⟨kernel.lift γ _ hzr, kernel.lift_ι _ _ _⟩
  have hjr : j ≫ r = 0 := by
    rw [← cancel_mono (kernel.ι γ), Category.assoc, hr, ← Category.assoc, hj]
    simp
  have hrepi : Epi r := by
    rw [epi_iff_surjective_up_to_refinements]
    intro T y
    obtain ⟨a, ha⟩ := hS.exact.lift' ((y ≫ kernel.ι γ) ≫ s) (by
      rw [Category.assoc, Category.assoc, hs, kernel.condition, comp_zero])
    obtain ⟨T', e, he, p, hp⟩ := surjective_up_to_refinements_of_epi α a
    have hkey : p ≫ (α ≫ S.f) = (e ≫ y ≫ kernel.ι γ) ≫ s := by
      rw [← Category.assoc, ← hp, Category.assoc, ha]
      simp
    have hx : (biprod.lift (-p) (e ≫ y ≫ kernel.ι γ)) ≫ β = 0 := by
      rw [hβdef, biprod.lift_desc, Preadditive.neg_comp, hkey, neg_add_cancel]
    obtain ⟨x, hxι⟩ : ∃ x : T' ⟶ kernel β,
        x ≫ kernel.ι β = biprod.lift (-p) (e ≫ y ≫ kernel.ι γ) :=
      ⟨kernel.lift β _ hx, kernel.lift_ι _ _ _⟩
    refine ⟨T', e, he, x, (cancel_mono (kernel.ι γ)).mp ?_⟩
    have hgoal : x ≫ r ≫ kernel.ι γ = e ≫ y ≫ kernel.ι γ := by
      conv_lhs => rw [hr, ← Category.assoc, hxι, biprod.lift_snd]
    simp only [Category.assoc]
    exact hgoal.symm
  have hjr_exact : (ShortComplex.mk j r hjr).Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    set z := x ≫ kernel.ι β with hzdef
    have h1 : z ≫ biprod.snd = 0 := by
      rw [hzdef, Category.assoc, ← hr, ← Category.assoc, hx, zero_comp]
    have h2 : z = (z ≫ biprod.fst) ≫ biprod.inl := by
      calc z = z ≫ 𝟙 _ := by simp
        _ = z ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) := by rw [biprod.total]
        _ = (z ≫ biprod.fst) ≫ biprod.inl + (z ≫ biprod.snd) ≫ biprod.inr := by
            simp only [Preadditive.comp_add, Category.assoc]
        _ = (z ≫ biprod.fst) ≫ biprod.inl := by rw [h1, zero_comp, add_zero]
    have h3 : (z ≫ biprod.fst) ≫ α = 0 := by
      refine (Preadditive.mono_iff_cancel_zero _).mp hS.mono_f _ ((z ≫ biprod.fst) ≫ α) ?_
      rw [Category.assoc, ← hinl, ← Category.assoc, ← h2, hzdef, Category.assoc,
        kernel.condition, comp_zero]
    obtain ⟨y', hy'⟩ : ∃ y' : T ⟶ kernel α, y' ≫ kernel.ι α = z ≫ biprod.fst :=
      ⟨kernel.lift α _ h3, kernel.lift_ι _ _ _⟩
    refine ⟨T, 𝟙 T, inferInstance, y', ?_⟩
    rw [Category.id_comp]
    refine (cancel_mono (kernel.ι β)).mp ?_
    conv_rhs => rw [Category.assoc, hj, ← Category.assoc, hy']
    exact h2
  -- the four term diagram chase
  have hFjr := hjr_exact.map_of_epi_of_preservesCokernel F hrepi inferInstance
  have hmβ : Mono (F.map (kernel.ι β)) := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro T y hy
    have h1 : y ≫ F.map r = 0 := comp_map_eq_zero_of_mono hr hy
    obtain ⟨T', e, he, x, hx⟩ := hFjr.exact_up_to_refinements y h1
    simp only [ShortComplex.map_f] at hx
    have : IsSplitMono (F.map (biprod.inl : PA ⟶ PA ⊞ PC)) :=
      IsSplitMono.mk' { retraction := F.map biprod.fst
                        id := by rw [← F.map_comp, biprod.inl_fst, F.map_id] }
    have h3 : x ≫ F.map (kernel.ι α) = 0 := by
      refine (Preadditive.mono_iff_cancel_zero (F.map (biprod.inl : PA ⟶ PA ⊞ PC))).mp
        inferInstance _ (x ≫ F.map (kernel.ι α)) ?_
      rw [Category.assoc, ← F.map_comp, ← hj, F.map_comp, ← Category.assoc, ← hx,
        Category.assoc, hy, comp_zero]
    have hx0 : x = 0 := (Preadditive.mono_iff_cancel_zero _).mp hmα _ x h3
    have hey : e ≫ y = 0 := by rw [hx, hx0, zero_comp]
    exact zero_of_epi_comp e hey
  have := hβepi
  exact (isZero_leftDerived_one_iff_mono F (ShortComplex.exact_kernel β)).mpr hmβ

end LeftDerived

section Tor

variable {R : Type u} [CommRing R]

/-- Tag 00MJ, as an induction on Mathlib's inductive predicate `IsFiniteLength`. -/
@[ega "III 7.3.5.3" "special case"]
private lemma isZero_Tor'_one_of_isFiniteLength [IsLocalRing R] (M : ModuleCat.{u} R)
    (hM : IsZero (((Tor' (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj M))
    (X : Type u) [AddCommGroup X] [Module R X] (hX : IsFiniteLength R X) :
    IsZero (((Tor' (ModuleCat.{u} R) 1).obj (ModuleCat.of R X)).obj M) := by
  induction hX with
  | @of_subsingleton Y _ _ _ =>
      have : Projective (ModuleCat.of R Y) := (ModuleCat.isZero_of_subsingleton _).projective
      exact isZero_Tor'_succ_of_projective (ModuleCat.{u} R) (ModuleCat.of R Y) M 0
  | @of_simple_quotient Y _ _ N' _ hfl ih =>
      have hzero : ModuleCat.ofHom N'.subtype ≫ ModuleCat.ofHom N'.mkQ = 0 := by
        ext x
        simp
      have hSE := ModuleCat.shortComplex_shortExact
        (ShortComplex.mk (ModuleCat.ofHom N'.subtype) (ModuleCat.ofHom N'.mkQ) hzero)
        (LinearMap.exact_subtype_mkQ N') (Submodule.injective_subtype N')
        (Submodule.mkQ_surjective N')
      have hquot : IsZero (((Tor' (ModuleCat.{u} R) 1).obj (ModuleCat.of R (Y ⧸ N'))).obj M) := by
        obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R (Y ⧸ N')›
        rw [IsLocalRing.eq_maximalIdeal hI] at e
        have e' : (Y ⧸ N') ≃ₗ[R] IsLocalRing.ResidueField R := e
        exact hM.of_iso (((Tor' (ModuleCat.{u} R) 1).mapIso e'.toModuleIso).app M)
      exact isZero_leftDerived_one_X₂ ((tensoringRight (ModuleCat.{u} R)).obj M) hSE ih hquot

end Tor

private theorem solution {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R)
    (hM : IsZero (((Tor' (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj M))
    (N : ModuleCat.{u} R) (hN : IsFiniteLength R N) :
    IsZero (((Tor' (ModuleCat.{u} R) 1).obj N).obj M) :=
  isZero_Tor'_one_of_isFiniteLength M hM N hN

end Stacks.CategoryHomology.LeftDerivedVanishing

end

section

open CategoryTheory Limits


namespace IsLocalRing

/-- **Stacks 00MJ.** Let `R` be a local ring with residue field `κ` and let `M` be an `R`-module.
If `Tor₁(κ, M) = 0`, then `Tor₁(N, M) = 0` for every `R`-module `N` of finite length. Here
`Tor₁(N, M)` is `((Tor' (ModuleCat R) 1).obj N).obj M`, the first left derived functor of
`- ⊗ M` evaluated at `N`. -/
@[stacks 00MJ]
theorem isZero_Tor'_one_of_isFiniteLength {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R)
    (hM : IsZero (((Tor' (ModuleCat.{u} R) 1).obj (ModuleCat.of R (ResidueField R))).obj M))
    (N : ModuleCat.{u} R) (hN : IsFiniteLength R N) :
    IsZero (((Tor' (ModuleCat.{u} R) 1).obj N).obj M) :=
      Stacks.CategoryHomology.LeftDerivedVanishing.solution M hM N hN

end IsLocalRing

end


/-! ### Stacks 0H7N -/

section

namespace Stacks.Flatness.AwayAndQuotientCriterion

open TensorProduct LinearMap Pointwise

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] {f : A}

/-- Multiplication by `f`, as a surjective `A`-linear map `A → fA`. -/
private noncomputable def toSpan (f : A) : A →ₗ[A] (Ideal.span {f} : Ideal A) :=
  LinearMap.codRestrict _ (f • LinearMap.id) fun a =>
    Ideal.mem_span_singleton'.2 ⟨a, by simp [mul_comm]⟩

private lemma toSpan_surjective (f : A) : Function.Surjective (toSpan f) := by
  rintro ⟨x, hx⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  exact ⟨c, by ext; simp [toSpan, mul_comm]⟩

/-- If `f` is a nonzerodivisor on `M` then `fA ⊗_A M → M` is injective: the map becomes
multiplication by `f` on `M` after the isomorphism `A ≅ fA`. -/
private lemma injective_lift_lsmul_span_singleton (hM : IsSMulRegular M f) :
    Function.Injective (TensorProduct.lift
      ((LinearMap.lsmul A M).comp (Ideal.span {f} : Ideal A).subtype)) := by
  set k := TensorProduct.lift ((LinearMap.lsmul A M).comp (Ideal.span {f} : Ideal A).subtype)
  have hcomp : ∀ x : A ⊗[A] M,
      k (LinearMap.rTensor M (toSpan f) x) = f • (TensorProduct.lid A M x) := by
    intro x
    induction x with
    | tmul a m =>
        change TensorProduct.lift ((LinearMap.lsmul A M).comp
          (Ideal.span {f} : Ideal A).subtype) ((toSpan f a) ⊗ₜ[A] m) = _
        simp only [TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
          Submodule.coe_subtype, LinearMap.lsmul_apply, TensorProduct.lid_tmul, toSpan,
          LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
          smul_eq_mul]
        rw [mul_smul]
    | add a b ha hb => simp [ha, hb, smul_add]
  have h1 : Function.Injective (k ∘ (LinearMap.rTensor M (toSpan f))) := by
    intro x y hxy
    simp only [Function.comp_apply, hcomp] at hxy
    exact (TensorProduct.lid A M).injective (hM hxy)
  exact h1.of_comp_right (LinearMap.rTensor_surjective M (toSpan_surjective f))

/-- Multiplication by `f`, as an `A`-linear map `P → f • P`. -/
private noncomputable def toSMulTop (f : A) (P : Type*) [AddCommGroup P] [Module A P] :
    P →ₗ[A] (((Ideal.span {f} : Ideal A) • (⊤ : Submodule A P) : Submodule A P)) :=
  LinearMap.codRestrict _ (f • LinearMap.id) fun p => by
    rw [Submodule.ideal_span_singleton_smul]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨p, Submodule.mem_top, rfl⟩

private lemma toSMulTop_apply (f : A) (P : Type*) [AddCommGroup P] [Module A P] (p : P) :
    (toSMulTop f P p : P) = f • p := rfl

private lemma toSMulTop_surjective (f : A) (P : Type*) [AddCommGroup P] [Module A P] :
    Function.Surjective (toSMulTop f P) := by
  rintro ⟨x, hx⟩
  rw [Submodule.ideal_span_singleton_smul] at hx
  obtain ⟨p, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  exact ⟨p, rfl⟩

/-- **A nonzerodivisor stays one after tensoring with `M`.** If `M/fM` is flat over `A/fA` and
`fA ⊗_A M → M` is injective, then `f` is a nonzerodivisor on `M ⊗_A P` for every `A`-module `P`
on which `f` is a nonzerodivisor: multiplication by `f` on `M ⊗_A P` is the isomorphism
`M ⊗_A P ≅ M ⊗_A (f • P)` followed by the injection `M ⊗_A (f • P) → M ⊗_A P`. -/
private lemma isSMulRegular_tensorProduct
    (hquot : Module.Flat (A ⧸ Ideal.span {f}) (M ⧸ (Ideal.span {f} • (⊤ : Submodule A M))))
    (htor : Function.Injective (TensorProduct.lift
      ((LinearMap.lsmul A M).comp (Ideal.span {f} : Ideal A).subtype)))
    {P : Type*} [AddCommGroup P] [Module A P] (hP : IsSMulRegular P f) :
    IsSMulRegular (M ⊗[A] P) f := by
  have hsub := lemmaC_smul_top_subtype_lTensor_injective (Ideal.span {f}) hquot htor (P := P)
  have hbij : Function.Bijective (toSMulTop f P) := by
    refine ⟨fun x y hxy => hP ?_, toSMulTop_surjective f P⟩
    have := congrArg (Subtype.val) hxy
    rwa [toSMulTop_apply, toSMulTop_apply] at this
  have he : Function.Injective (LinearMap.lTensor M (toSMulTop f P)) :=
    (LinearEquiv.lTensor M (LinearEquiv.ofBijective (toSMulTop f P) hbij)).injective
  have hfun : ∀ x : M ⊗[A] P, f • x =
      LinearMap.lTensor M ((Ideal.span {f} • (⊤ : Submodule A P)).subtype)
        (LinearMap.lTensor M (toSMulTop f P) x) := by
    intro x
    induction x with
    | tmul m p => simp [toSMulTop_apply, TensorProduct.tmul_smul]
    | add a b ha hb => simp [ha, hb, smul_add]
  intro x y hxy
  have hxy' : f • x = f • y := hxy
  rw [hfun x, hfun y] at hxy'
  exact he (hsub hxy')

/-- `M/fM` flat over `A/fA` in the spelling `M ⧸ (fA) • ⊤`.

The two quotients are quotients by the *equal* submodules `Ideal.span {f} • ⊤` and `f • ⊤`, so
they carry different `A ⧸ Ideal.span {f}`-module instances and no `▸` relates them; what does is
`Submodule.quotEquivOfEq`, extended to `A ⧸ Ideal.span {f}`-linearity along the surjection
`A → A ⧸ Ideal.span {f}`. -/
private lemma flat_quot_span
    (hQ : Module.Flat (A ⧸ Ideal.span {f}) (QuotSMulTop f M)) :
    Module.Flat (A ⧸ Ideal.span {f}) (M ⧸ (Ideal.span {f} • (⊤ : Submodule A M))) :=
  have : Module.Flat (A ⧸ Ideal.span {f}) (QuotSMulTop f M) := hQ
  Module.Flat.of_linearEquiv
    (LinearEquiv.extendScalarsOfSurjective (S := A ⧸ Ideal.span {f})
      Ideal.Quotient.mk_surjective
      (Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul f ⊤)))

/-- Every ideal of `A` is a module on which `f` is a nonzerodivisor, when `f` is one on `A`. -/
private lemma isSMulRegular_ideal (hA : IsSMulRegular A f) (J : Ideal A) :
    IsSMulRegular (↥J) f := fun x y hxy =>
  Subtype.ext (hA (by simpa using congrArg (Subtype.val) hxy))

/-- **The flat form of Stacks 0H7N.** -/
private theorem flat_of_flat_away_of_flat_quotSMulTop
    (Aₜ : Type*) [CommRing Aₜ] [Algebra A Aₜ] [IsLocalization.Away f Aₜ]
    (Mₜ : Type*) [AddCommGroup Mₜ] [Module A Mₜ] [Module Aₜ Mₜ] [IsScalarTower A Aₜ Mₜ]
    (g : M →ₗ[A] Mₜ) [IsLocalizedModule (Submonoid.powers f) g]
    (hA : IsSMulRegular A f) (hM : IsSMulRegular M f)
    (hflat : Module.Flat Aₜ Mₜ)
    (hQ : Module.Flat (A ⧸ Ideal.span {f}) (QuotSMulTop f M)) :
    Module.Flat A M := by
  have htor := injective_lift_lsmul_span_singleton hM
  have hquot := flat_quot_span hQ
  have : Module.Flat A Aₜ := IsLocalization.flat Aₜ (Submonoid.powers f)
  have : Module.Flat Aₜ Mₜ := hflat
  have hMtflat : Module.Flat A Mₜ := Module.Flat.trans A Aₜ Mₜ
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  have hreg : IsSMulRegular (M ⊗[A] ↥J) f :=
    isSMulRegular_tensorProduct hquot htor (isSMulRegular_ideal hA J)
  have hinj : Function.Injective (LinearMap.lTensor Mₜ J.subtype) :=
    Module.Flat.iff_lTensor_injective'.mp hMtflat J
  have hnat : ∀ x : M ⊗[A] ↥J,
      LinearMap.lTensor Mₜ J.subtype ((AlgebraTensorModule.rTensor A (↥J) g) x)
        = (AlgebraTensorModule.rTensor A A g) (LinearMap.lTensor M J.subtype x) := by
    intro x
    induction x with
    | tmul m a => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h0 : (AlgebraTensorModule.rTensor A (↥J) g) x = 0 := by
    refine hinj ?_
    rw [hnat x, hx, map_zero, map_zero]
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
    (AlgebraTensorModule.rTensor A (↥J) g)).mp h0
  obtain ⟨n, hn⟩ := s.2
  refine hreg.pow n ?_
  have hn' : f ^ n = (s : A) := hn
  change f ^ n • x = f ^ n • (0 : M ⊗[A] ↥J)
  rw [smul_zero, hn']
  exact hs

/-- A faithfully flat module has `J • ⊤ ≠ ⊤` for every proper ideal `J`, not just every maximal
one: `J` lies in a maximal ideal `𝔪`, and `J • ⊤ ≤ 𝔪 • ⊤ ≠ ⊤`. -/
@[sga "1 IV 2.1" "(i)"]
private lemma smul_top_ne_top_of_ne_top {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
    [Module R X] [Module.FaithfullyFlat R X] {J : Ideal R} (hJ : J ≠ ⊤) :
    J • (⊤ : Submodule R X) ≠ ⊤ := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal J hJ
  intro h
  refine ((Module.faithfullyFlat_iff R X).mp ‹Module.FaithfullyFlat R X›).2 hm
    (top_le_iff.mp ?_)
  exact h.ge.trans (Submodule.smul_mono_left hle)

/-- A linear map sends `I • ⊤` into the `B`-span of `I`-multiples, for `B` an `A`-algebra acting
compatibly on the target. -/
private lemma map_mem_map_smul_top {B : Type*} [CommRing B] [Algebra A B] {N : Type*}
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] (g : M →ₗ[A] N) {I : Ideal A}
    {y : M} (hy : y ∈ I • (⊤ : Submodule A M)) :
    g y ∈ I.map (algebraMap A B) • (⊤ : Submodule B N) := by
  refine Submodule.smul_induction_on hy ?_ fun a b ha hb => ?_
  · intro a ha n _
    rw [map_smul, ← IsScalarTower.algebraMap_smul B a]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ ha hb

/-- **The faithfully flat form of Stacks 0H7N.** -/
private theorem faithfullyFlat_of_faithfullyFlat_away_of_faithfullyFlat_quotSMulTop
    (Aₜ : Type*) [CommRing Aₜ] [Algebra A Aₜ] [IsLocalization.Away f Aₜ]
    (Mₜ : Type*) [AddCommGroup Mₜ] [Module A Mₜ] [Module Aₜ Mₜ] [IsScalarTower A Aₜ Mₜ]
    (g : M →ₗ[A] Mₜ) [IsLocalizedModule (Submonoid.powers f) g]
    (hA : IsSMulRegular A f) (hM : IsSMulRegular M f)
    (hflat : Module.FaithfullyFlat Aₜ Mₜ)
    (hQ : Module.FaithfullyFlat (A ⧸ Ideal.span {f}) (QuotSMulTop f M)) :
    Module.FaithfullyFlat A M := by
  have : Module.FaithfullyFlat Aₜ Mₜ := hflat
  have : Module.FaithfullyFlat (A ⧸ Ideal.span {f}) (QuotSMulTop f M) := hQ
  rw [Module.faithfullyFlat_iff]
  refine ⟨flat_of_flat_away_of_flat_quotSMulTop Aₜ Mₜ g hA hM hflat.toFlat hQ.toFlat,
    fun m hm hmtop => ?_⟩
  by_cases hf : f ∈ m
  · -- `f ∈ 𝔪`: the image of `𝔪` in `A/fA` is proper, and it spans `M/fM`.
    have hIle : Ideal.span {f} ≤ m := (Ideal.span_le).2 (by simpa using hf)
    have h𝔫top : m.map (Ideal.Quotient.mk (Ideal.span {f})) ≠ ⊤ := by
      intro h
      have h1 : (1 : A ⧸ Ideal.span {f}) ∈ m.map (Ideal.Quotient.mk (Ideal.span {f})) :=
        h ▸ Submodule.mem_top
      obtain ⟨a, ha, ha1⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h1
      have hsub : (1 : A) - a ∈ Ideal.span {f} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ha1, map_one, sub_self]
      refine hm.ne_top (Ideal.eq_top_iff_one m |>.2 ?_)
      simpa using m.add_mem (hIle hsub) ha
    refine smul_top_ne_top_of_ne_top (X := QuotSMulTop f M) h𝔫top (top_le_iff.mp ?_)
    intro x _
    obtain ⟨y, rfl⟩ := (f • (⊤ : Submodule A M)).mkQ_surjective x
    exact map_mem_map_smul_top (N := QuotSMulTop f M) (f • (⊤ : Submodule A M)).mkQ
      (by rw [hmtop]; exact Submodule.mem_top)
  · -- `f ∉ 𝔪`: `𝔪 A_f` is prime, hence proper, and it spans `M_f`.
    have hdisj : Disjoint (Submonoid.powers f : Set A) (m : Set A) := by
      rw [Set.disjoint_left]
      rintro x ⟨n, rfl⟩ hx
      exact hf (hm.isPrime.mem_of_pow_mem n hx)
    have hP : (m.map (algebraMap A Aₜ)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) Aₜ m hm.isPrime hdisj
    refine smul_top_ne_top_of_ne_top (X := Mₜ) hP.ne_top (top_le_iff.mp ?_)
    intro x _
    obtain ⟨⟨y, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers f) g x
    have hs' : (s : A) • x = g y := hs
    obtain ⟨u, hu⟩ := IsLocalization.map_units (M := Submonoid.powers f) Aₜ s
    have hux : (u : Aₜ) • x ∈ m.map (algebraMap A Aₜ) • (⊤ : Submodule Aₜ Mₜ) := by
      rw [hu, IsScalarTower.algebraMap_smul, hs']
      exact map_mem_map_smul_top g (by rw [hmtop]; exact Submodule.mem_top)
    have := Submodule.smul_mem _ ((u⁻¹ : Aₜˣ) : Aₜ) hux
    rwa [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at this

/-- **Stacks 0H7N.** -/
private theorem solution
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] (f : A)
    (Aₜ : Type*) [CommRing Aₜ] [Algebra A Aₜ] [IsLocalization.Away f Aₜ]
    (Mₜ : Type*) [AddCommGroup Mₜ] [Module A Mₜ] [Module Aₜ Mₜ] [IsScalarTower A Aₜ Mₜ]
    (g : M →ₗ[A] Mₜ) [IsLocalizedModule (Submonoid.powers f) g]
    (hA : IsSMulRegular A f) (hM : IsSMulRegular M f) :
    (Module.Flat Aₜ Mₜ → Module.Flat (A ⧸ Ideal.span {f}) (QuotSMulTop f M) →
        Module.Flat A M) ∧
      (Module.FaithfullyFlat Aₜ Mₜ →
        Module.FaithfullyFlat (A ⧸ Ideal.span {f}) (QuotSMulTop f M) →
        Module.FaithfullyFlat A M) :=
  ⟨fun h1 h2 => flat_of_flat_away_of_flat_quotSMulTop Aₜ Mₜ g hA hM h1 h2,
    fun h1 h2 =>
      faithfullyFlat_of_faithfullyFlat_away_of_faithfullyFlat_quotSMulTop Aₜ Mₜ g hA hM h1 h2⟩

end Stacks.Flatness.AwayAndQuotientCriterion

end

section

namespace Module

/-- **Stacks 0H7N.** Let `A` be a ring, let `M` be an `A`-module and let `f ∈ A` be a
nonzerodivisor on `A` and on `M`. If `M_f` is a flat `A_f`-module and `M/fM` is a flat
`A/fA`-module, then `M` is a flat `A`-module; the same with "flat" replaced by "faithfully flat".

Here `A_f` is any localization `Aₜ` of `A` away from `f` and `M_f` is any localization `Mₜ` of `M`
at the powers of `f`, while `M/fM` is `QuotSMulTop f M` as a module over `A ⧸ Ideal.span {f}`. -/
@[stacks 0H7N "The two forms of the lemma are the two components of the conjunction: they share
the hypotheses on `f`. `M_f` is an arbitrary localization away from `f` (`IsLocalization.Away`,
`IsLocalizedModule`) rather than the model, `M/fM` is `QuotSMulTop f M` over `A ⧸ Ideal.span {f}`,
and `f` a nonzerodivisor on `A` and on `M` is `IsSMulRegular A f` and `IsSMulRegular M f`."]
theorem flat_and_faithfullyFlat_of_flat_away_of_flat_quotSMulTop
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] (f : A)
    (Aₜ : Type*) [CommRing Aₜ] [Algebra A Aₜ] [IsLocalization.Away f Aₜ]
    (Mₜ : Type*) [AddCommGroup Mₜ] [Module A Mₜ] [Module Aₜ Mₜ] [IsScalarTower A Aₜ Mₜ]
    (g : M →ₗ[A] Mₜ) [IsLocalizedModule (Submonoid.powers f) g]
    (hA : IsSMulRegular A f) (hM : IsSMulRegular M f) :
    (Flat Aₜ Mₜ → Flat (A ⧸ Ideal.span {f}) (QuotSMulTop f M) → Flat A M) ∧
      (FaithfullyFlat Aₜ Mₜ → FaithfullyFlat (A ⧸ Ideal.span {f}) (QuotSMulTop f M) →
        FaithfullyFlat A M) :=
          Stacks.Flatness.AwayAndQuotientCriterion.solution f Aₜ Mₜ g hA hM

end Module

end


end


/-!
# The local criterion for flatness along an injective ring map

Let `φ : R → R'` be a map of commutative rings, let `I ⊆ R` be a nilpotent ideal and let `M` be
an `R`-module. This file proves Stacks 051J: if `φ` is injective, `M/IM` is flat over `R/I` and
`R' ⊗_R M` is flat over `R'`, then `M` is flat over `R`.

The source bootstraps the square-zero criterion (Stacks 051I, in this repository
`flat_quot_idealTwo_smul_top_of_flat_quot_and_flat_baseChange`) along the tower `I₁ = I`,
`I_{n+1} = φ⁻¹(φ(I_n)² R') = idealTwo I_n R'`: each step turns flatness of `M/I_nM` over `R/I_n`
into flatness of `M/I_{n+1}M` over `R/I_{n+1}`, while `φ(I_{n+1}) ⊆ φ(I_n)² R'` makes the
generated ideals `φ(I_n) R'` square at every step, so that `φ(I_n) R' ⊆ (φ(I) R')^{2ⁿ⁻¹}` vanishes
once `I` is nilpotent. Injectivity of `φ` then upgrades `φ(I_n) R' = 0` to `I_n = 0`, and the
`n`-th stage of the induction reads `M/0 = M` is flat over `R/0 = R`.

## Main results

* `Stacks.Flatness.NilpotentDescent.solution`: Stacks 051J, in the shape of
  `Module.Flat.of_flat_quotient_of_flat_tensorProduct_of_isNilpotent_of_injective`.

## Implementation notes

The tower is not built as a function `ℕ → Ideal R`. Instead the induction is run on the single
statement `flat_of_flat_quotient_of_map_pow_eq_bot`, which is universally quantified over the
ideal: at stage `n` the hypothesis is that `(φ(J) R')^{2ⁿ} = 0`, and the inductive step replaces
`J` by `idealTwo J R'`, whose image ideal squares into that of `J` by `map_idealTwo_le_sq`.
Quantifying over `J` rather than iterating a definition removes the need for any lemma about the
tower and makes the descending exponent the induction variable.

## References

* [Stacks Project, Tag 051J](https://stacks.math.columbia.edu/tag/051J)
-/


open TensorProduct

namespace Stacks.Flatness.NilpotentDescent

section Helpers

variable {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
  {M : Type*} [AddCommGroup M] [Module R M]

/-- A module is flat as soon as its reduction modulo the zero ideal is flat over `R ⧸ 0`: the
`R`-module `R ⧸ (0)` is flat, so flatness composes along `R → R ⧸ (0)` by `Module.Flat.trans`,
and `M ⧸ 0 · M` is `R`-linearly isomorphic to `M`. -/
private lemma flat_of_flat_quotient_smul_top_of_eq_bot {I : Ideal R} (hI : I = ⊥)
    (h : Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) : Module.Flat R M := by
  subst hI
  have hR : Module.Flat R (R ⧸ (⊥ : Ideal R)) := .of_linearEquiv (Submodule.quotEquivOfEqBot _ rfl)
  have hM : Module.Flat R (M ⧸ (⊥ : Ideal R) • (⊤ : Submodule R M)) :=
    Module.Flat.trans R (R ⧸ (⊥ : Ideal R)) (M ⧸ (⊥ : Ideal R) • (⊤ : Submodule R M))
  have e : M ≃ₗ[R] M ⧸ (⊥ : Ideal R) • (⊤ : Submodule R M) :=
    (Submodule.quotEquivOfEqBot _ (Submodule.bot_smul _)).symm
  exact .of_linearEquiv e

/-- The ideal generated by the image of `idealTwo J R' = φ⁻¹(φ(J²) R')` is contained in the square
of the ideal generated by the image of `J`: `φ(idealTwo J R') R' ⊆ φ(J²) R' = (φ(J) R')²`. -/
private lemma map_idealTwo_le_sq (J : Ideal R) :
    Ideal.map (algebraMap R R') (idealTwo J R') ≤ Ideal.map (algebraMap R R') J ^ 2 :=
  Ideal.map_comap_le.trans_eq (Ideal.map_pow _ _ _)

/-- Passing from `J` to `idealTwo J R'` costs one squaring: if `(φ(J) R')^{2ⁿ⁺¹} = 0` then
`(φ(idealTwo J R') R')^{2ⁿ} = 0`, the latter ideal being contained in `(φ(J) R')²` by
`map_idealTwo_le_sq`, whose `2ⁿ`-th power is `(φ(J) R')^{2ⁿ⁺¹}`. -/
private lemma map_idealTwo_pow_eq_bot {J : Ideal R} {n : ℕ}
    (hJ : Ideal.map (algebraMap R R') J ^ 2 ^ (n + 1) = ⊥) :
    Ideal.map (algebraMap R R') (idealTwo J R') ^ 2 ^ n = ⊥ :=
  le_bot_iff.mp <| calc Ideal.map (algebraMap R R') (idealTwo J R') ^ 2 ^ n
      ≤ (Ideal.map (algebraMap R R') J ^ 2) ^ 2 ^ n := pow_le_pow_left' (map_idealTwo_le_sq J) _
    _ = ⊥ := by rwa [← pow_mul, ← pow_succ']

/-- The induction behind Stacks 051J, with the number of remaining squarings as the variable: if
the ideal generated by `φ(J)` in `R'` satisfies `(φ(J) R')^{2ⁿ} = 0` and `M/JM` is flat over
`R/J`, then `M` is flat over `R`. The step from `n + 1` to `n` replaces `J` by `idealTwo J R'`,
for which the square-zero criterion (Stacks 051I) supplies flatness of the reduction and
`map_idealTwo_pow_eq_bot` the vanishing; the base case `n = 0` says `φ(J) R' = 0`, whence `J = 0`
because `φ` is injective. -/
@[ega "IV 11.4.9" "sufficiency (flat case)"]
private lemma flat_of_flat_quotient_of_map_pow_eq_bot
    (hφ : Function.Injective (algebraMap R R')) (hM' : Module.Flat R' (R' ⊗[R] M)) (n : ℕ) :
    ∀ J : Ideal R, Ideal.map (algebraMap R R') J ^ 2 ^ n = ⊥ →
      Module.Flat (R ⧸ J) (M ⧸ J • (⊤ : Submodule R M)) → Module.Flat R M := by
  induction n with
  | zero =>
    intro J hJ hflat
    exact flat_of_flat_quotient_smul_top_of_eq_bot
      ((Ideal.map_eq_bot_iff_of_injective hφ).mp (by simpa using hJ)) hflat
  | succ n ih =>
    intro J hJ hflat
    exact ih _ (map_idealTwo_pow_eq_bot hJ)
      (flat_quot_idealTwo_smul_top_of_flat_quot_and_flat_baseChange J hflat hM')

end Helpers

/-- Stacks 051J: let `I` be a nilpotent ideal of `R` and `R → R'` an injective ring map. If
`M/IM` is flat over `R/I` and `R' ⊗[R] M` is flat over `R'`, then `M` is flat over `R`. -/
public theorem solution {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    {M : Type*} [AddCommGroup M] [Module R M] (I : Ideal R)
    (hI : IsNilpotent I) (hφ : Function.Injective (algebraMap R R'))
    (hMI : Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)))
    (hM' : Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat R M := by
  obtain ⟨k, hk⟩ := hI
  have hmap : Ideal.map (algebraMap R R') I ^ k = ⊥ := by rw [← Ideal.map_pow, hk]; simp
  exact flat_of_flat_quotient_of_map_pow_eq_bot hφ hM' k I
    (le_bot_iff.mp ((Ideal.pow_le_pow_right Nat.lt_two_pow_self.le).trans hmap.le)) hMI

end Stacks.Flatness.NilpotentDescent

/-!
# The local criterion for flatness along an injective ring map

Let `φ : R → R'` be a map of commutative rings, let `I ⊆ R` be a **nilpotent** ideal and let `M`
be an `R`-module. If `φ` is injective, `M/IM` is flat over `R/I`, and the base change `R' ⊗_R M`
is flat over `R'`, then `M` is flat over `R`. So flatness of a module may be tested after a base
change that is merely injective — no flatness of `φ` itself is required, in contrast with
faithfully flat descent (`Module.Flat.of_flat_tensorProduct`) — provided one already knows
flatness modulo a nilpotent ideal.

The source's proof bootstraps the square-zero case. Put `I₁ = I` and, inductively,
`I_{n+1} = φ⁻¹(φ(I_n)² R')`. The square-zero criterion (Stacks 051I) upgrades flatness of
`M/I_nM` over `R/I_n` to flatness of `M/I_{n+1}M` over `R/I_{n+1}`, so by induction `M/I_nM` is
flat over `R/I_n` for every `n ≥ 1`. Since `φ(I_{n+1}) ⊆ φ(I)^{2ⁿ} R'` and `I` is nilpotent,
`φ(I_n) = 0` for some `n`; injectivity of `φ` then forces `I_n = 0` for that `n`, and the `n`-th
stage of the induction is the assertion that `M` is flat over `R`. That is the one place
injectivity is spent, and it is spent only to convert nilpotence of `φ(I)` into nilpotence of `I`
along the tower.

## Main results

* `Module.Flat.of_flat_quotient_of_flat_tensorProduct_of_isNilpotent_of_injective`: a module is
  flat as soon as, for some nilpotent ideal `I`, the reduction `M/IM` is flat over `R/I` and the
  base change of `M` along an injective ring map is flat.

## Implementation notes

The ring map `φ` is `algebraMap R R'` for an `[Algebra R R']` structure, which is Mathlib's
spelling of a map of commutative rings and simultaneously supplies the `R'`-module structure on
the base change; hypothesis (2) is then `Function.Injective (algebraMap R R')`, and a caller
holding a `FaithfulSMul R R'` instance discharges it by `FaithfulSMul.algebraMap_injective R R'`.

The reduction `M/IM` is `M ⧸ I • (⊤ : Submodule R M)`, whose canonical `R ⧸ I`-module structure
exists because `I` annihilates it, and the base change is the concrete `R' ⊗[R] M` with `R'`
acting through the left factor, that is via `φ`. The concrete tensor product is how Mathlib states
the sibling descent theorem `Module.Flat.of_flat_tensorProduct`. The variant in which `R' ⊗[R] M`
is replaced by an arbitrary `R'`-module `N` together with an `f : M →ₗ[R] N` satisfying
`IsBaseChange R' f` — the shape taken by the Artinian specialisation
`Module.Flat.of_flat_baseChange_of_injective` (Stacks 051L) — follows by transporting flatness
along the `R'`-linear equivalence `IsBaseChange.equiv`, and conversely specialises to the form
below by `TensorProduct.isBaseChange`; nothing is lost either way.

All four hypotheses are explicit rather than instance arguments, `Module.Flat (R ⧸ I) _` not being
findable by instance search and the two flatness hypotheses being the mathematical content.

Generality deliberately not taken: nilpotence of `I` cannot be weakened to `I ≤ Ideal.jacobson ⊥`,
even for `R` a discrete valuation ring. For `R = ℤ_p`, `I = (p) = Ideal.jacobson ⊥`, `R' = ℚ_p`
and `M = ℚ_p ⧸ ℤ_p` the map is injective, `M/IM = 0` is flat over `R/I` since `M` is `p`-divisible,
and `R' ⊗_R M = 0` is flat over `ℚ_p`, yet `M` is torsion and hence not flat over `ℤ_p`. The
statements obtained by replacing nilpotence with completeness are separate tags.

Faithfulness. (1) No hypothesis is dead: for `R = ℤ`, `R' = ℚ`, `I = 2ℤ` and `M = ℤ ⧸ 2ℤ` only
nilpotence of `I` fails and the conclusion fails with it; for `R = k[x] ⧸ (x ^ 2)`, `R' = k[y]`
with `y ↦ 0`, `I = (x)` and `M = R ⧸ (x)` only injectivity fails, since `M/IM = k` is flat over
`R/I = k` and `R' ⊗_R M = k` is flat over `k`, while `M` is not flat over `R`, not being free; for
`R = k[y][x] ⧸ (x ^ 2)`, `R' = k[y, y⁻¹][x] ⧸ (x ^ 2)`, `I = (x)` and `M = R ⧸ (y)` only flatness
of the reduction fails, `φ` being injective and `R' ⊗_R M = 0` flat; and for
`R = R' = k[x] ⧸ (x ^ 2)`, `I = (x)` and `M = R ⧸ (x)` only flatness of the base change fails. (2)
The scalars and base are the source's: the reduction is flat over `R ⧸ I`, the base change over
`R'`, the conclusion is flatness of `M` over `R` itself, and nothing is localised. (3) The maps
the source names are pinned: the ring map is `algebraMap R R'`, not merely some injection; the
reduction is by the given `I` acting on `⊤`, not by an abstract submodule; and the base change is
`R' ⊗[R] M` with the `R'`-action along `φ`. (4) The instantiation is not degenerate: for
`R = ℤ ⧸ 4`, `I = (2)` and `R' = R[t]` all four hypotheses hold of `M = R` and of `M = R ^ (ℕ)`
with the conclusion true, whereas for `R' = R` and `M = ℤ ⧸ 2` hypotheses (1), (2) and (3) hold
while (4) and the conclusion both fail.

## References

* [Stacks Project, Tag 051J](https://stacks.math.columbia.edu/tag/051J)
-/

open TensorProduct

namespace Module.Flat

/-- **Stacks 051J**: the local criterion for flatness along an injective ring map. Let
`φ : R → R'` be a map of commutative rings, `I ⊆ R` a nilpotent ideal and `M` an `R`-module. If
`φ = algebraMap R R'` is injective, `M/IM` is flat over `R ⧸ I` and the base change `R' ⊗[R] M`
is flat over `R'`, then `M` is flat over `R`. Compare `Module.Flat.of_flat_tensorProduct`, which
descends flatness along a faithfully flat ring map with no nilpotent ideal in sight, and
`Module.Flat.of_flat_baseChange_of_injective` (Stacks 051L), the case where `R` is Artinian and
`I` is its Jacobson radical, so that flatness of the reduction is automatic. The proof is the
source's: the tower `I₁ = I`, `I_{n+1} = φ⁻¹(φ(I_n) ^ 2 R')` reaches `0` because `I` is nilpotent
and `φ` is injective, and each step preserves flatness of the reduction by the square-zero
criterion (Stacks 051I). -/
@[stacks 051J "The ring map is `algebraMap R R'`; `M/IM` is `M ⧸ I • ⊤` with its canonical
`R ⧸ I`-action and the base change is `R' ⊗[R] M`, acted on by `R'` through the left factor. See
the module docstring.", ega "IV 11.4.1" "special case", ega "IV 11.4.9" "sufficiency (flat case)"]
public theorem of_flat_quotient_of_flat_tensorProduct_of_isNilpotent_of_injective
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    {M : Type*} [AddCommGroup M] [Module R M] (I : Ideal R)
    (hI : IsNilpotent I) (hφ : Function.Injective (algebraMap R R'))
    (hMI : Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)))
    (hM' : Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat R M :=
      Stacks.Flatness.NilpotentDescent.solution (R' := R') I hI hφ hMI hM'

end Module.Flat

end

@[expose] public section

open TensorProduct

namespace Stacks.Flatness

/-- Flatness of `N/IN` over `R/I` passes to `N/(IA)N` over `A/IA` for a localization `A` of `R`
and `N` an `A`-module.

`A/IA` is the localization of `R/I` at the image of `T` (`IsLocalization.of_surjective` applied
to the two quotient maps), so `Module.flat_iff_of_isLocalization` reduces the goal to flatness
over `R/I`, and there `Ideal.smul_restrictScalars` identifies `N/(IA)N` with `N/IN`. -/
public theorem flat_quotient_map_of_isLocalization {R : Type*} [CommRing R] (T : Submonoid R)
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization T A] (I : Ideal R) (N : Type*)
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (h : Module.Flat (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N)))) :
    Module.Flat (A ⧸ I.map (algebraMap R A))
      (N ⧸ (I.map (algebraMap R A) • (⊤ : Submodule A N))) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) T)
      (A ⧸ I.map (algebraMap R A)) :=
    IsLocalization.of_surjective T A (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (I.map (algebraMap R A))) Ideal.Quotient.mk_surjective rfl (by simp)
  let _ : Module (R ⧸ I) (N ⧸ (I.map (algebraMap R A) • (⊤ : Submodule A N))) :=
    Module.compHom _ (algebraMap (R ⧸ I) (A ⧸ I.map (algebraMap R A)))
  have _ : IsScalarTower (R ⧸ I) (A ⧸ I.map (algebraMap R A))
      (N ⧸ (I.map (algebraMap R A) • (⊤ : Submodule A N))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : IsScalarTower R (R ⧸ I) (N ⧸ (I.map (algebraMap R A) • (⊤ : Submodule A N))) := by
    refine IsScalarTower.of_algebraMap_smul fun r x => ?_
    calc (algebraMap R (R ⧸ I)) r • x
        = algebraMap (R ⧸ I) (A ⧸ I.map (algebraMap R A)) (algebraMap R (R ⧸ I) r) • x := rfl
      _ = algebraMap A (A ⧸ I.map (algebraMap R A)) (algebraMap R A r) • x := by
          rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      _ = algebraMap R A r • x := IsScalarTower.algebraMap_smul _ _ _
      _ = r • x := IsScalarTower.algebraMap_smul _ _ _
  rw [Module.flat_iff_of_isLocalization (A ⧸ I.map (algebraMap R A))
    (Algebra.algebraMapSubmonoid (R ⧸ I) T)]
  have hEq : Submodule.restrictScalars R (I.map (algebraMap R A) • (⊤ : Submodule A N))
      = I • (⊤ : Submodule R N) := by
    rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (hEq ▸ Submodule.Quotient.restrictScalarsEquiv R
        (I.map (algebraMap R A) • (⊤ : Submodule A N))).symm)

end Stacks.Flatness

end
