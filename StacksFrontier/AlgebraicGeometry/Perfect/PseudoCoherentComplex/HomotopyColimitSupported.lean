module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.DetectingBoundednessOfAPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.QuasiCompactQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ApproximationTriangle
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction

/-!
# Pseudo-coherent objects supported on a closed subset as homotopy colimits of perfect ones

Let `X` be a quasi-compact and quasi-separated scheme, let `T ⊆ X` be a closed subset whose
complement is quasi-compact and let `K` be an object of `D(𝒪_X)` whose cohomology sheaves are
supported on `T`. Then `K` is pseudo-coherent if and only if `K = hocolim Kₙ` for a system of
perfect objects `Kₙ` supported on `T` such that `τ_{≥-n}Kₙ ⟶ τ_{≥-n}K` is an isomorphism for
every `n` ([Stacks, Tag 0DKC]; the same statement is [Stacks, Tag 0DJP] in the chapter on
derived categories of schemes).

## Main results

* `Stacks.DerivedColimit.isHomotopyColimitWith_of_eventually_isIso_homology`: in the derived
  category of a Grothendieck abelian category, a compatible family of maps `cₙ : Kₙ ⟶ K` out of
  a system exhibits `K` as the derived colimit of the system as soon as in every degree `i` the
  maps `Hⁱ(cₙ)` are eventually invertible.
* `AlgebraicGeometry.PerfectApproximation.exists_window_subsingleton_hom_of_isPerfect`:
  [Stacks, Tag 09M4] part (1) at the locally small model of `D(𝒪_X)`.
* `AlgebraicGeometry.PerfectApproximation.exists_supported_perfect_factorization`: the induction
  step of the source's proof — a map from a perfect object to `K` factors through a perfect
  approximation of `K` supported on `T` which is invertible on cohomology in any prescribed
  range of high degrees.
* `AlgebraicGeometry.PerfectApproximation.isPseudoCoherent_iff_exists_isHomotopyColimitWith`:
  [Stacks, Tag 0DKC].

## Implementation notes

**The proof** is the source's. For `(1) ⟹ (2)`, approximations by perfect complexes supported
on `T` exist for every triple `(T, K, m)` ([Stacks, Tag 08ES]). Given a perfect `Kₙ ⟶ K`,
[Stacks, Tag 09M4] gives a window `[a, b]` of degrees in which vanishing of the cohomology of an
object of `D_QCoh(𝒪_X)` forbids nonzero maps out of `Kₙ`. An approximation `Kₙ₊₁ ⟶ K` of
`(T, K, min(a - 1, -n - 2))` has a cone `C` in `D_QCoh(𝒪_X)` with no cohomology from degree
`a` on, so `Kₙ ⟶ K ⟶ C` vanishes and `Kₙ ⟶ K` factors through `Kₙ₊₁` ([Stacks, Tag 0149]).
That `K` is the derived colimit of the tower is [Stacks, Tag 0CRK] for the cohomology functors:
the colimit of `Hⁱ(Kₙ)` is computed by the derived colimit, and the system `Hⁱ(Kₙ)` is
eventually constant with value `Hⁱ(K)`. For `(2) ⟹ (1)`, each `Kₙ` is pseudo-coherent, and
`Kₙ ⟶ K` is an isomorphism on cohomology in degrees `≥ -n`, so `K` is `m`-pseudo-coherent for
every `m` (`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_approximation`).

**Indexing.** The source indexes the system from `1`; here it is indexed by `ℕ` from `0`, and
the member at index `n` is the source's `K_{n+1}`. So the condition at index `n` is that
`τ_{≥-(n+1)}Kₙ ⟶ τ_{≥-(n+1)}K` is an isomorphism, which is the source's condition verbatim.

**Derived colimits.** "`K = hocolim Kₙ`" is
`CategoryTheory.Pretriangulated.IsHomotopyColimitWith F K c`: there is a distinguished triangle
`⊕ Kₙ ⟶ ⊕ Kₙ ⟶ K ⟶` whose first map is `1 - fₙ` and whose second map restricts to `cₙ` on the
`n`-th summand ([Stacks, Tag 090Z]). The truncation condition is imposed on these coprojections
`cₙ`, which are the maps `Kₙ ⟶ K` the source refers to. The direct sum `⊕ Kₙ` exists in
`D(𝒪_X)` (`Stacks.DerivedColimit.hasColimitsOfShape_discrete_nat_derivedCategory`), which is a
local instance here; any other proof of its existence is the same, existence being a
proposition.

**The model of `D(𝒪_X)`.** Everything is stated at the ambient instance on `D(𝒪_X)`, the
locally small model, and no model is fixed by a local instance. The perfect approximations of
[Stacks, Tag 08ES] are read there through
`AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes_iff_locallySmall`, and
[Stacks, Tag 09M4], proved at the standard model, is transported along the comparison
equivalence `Stacks.Injectives.grothendieckModelEquiv`, which is the identity on objects.

**Support.** "`K` is supported on `T`" is
`Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn`: every cohomology sheaf of `K`
has vanishing stalks at the points off `T` ([Stacks, Tag 08DA]). It is that predicate, which takes
the model of `D(𝒪_X)` as an instance, and not `AlgebraicGeometry.CohomologySupportedOn`, which
is pinned to the standard model, so it is written with its full name inside the namespace
`AlgebraicGeometry`.

## References

* [Stacks Project, Tag 0DKC](https://stacks.math.columbia.edu/tag/0DKC)
* [Stacks Project, Tag 0DJP](https://stacks.math.columbia.edu/tag/0DJP)
* [Stacks Project, Tag 0DKB](https://stacks.math.columbia.edu/tag/0DKB)
* [Stacks Project, Tag 08ES](https://stacks.math.columbia.edu/tag/08ES)
* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 0CRK](https://stacks.math.columbia.edu/tag/0CRK)
* [Stacks Project, Tag 0149](https://stacks.math.columbia.edu/tag/0149)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

universe w v u

namespace Stacks.DerivedColimit

/-! ### Derived colimits in the derived category of a Grothendieck abelian category -/

section Grothendieck

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{w} A]

/-- The derived category of a Grothendieck abelian category has countable direct sums. -/
theorem hasColimitsOfShape_discrete_nat_derivedCategory :
    HasColimitsOfShape (Discrete ℕ) (DerivedCategory A) :=
  have := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory A
    (ULift.{v} ℕ)
  hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)

/-- The cohomology functors of the derived category of a Grothendieck abelian category commute
with countable direct sums. -/
theorem preservesColimitsOfShape_discrete_nat_homologyFunctor (i : ℤ) :
    PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor A i) :=
  have := Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor A
    (J := ULift.{v} ℕ) i
  preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _

/-- Colimits over `ℕ` exist in a Grothendieck abelian category. -/
theorem hasColimitsOfShape_nat : HasColimitsOfShape ℕ A :=
  hasColimitsOfShape_of_equivalence (AsSmall.equiv.{0, 0, v}).symm

/-- Colimits over `ℕ` are exact in a Grothendieck abelian category. -/
theorem hasExactColimitsOfShape_nat : HasExactColimitsOfShape ℕ A :=
  HasExactColimitsOfShape.of_domain_equivalence A (AsSmall.equiv.{0, 0, v}).symm

variable {A}

/-- A compatible family of maps out of a system over `ℕ` satisfies `c m = f ≫ c n` along every
transition map `f`. -/
theorem comp_eq_of_le {D : Type*} [Category D] (F : ℕ ⥤ D) {K : D} (c : ∀ n, F.obj n ⟶ K)
    (hc : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ c (n + 1) = c n) {m n : ℕ} (h : m ≤ n) :
    F.map (homOfLE h) ≫ c n = c m := by
  simpa using (NatTrans.ofSequence (F := F) (G := (Functor.const ℕ).obj K) c
    (fun n => by simpa using hc n)).naturality (homOfLE h)

/-- **A derived colimit detected by cohomology.** Let `A` be a Grothendieck abelian category,
let `F : ℕ ⥤ D(A)` be a system and let `cₙ : Kₙ ⟶ K` be maps compatible with the transition
maps. If in every degree `i` the maps `Hⁱ(cₙ)` are isomorphisms for all large `n`, then `K` is
the derived colimit of the system with coprojections `cₙ`.

This is [Stacks, Tag 0CRK] applied to the cohomology functors, which commute with countable
direct sums: the cohomology of the third vertex `C` of a triangle on `1 - fₙ` is
`colim Hⁱ(Kₙ)`, which is `Hⁱ(K)` because the system `Hⁱ(Kₙ)` is eventually constant with value
`Hⁱ(K)`; so the map `C ⟶ K` induced by the `cₙ` is an isomorphism on all cohomology sheaves. -/
theorem isHomotopyColimitWith_of_eventually_isIso_homology (F : ℕ ⥤ DerivedCategory A)
    [HasCoproduct F.obj] {K : DerivedCategory A} (c : ∀ n, F.obj n ⟶ K)
    (hc : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ c (n + 1) = c n)
    (hiso : ∀ i : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor A i).map (c n))) :
    IsHomotopyColimitWith F K c := by
  have := hasColimitsOfShape_nat A
  have := hasExactColimitsOfShape_nat A
  obtain ⟨C, p, q, hT⟩ :=
    distinguished_cocone_triangle (Stacks.CountableCoproducts.oneSubShift F)
  have hone : Stacks.CountableCoproducts.oneSubShift F ≫ Sigma.desc c = 0 := by
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [← Category.assoc, Stacks.CountableCoproducts.ι_oneSubShift, Preadditive.sub_comp,
      Category.assoc, Sigma.ι_desc, Sigma.ι_desc, hc, sub_self, comp_zero]
  obtain ⟨b, hb⟩ := Triangle.yoneda_exact₂ _ hT (Sigma.desc c) hone
  have hpb : ∀ n, Sigma.ι F.obj n ≫ p ≫ b = c n := fun n => by
    have := congrArg (fun φ => Sigma.ι F.obj n ≫ φ) hb
    simpa using this.symm
  have hbiso : IsIso b := by
    rw [DerivedCategory.isIso_iff]
    intro i
    let H := DerivedCategory.homologyFunctor A i
    have := preservesColimitsOfShape_discrete_nat_homologyFunctor A i
    obtain ⟨e, he⟩ := exists_iso_colimit_of_isHomotopyColimit F H p q hT
    obtain ⟨N, hN⟩ := hiso i
    have hcomm : ∀ {m n : ℕ} (f : m ⟶ n), F.map f ≫ c n = c m := fun f => by
      rw [Subsingleton.elim f (homOfLE (leOfHom f))]
      exact comp_eq_of_le F c hc _
    let cK : Cocone (F ⋙ H) :=
      { pt := H.obj K
        ι :=
          { app := fun n => H.map (c n)
            naturality := fun m n f => by
              simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
                Functor.const_obj_map, Category.comp_id, ← H.map_comp, hcomm f] } }
    have hev : (F ⋙ H).IsEventuallyConstantFrom N := by
      intro n f
      have : IsIso (H.map (F.map f) ≫ H.map (c n)) := by
        rw [← H.map_comp, hcomm f]
        exact hN N le_rfl
      have := hN n (leOfHom f)
      exact (isIso_comp_right_iff (H.map (F.map f)) (H.map (c n))).1 ‹_›
    have : IsIso (cK.ι.app N) := hN N le_rfl
    have hfac : e.hom ≫ H.map b = colimit.desc (F ⋙ H) cK := by
      refine colimit.hom_ext fun n => ?_
      rw [← Category.assoc, he, ← H.map_comp, Category.assoc, hpb, colimit.ι_desc]
    have : IsIso (colimit.desc (F ⋙ H) cK) :=
      inferInstanceAs (IsIso ((colimit.isColimit (F ⋙ H)).coconePointUniqueUpToIso
        (hev.isColimitOfIsIso cK)).hom)
    have : IsIso (e.hom ≫ H.map b) := by
      rw [hfac]
      infer_instance
    exact (isIso_comp_left_iff e.hom (H.map b)).1 this
  exact (IsHomotopyColimitWith.of_iso ⟨p, q, hT, fun _ => rfl⟩ (asIso b)).congr_coprojections
    fun n => by simpa using hpb n

end Grothendieck

end Stacks.DerivedColimit

namespace AlgebraicGeometry.PerfectApproximation

open Stacks.Cohomology.PerfectComplexes (IsPerfect)

variable (X : Scheme.{u})

attribute [local instance] Stacks.DerivedColimit.hasColimitsOfShape_discrete_nat_derivedCategory

/-! ### [Stacks, Tag 09M4] at the locally small model -/

/-- **[Stacks, Tag 09M4], part (1), at the locally small model of `D(𝒪_X)`.** Let `X` be a
quasi-compact and quasi-separated scheme and let `K` be a perfect object of `D(𝒪_X)`. There are
integers `a ≤ b` such that every `L ∈ D_QCoh(𝒪_X)` whose cohomology sheaves vanish in the degrees
`a, …, b` admits no nonzero morphism `K ⟶ L`.

This is `Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_qcqs`, stated at the
standard model, transported along the comparison equivalence
`Stacks.Injectives.grothendieckModelEquiv`, which is the identity on objects and bijective on
morphisms; perfectness, quasi-coherence and vanishing of cohomology sheaves do not depend on the
model. -/
theorem exists_window_subsingleton_hom_of_isPerfect [CompactSpace X] [QuasiSeparatedSpace X]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K) :
    ∃ a b : ℤ, a ≤ b ∧
      ∀ L : DerivedCategory X.Modules,
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsQuasicoherent) →
        (∀ i : ℤ, a ≤ i → i ≤ b → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj L)) →
        Subsingleton (K ⟶ L) := by
  obtain ⟨a, b, hab, h⟩ := Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_qcqs X
    K ((isPerfect_standard_iff K).2 hK)
  refine ⟨a, b, hab, fun L hqc hzero => ?_⟩
  have hstd := h L (fun i => (isQuasicoherent_homology_standard_iff L i).2 (hqc i))
    (fun i hi hi' => (isZero_homology_standard_iff L i).2 (hzero i hi hi'))
  let G := (Stacks.Injectives.grothendieckModelEquiv X.Modules).functor
  let G' := (Stacks.Injectives.grothendieckModelEquiv X.Modules).inverse
  have hGG' : ∀ α : K ⟶ L, G.map (G'.map α) = α := fun α => Equiv.apply_symm_apply _ α
  refine ⟨fun f g => ?_⟩
  rw [← hGG' f, ← hGG' g, @Subsingleton.elim _ hstd (G'.map f) (G'.map g)]

/-! ### Supported perfect approximations of a pseudo-coherent object -/

variable {X}

/-- **Approximations by perfect complexes supported on `T`.** On a quasi-compact and
quasi-separated scheme, if `T` is closed with quasi-compact complement and `K` is pseudo-coherent
and supported on `T`, then approximation holds for `(T, K, m)` for every `m`: there are a perfect
`P` supported on `T` and a map `P ⟶ K` which is an isomorphism on cohomology above `m` and
surjective in degree `m` ([Stacks, Tag 08ES]). -/
theorem exists_supported_perfect_approximatesFrom [CompactSpace X] [QuasiSeparatedSpace X]
    {T : Set X} (hT : IsClosed T) (hTc : IsCompact Tᶜ) {K : DerivedCategory X.Modules}
    (hK : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T K)
    (hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (m : ℤ) :
    ∃ P : DerivedCategory X.Modules, IsPerfect (X := X.toRingedSpace) P ∧
      Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T P ∧
        ∃ α : P ⟶ K, DerivedCategory.ApproximatesFrom α m := by
  have hTc' : IsRetrocompact Tᶜ :=
    (QuasiSeparatedSpace.isRetrocompact_iff_isCompact hT.isOpen_compl).2 hTc
  obtain ⟨r, hr⟩ := (hasApproximationByPerfectComplexes_iff_locallySmall X).1
    (hasApproximationByPerfectComplexes X) T hT hTc'
  exact hr K m (isQuasicoherentDerived_of_isPseudoCoherent X K hpc)
    ((RingedSpace.isPseudoCoherent_iff_forall K).1 hpc (m - r))
    (fun i x _ hx => hK i x hx)

/-- **The induction step.** On a quasi-compact and quasi-separated scheme, let `T` be closed with
quasi-compact complement and let `K` be pseudo-coherent and supported on `T`. Every map `f`
from a perfect object `P` to `K` factors as `P ⟶ Q ⟶ K` through a perfect `Q` supported on `T`
whose map `Q ⟶ K` is an isomorphism on cohomology in every degree `≥ a`, for any prescribed `a`.

Following the source: take a window `[a₀, b₀]` for `P` as in [Stacks, Tag 09M4] and an
approximation `β : Q ⟶ K` of `(T, K, min(a₀ - 1, a - 1))`. The cone `C` of `β` lies in
`D_QCoh(𝒪_X)` and has no cohomology from degree `min(a₀ - 1, a - 1)` on, so `Hom(P, C) = 0`; the
composite `P ⟶ K ⟶ C` vanishes and `f` factors through `β` ([Stacks, Tag 0149]). -/
theorem exists_supported_perfect_factorization [CompactSpace X] [QuasiSeparatedSpace X]
    {T : Set X} (hT : IsClosed T) (hTc : IsCompact Tᶜ) {K : DerivedCategory X.Modules}
    (hK : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T K)
    (hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K)
    {P : DerivedCategory X.Modules} (hP : IsPerfect (X := X.toRingedSpace) P) (f : P ⟶ K)
    (a : ℤ) :
    ∃ (Q : DerivedCategory X.Modules) (g : P ⟶ Q) (β : Q ⟶ K),
      IsPerfect (X := X.toRingedSpace) Q ∧
        Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T Q ∧
        g ≫ β = f ∧
          ∀ i : ℤ, a ≤ i → IsIso ((DerivedCategory.homologyFunctor X.Modules i).map β) := by
  obtain ⟨a₀, b₀, -, hwin⟩ := exists_window_subsingleton_hom_of_isPerfect X P hP
  obtain ⟨Q, hQ, hQT, β, hβ⟩ :=
    exists_supported_perfect_approximatesFrom hT hTc hK hpc (min (a₀ - 1) (a - 1))
  obtain ⟨C, v, w, hT₃⟩ := distinguished_cocone_triangle β
  have hQqc := isQuasicoherentDerived_of_isPseudoCoherent X Q
    (RingedSpace.IsPerfect.isPseudoCoherent hQ)
  have hKqc := isQuasicoherentDerived_of_isPseudoCoherent X K hpc
  have hCqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj C).IsQuasicoherent :=
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ext_of_isTriangulatedClosed₃ _ hT₃
        hQqc hKqc
  have hC : Subsingleton (P ⟶ C) := hwin C hCqc fun i hi _ =>
    isZero_homology_obj₃_of_distinguished (min (a₀ - 1) (a - 1)) _ hT₃ hβ.1 hβ.2 i (by omega)
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT₃ f (@Subsingleton.elim _ hC _ _)
  exact ⟨Q, g, β, hQ, hQT, hg.symm, fun i hi => hβ.1 i (by omega)⟩

/-! ### The tower of approximations -/

/-- A member of the tower of the proof of [Stacks, Tag 0DKC] at index `n`: a perfect object
supported on `T` with a map to `K` which is an isomorphism on cohomology in degrees
`≥ -(n + 1)`. -/
private structure Stage (T : Set X) (K : DerivedCategory X.Modules) (n : ℕ) where
  obj : DerivedCategory X.Modules
  perfect : IsPerfect (X := X.toRingedSpace) obj
  supported : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T obj
  toTarget : obj ⟶ K
  isIso : ∀ i : ℤ, -((n : ℤ) + 1) ≤ i →
    IsIso ((DerivedCategory.homologyFunctor X.Modules i).map toTarget)

/-- The first member of the tower: an approximation of `(T, K, -2)`. -/
private theorem exists_stage_zero [CompactSpace X] [QuasiSeparatedSpace X]
    {T : Set X} (hT : IsClosed T) (hTc : IsCompact Tᶜ) {K : DerivedCategory X.Modules}
    (hK : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T K)
    (hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) :
    Nonempty (Stage T K 0) := by
  obtain ⟨P, hP, hPT, α, hα⟩ := exists_supported_perfect_approximatesFrom hT hTc hK hpc (-2)
  exact ⟨⟨P, hP, hPT, α, fun i hi => hα.1 i (by omega)⟩⟩

/-- The induction step of the tower: the map of a member to `K` factors through the next. -/
private theorem exists_stage_succ [CompactSpace X] [QuasiSeparatedSpace X]
    {T : Set X} (hT : IsClosed T) (hTc : IsCompact Tᶜ) {K : DerivedCategory X.Modules}
    (hK : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T K)
    (hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (n : ℕ) (s : Stage T K n) :
    ∃ s' : Stage T K (n + 1), ∃ g : s.obj ⟶ s'.obj, g ≫ s'.toTarget = s.toTarget := by
  obtain ⟨Q, g, β, hQ, hQT, hg, hβ⟩ :=
    exists_supported_perfect_factorization hT hTc hK hpc s.perfect s.toTarget (-((n : ℤ) + 2))
  exact ⟨⟨Q, hQ, hQT, β, fun i hi => hβ i (by push_cast at hi; omega)⟩, g, hg⟩

/-! ### [Stacks, Tag 0DKC] -/

/-- **[Stacks, Tag 0DKC].** Let `X` be a quasi-compact and quasi-separated scheme, let `T ⊆ X`
be a closed subset such that `X \ T` is quasi-compact, and let `K ∈ D(𝒪_X)` be supported on `T`.
The following are equivalent:
1. `K` is pseudo-coherent;
2. `K = hocolim Kₙ` where `Kₙ` is perfect, supported on `T`, and `τ_{≥-n}Kₙ ⟶ τ_{≥-n}K` is an
   isomorphism for all `n`.

The system is `F : ℕ ⥤ D(𝒪_X)`, indexed from `0`, its member `F.obj n` being the source's
`K_{n+1}`; so the truncation condition at index `n` is in degree `-(n + 1)`. The maps
`Kₙ ⟶ K` are the coprojections `c n` of the derived colimit
(`CategoryTheory.Pretriangulated.IsHomotopyColimitWith`). The same statement is
[Stacks, Tag 0DJP]. -/
@[stacks 0DKC]
theorem isPseudoCoherent_iff_exists_isHomotopyColimitWith [CompactSpace X]
    [QuasiSeparatedSpace X] (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (K : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T K) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K ↔
      ∃ (F : ℕ ⥤ DerivedCategory X.Modules) (c : ∀ n, F.obj n ⟶ K),
        (∀ n, IsPerfect (X := X.toRingedSpace) (F.obj n)) ∧
          (∀ n, Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T
            (F.obj n)) ∧
            (∀ n : ℕ,
              IsIso ((DerivedCategory.TStructure.t.truncGE (-((n : ℤ) + 1))).map (c n))) ∧
              IsHomotopyColimitWith F K c := by
  constructor
  · intro hpc
    obtain ⟨s₀⟩ := exists_stage_zero hT hTc hK hpc
    let step := exists_stage_succ hT hTc hK hpc
    let tower : ∀ n, Stage T K n := fun n => Nat.rec s₀ (fun n s => (step n s).choose) n
    let map : ∀ n, (tower n).obj ⟶ (tower (n + 1)).obj := fun n =>
      (step n (tower n)).choose_spec.choose
    let F : ℕ ⥤ DerivedCategory X.Modules := Functor.ofSequence map
    let c : ∀ n, F.obj n ⟶ K := fun n => (tower n).toTarget
    have hc : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ c (n + 1) = c n := fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ]
      exact (step n (tower n)).choose_spec.choose_spec
    exact ⟨F, c, fun n => (tower n).perfect, fun n => (tower n).supported,
      fun n => (Stacks.DerivedTruncation.isIso_truncGE_map_iff_forall_isIso_homologyMap (c n)
        _).2 (tower n).isIso,
      Stacks.DerivedColimit.isHomotopyColimitWith_of_eventually_isIso_homology F c hc
        fun i => ⟨i.natAbs, fun n hn => (tower n).isIso i (by omega)⟩⟩
  · rintro ⟨F, c, hperf, -, htrunc, -⟩
    refine (RingedSpace.isPseudoCoherent_iff_forall K).2 fun m => ?_
    have hiso : ∀ j : ℤ, -((m.natAbs : ℤ) + 1) ≤ j →
        IsIso ((DerivedCategory.homologyFunctor X.Modules j).map (c m.natAbs)) :=
      (Stacks.DerivedTruncation.isIso_truncGE_map_iff_forall_isIso_homologyMap (c m.natAbs)
        _).1 (htrunc m.natAbs)
    exact RingedSpace.isPseudoCoherentFrom_of_approximation m
      ((RingedSpace.isPseudoCoherent_iff_forall _).1
        (RingedSpace.IsPerfect.isPseudoCoherent (hperf m.natAbs)) m)
      (c m.natAbs) (fun j hj => hiso j (by omega))
      (@IsIso.epi_of_iso _ _ _ _ _ (hiso m (by omega)))

end AlgebraicGeometry.PerfectApproximation

end
