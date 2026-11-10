module

public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoStandardClasses
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedImmersionAtUnramifiedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank
public import StacksFrontier.AlgebraicGeometry.Variety.MiracleFlatEtale
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.ConormalUnramified
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.FiniteProjection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.SecantCone
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RegularPointCotangent
public import StacksFrontier.RingTheory.RegularLocalRing.KrullDimSurjection
public import StacksFrontier.Topology.Dimension.NowhereDense
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic projections of a subvariety near a nonsingular point

Let `V` be a vector space of dimension `n + 1` over an algebraically closed field, let
`X ⊆ 𝐏(V)` be a closed subvariety and let `x` be a nonsingular point of `X`. For a
sufficiently general centre `p`, the projection `r_p` away from `p` is well behaved at `x`: if
`dim X < n - 1` it identifies `X` with its image near `r_p(x)`, and if `dim X = n - 1` it is
étale at `x`.

In both cases the centres to avoid are those lying on the linear subspace cut out by the conormal
space of `X` at `x`, which is the locus of centres whose projection is tangent to `X` at `x`; for
the first assertion one must also avoid the secant cone, so that `x` is the only point of `X` in
its fibre.

The first assertion is stated as the restriction of `r_p|_X` over an open neighbourhood `R` of
`r_p(x)` being a closed immersion, which is exactly the source's "isomorphism over an open
neighbourhood of `r_p(x)`": a closed immersion over `R` is precisely an isomorphism of
`(r_p|_X)^{-1}(R)` onto its scheme-theoretic image, and that image is `r_p(X) ∩ R`.

## Main results

* `ProjectiveSpaceOfModule.conormal_ne_bot`: the conormal space at a nonsingular closed point of a
  subvariety of dimension less than `n` is nonzero.
* `IsClosedImmersion.topologicalKrullDim_lt`: a closed immersion into an irreducible reduced
  Noetherian scheme of finite dimension which is not an isomorphism lowers the dimension.
* `ProjectiveSpaceOfModule.exists_isOpen_isFinite_unramifiedAt_projection_restrict`: for a general
  centre the projection is defined on a closed subvariety other than `𝐏(V)`, finite there and
  unramified at a given nonsingular closed point, in every codimension.
* `ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_isClosedImmersion_projection_restrict`:
  part (1) of Tag 0B1Q.
* `ProjectiveSpaceOfModule.exists_isOpen_etaleAt_projection_restrict`: part (2) of Tag 0B1Q.
* `ProjectiveSpaceOfModule.exists_isOpen_projection_isClosedImmersion_and_etaleAt`: the whole of
  Tag 0B1Q, both parts, each under its own dimension condition.

## Implementation notes

Both assertions are proved first at a *closed* nonsingular point, because the identification of
the cotangent space of `𝐏(V)` at a point with the hyperplane `W_x` of degree-one forms vanishing
there — on which the whole argument rests — holds only at a closed point: at the generic point of
a nondegenerate curve in `𝐏³` the cotangent space has dimension two while `W_x` is zero. The
general case follows because a nonsingular point specializes to a nonsingular closed point — the
regular locus is open, being that of a scheme of finite type over a field, and the closed points
of such a scheme are dense in every locally closed subset — and because both conclusions are
assertions about an open neighbourhood, hence pass from a specialization back to the point.

The dimension conditions are written `dim X + 1 < n` and `dim X + 1 = n` rather than with a
truncated subtraction `n - 1`.

That the conormal space is nonzero is the only place where the ambient dimension is used
negatively. If it vanished then, by surjectivity of the affine coordinates onto `𝔪_x / 𝔪_x²`, the
kernel of the comparison map to the stalk of `X` would lie in the square of the maximal ideal, and
then `𝐏(V)` could not have larger dimension at `x` than `X` does.

## References

* [Stacks Project, Tag 0B1Q](https://stacks.math.columbia.edu/tag/0B1Q)
* [Stacks Project, Tag 0B1P](https://stacks.math.columbia.edu/tag/0B1P)
* [Stacks Project, Tag 04DG](https://stacks.math.columbia.edu/tag/04DG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

/-! ### Irreducibility of the ambient projective space -/

/-- **The projective space of a nonzero finite-dimensional vector space is irreducible**, being
isomorphic to projective `n`-space over the ground field, whose underlying space is irreducible
because the polynomial ring is a domain. -/
public instance irreducibleSpace_projectiveSpaceOfModule [FiniteDimensional k V] [Nontrivial V] :
    IrreducibleSpace (projectiveSpaceOfModule k V) := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k V = n + 1 :=
    ⟨Module.finrank k V - 1, by have := Module.finrank_pos (R := k) (M := V); omega⟩
  exact ObjectProperty.prop_of_iso (P := fun X : Scheme.{u} => IrreducibleSpace ↥X)
    (projectiveSpaceOfModuleIsoProjMvPolynomial
      (Module.finBasisOfFinrankEq k V hn)).symm inferInstance

attribute [local instance] AlgebraicGeometry.stalkResidueAlgebra
  AlgebraicGeometry.stalkMapAlgebra AlgebraicGeometry.stalkMapIsLocalHom
  AlgebraicGeometry.residueFieldMapAlgebra
  AlgebraicGeometry.relativeCotangentSpaceResidueModule

/-- The image of a closed point under a closed immersion is closed. -/
public theorem isClosed_singleton_base {X : Scheme.{u}}
    (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i] (x : X)
    (hxc : IsClosed ({x} : Set X)) :
    IsClosed ({i.base x} : Set (projectiveSpaceOfModule k V)) := by
  have he : ({i.base x} : Set (projectiveSpaceOfModule k V)) = i.base '' {x} := by simp
  rw [he]
  exact i.isClosedEmbedding.isClosedMap _ hxc

/-! ### Passing from a closed point to an arbitrary one -/

/-- **A nonsingular point of a scheme of finite type over a field specializes to a nonsingular
closed point.** The regular locus is open because such a scheme is J-2, its intersection with
the closure of the point is a nonempty locally closed set, and the closed points of a Jacobson
space are dense in such a set. -/
private theorem exists_isClosed_specializes_mem_regularLocus {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {x : X} (hx : x ∈ regularLocus X) :
    ∃ y : X, x ⤳ y ∧ IsClosed ({y} : Set X) ∧ y ∈ regularLocus X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hopen : IsOpen (regularLocus X) :=
    (Scheme.isJ2_of_locallyOfFiniteType_over_field k f).isOpen_regularLocus (𝟙 X)
  obtain ⟨y, ⟨hycl, hyreg⟩, hyc⟩ := nonempty_inter_closedPoints
    (Z := closure ({x} : Set X) ∩ regularLocus X) ⟨x, subset_closure rfl, hx⟩
    (isClosed_closure.isLocallyClosed.inter hopen.isLocallyClosed)
  exact ⟨y, specializes_iff_mem_closure.mpr hycl, hyc, hyreg⟩

/-- An open set containing the image of a specialization of `x` contains the image of `x`. -/
private theorem mem_of_specializes {Y Z : Scheme.{u}} (f : Y ⟶ Z) {y y₀ : Y} (h : y ⤳ y₀)
    (R : Z.Opens) (hR : f.base y₀ ∈ R) : f.base y ∈ R :=
  (h.map f.continuous).mem_open R.isOpen hR

/-- Étaleness at a point is inherited by its generizations, being a condition on an open
neighbourhood. -/
private theorem etaleAt_of_specializes {Y Z : Scheme.{u}} {f : Y ⟶ Z} {y y₀ : Y} (h : y ⤳ y₀)
    (hf : EtaleAt f y₀) : EtaleAt f y := by
  obtain ⟨U, hU, hy₀U, W, hW, hUW, het⟩ := hf
  exact ⟨U, hU, h.mem_open U.isOpen hy₀U, W, hW, hUW, het⟩

/-- **The conormal space at a nonsingular closed point of a proper closed subvariety is
nonzero.** If it vanished, the kernel of the comparison map to the stalk of `X` would lie in the
square of the maximal ideal, forcing `𝐏(V)` to have dimension at most that of `X`. -/
public theorem conormal_ne_bot [FiniteDimensional k V] [Nontrivial V] (n : ℕ)
    (hV : Module.finrank k V = n + 1)
    {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i]
    [IsVariety k (i ≫ projectiveSpaceOfModuleToSpec k V)] (x : X)
    (hxc : IsClosed ({x} : Set X)) (hxreg : x ∈ regularLocus X)
    (hdim : topologicalKrullDim X < (n : WithBot ℕ∞))
    {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V (i.base x))
    {g : Module.Dual k V} (hg : pointSubmodule k V (i.base x) = LinearMap.ker g)
    (hv₀g : g v₀ = 1) :
    conormal i x hv₀ ≠ ⊥ := by
  intro hN
  have hx'c := isClosed_singleton_base i x hxc
  -- the kernel of the comparison map lies in the square of the maximal ideal
  have hker : RingHom.ker (toStalk i x) ≤ maximalIdeal (localRing (i.base x)) ^ 2 := by
    intro xi hxi
    rw [RingHom.mem_ker] at hxi
    have hxim : xi ∈ maximalIdeal (localRing (i.base x)) := by
      rw [mem_maximalIdeal]
      intro hu
      exact not_isUnit_zero (hxi ▸ hu.map (toStalk i x))
    obtain ⟨w, hw, hdiff⟩ := exists_sub_chartGerm_mem_maximalIdeal_sq hg hv₀ hv₀g hxim
    have himg : toStalk i x (chartGerm (i.base x) hv₀ w) ∈
        maximalIdeal (X.presheaf.stalk x) ^ 2 := by
      have h1 : toStalk i x (xi - chartGerm (i.base x) hv₀ w) ∈
          maximalIdeal (X.presheaf.stalk x) ^ 2 := by
        rw [← map_maximalIdeal_toStalk i x, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hdiff
      rw [RingHom.map_sub, hxi, zero_sub] at h1
      simpa using Submodule.neg_mem _ h1
    have hwN : w ∈ conormal i x hv₀ := ⟨hw, himg⟩
    rw [hN, Submodule.mem_bot] at hwN
    rw [hwN, map_zero] at hdiff
    simpa using hdiff
  -- the two local rings and their dimensions
  have hLN : IsLocallyNoetherian (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOfModuleToSpec k V)
  have : IsNoetherianRing (localRing (i.base x)) :=
    isNoetherianRing_of_ringEquiv _ (stalkRingEquiv (i.base x))
  have : IsRegularLocalRing (X.presheaf.stalk x) := hxreg
  have hle := IsLocalRing.ringKrullDim_le_of_surjective_of_ker_le_maximalIdeal_sq
    (toStalk i x) (toStalk_surjective i x) hker
  have hA : ringKrullDim (localRing (i.base x)) = (n : WithBot ℕ∞) := by
    rw [← ringKrullDim_eq_of_ringEquiv (stalkRingEquiv (i.base x)),
      ← topologicalKrullDimAt_eq_krullDimOfRing_stalk k (projectiveSpaceOfModule k V)
        (projectiveSpaceOfModuleToSpec k V) (i.base x) hx'c,
      ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k
        (projectiveSpaceOfModule k V) (projectiveSpaceOfModuleToSpec k V) (i.base x)]
    exact topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV
  have hB : ringKrullDim (X.presheaf.stalk x) = topologicalKrullDim X := by
    rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X
      (i ≫ projectiveSpaceOfModuleToSpec k V) x hxc,
      ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X
        (i ≫ projectiveSpaceOfModuleToSpec k V) x]
  rw [hA, hB] at hle
  exact absurd hle (not_le.mpr hdim)

/-- A nonempty space whose dimension is less than a natural number `n` has as its dimension a
natural number less than `n`. -/
public theorem _root_.exists_nat_topologicalKrullDim_eq_of_lt {T : Type*} [TopologicalSpace T]
    [Nonempty T] {n : ℕ} (h : topologicalKrullDim T < (n : WithBot ℕ∞)) :
    ∃ d : ℕ, topologicalKrullDim T = (d : WithBot ℕ∞) ∧ d < n := by
  have hbot : topologicalKrullDim T ≠ ⊥ := fun hb =>
    ((topologicalKrullDim_eq_bot_iff_isEmpty T).mp hb).false (Classical.arbitrary T)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hbot
  rw [← ha] at h ⊢
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe d => exact ⟨d, rfl, by exact_mod_cast h⟩

/-- **A closed immersion into an irreducible reduced Noetherian scheme of finite dimension which
is not an isomorphism lowers the dimension.** Its image is a proper closed subset, since a
surjective closed immersion into a reduced scheme is an isomorphism; a proper closed subset of an
irreducible space is nowhere dense, and a nowhere dense closed subset of a finite-dimensional
Noetherian space has smaller dimension. -/
@[ega "IV 5.2.4" "special case"]
public theorem _root_.AlgebraicGeometry.IsClosedImmersion.topologicalKrullDim_lt
    {Y W : Scheme.{u}} (f : Y ⟶ W) [IsClosedImmersion f] [IsReduced W] [IrreducibleSpace W]
    [NoetherianSpace W] (hf : ¬ IsIso f) (hfin : topologicalKrullDim W ≠ ⊤) :
    topologicalKrullDim Y < topologicalKrullDim W := by
  have hclosed : IsClosed (Set.range f.base) := f.isClosedEmbedding.isClosed_range
  have hne : Set.range f.base ≠ Set.univ := fun h => by
    have : Surjective f := ⟨Set.range_eq_univ.mp h⟩
    exact hf (isIso_of_isClosedImmersion_of_surjective f)
  have hnd : IsNowhereDense (Set.range f.base) := by
    rw [IsNowhereDense, hclosed.closure_eq]
    by_contra hint
    refine hne (Set.eq_univ_of_univ_subset ?_)
    rw [← (isOpen_interior.dense (Set.nonempty_iff_ne_empty.mpr hint)).closure_eq]
    exact (closure_mono interior_subset).trans hclosed.closure_subset
  rw [IsHomeomorph.topologicalKrullDim_eq _
    f.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph]
  exact hnd.topologicalKrullDim_lt hclosed inferInstance hfin

/-- The hyperplane of degree-one forms vanishing at a closed point of `𝐏(V)` is nonzero as soon
as `V` has dimension at least two. -/
public theorem nontrivial_pointSubmodule [IsAlgClosed k] [FiniteDimensional k V]
    (p : projectiveSpaceOfModule k V)
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hV2 : 2 ≤ Module.finrank k V) : Nontrivial ↥(pointSubmodule k V p) := by
  refine Module.nontrivial_of_finrank_pos (R := k) ?_
  have h1 := Submodule.finrank_quotient_add_finrank (pointSubmodule k V p)
  rw [finrank_quotient_pointSubmodule k V p hpc] at h1
  omega

/-- A closed point of `𝐏(V)` has a hyperplane `ker g` of forms vanishing at it, and a vector
`v₀` outside it with `g v₀ = 1`. -/
private theorem exists_dual_ker_pointSubmodule [IsAlgClosed k] [FiniteDimensional k V]
    {p : projectiveSpaceOfModule k V}
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V))) :
    ∃ (g : Module.Dual k V) (v₀ : V),
      pointSubmodule k V p = LinearMap.ker g ∧ v₀ ∉ pointSubmodule k V p ∧ g v₀ = 1 := by
  obtain ⟨g, hg⟩ := exists_pointSubmodule_eq_ker_of_isClosed hpc
  have hgne : pointSubmodule k V p ≠ ⊤ := by
    intro h
    have hm : p ∈ linearSubspace k V ⊤ :=
      (mem_linearSubspace_iff k V ⊤ _).mpr (le_of_eq h.symm)
    rwa [linearSubspace_top] at hm
  obtain ⟨v, hvne⟩ : ∃ v, g v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hgne (by rw [hg, LinearMap.ker_eq_top.mpr (LinearMap.ext hc)])
  have hv₀g : g ((g v)⁻¹ • v) = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hvne]
  exact ⟨g, _, hg, by rw [hg, LinearMap.mem_ker, hv₀g]; exact one_ne_zero, hv₀g⟩

/-- Inside a nonempty open set, the complement of the linear subspace cut out by a nonzero
submodule is nonempty, as `𝐏(V)` is irreducible. -/
private theorem nonempty_inter_compl_linearSubspace [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V]
    {O : Set (projectiveSpaceOfModule k V)}
    (hO : IsOpen O) (hne : O.Nonempty) {N : Submodule k V} (hN : N ≠ ⊥) :
    (O ∩ (linearSubspace k V N)ᶜ).Nonempty := by
  obtain ⟨q, -, hq⟩ := exists_closedPoint_notMem_linearSubspace k V hN
  exact nonempty_preirreducible_inter hO (isClosed_linearSubspace k V _).isOpen_compl hne ⟨q, hq⟩

section Core

variable [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]

/-- **The projection away from a centre off the conormal linear subspace is finite and unramified
at `x`.** The common core of the two parts of Tag 0B1Q. -/
private theorem exists_fac_unramifiedAt {X : Scheme.{u}}
    (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i] (x : X)
    (hxc : IsClosed ({x} : Set X))
    {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V (i.base x))
    {g : Module.Dual k V} (hg : pointSubmodule k V (i.base x) = LinearMap.ker g)
    (hv₀g : g v₀ = 1) (hV2 : 2 ≤ Module.finrank k V)
    (p : projectiveSpaceOfModule k V)
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpX : p ∉ Set.range i.base)
    (hpN : p ∉ linearSubspace k V (conormal i x hv₀)) :
    ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
      j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = i ∧
        IsFinite (j ≫ projection k V (pointSubmodule k V p)) ∧
          UnramifiedAt (j ≫ projection k V (pointSubmodule k V p)) x := by
  have hx'c := isClosed_singleton_base i x hxc
  have hpne : i.base x ≠ p := fun h => hpX (h ▸ Set.mem_range_self x)
  have hWp : ¬ (pointSubmodule k V p ≤ pointSubmodule k V (i.base x)) := fun hle =>
    hpne (pointSubmodule_le_of_le_of_isClosed k V hpc hx'c hle).symm
  obtain ⟨w, hwW, hwg⟩ : ∃ w ∈ pointSubmodule k V p, g w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hWp fun w hw => by rw [hg, LinearMap.mem_ker]; exact hc w hw
  have hw₀mem : (g w)⁻¹ • w ∈ pointSubmodule k V p := Submodule.smul_mem _ _ hwW
  have hw₀g : g (((⟨(g w)⁻¹ • w, hw₀mem⟩ : ↥(pointSubmodule k V p)) : V)) = 1 := by
    change g ((g w)⁻¹ • w) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hwg]
  have hw₀V : (((⟨(g w)⁻¹ • w, hw₀mem⟩ : ↥(pointSubmodule k V p)) : V))
      ∉ pointSubmodule k V (i.base x) := by
    rw [hg, LinearMap.mem_ker, hw₀g]; exact one_ne_zero
  have hsub : Set.range i.base ⊆
      Set.range (projectionDomain k V (pointSubmodule k V p)).ι.base := by
    rw [Scheme.Opens.range_ι, coe_mapDomain_pointSubmodule k V p hpc]
    exact Set.subset_compl_singleton_iff.mpr hpX
  refine ⟨IsOpenImmersion.lift _ i hsub, IsOpenImmersion.lift_fac _ _ _, ?_, ?_⟩
  · exact isFinite_projection_of_isClosedImmersion i _ _ (IsOpenImmersion.lift_fac _ _ _)
  set j := IsOpenImmersion.lift (projectionDomain k V (pointSubmodule k V p)).ι i hsub with hjdef
  have hj : j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = i :=
    IsOpenImmersion.lift_fac _ _ _
  have hfin : IsFinite (j ≫ projection k V (pointSubmodule k V p)) :=
    isFinite_projection_of_isClosedImmersion i _ j hj
  have hbase : ∀ y : X, (j.base y).1 = i.base y := by intro y; rw [← hj]; rfl
  have hNtW : Nontrivial ↥(pointSubmodule k V p) := nontrivial_pointSubmodule p hpc hV2
  have hlft : LocallyOfFiniteType ((j ≫ projection k V (pointSubmodule k V p)) ≫
      projectiveSpaceOfModuleToSpec k ↥(pointSubmodule k V p)) := by
    have : LocallyOfFiniteType (j ≫ projection k V (pointSubmodule k V p)) := inferInstance
    infer_instance
  refine unramifiedAt_projection_of_sup_eq_of_fac x _ j i hj hg ?_ hw₀V hw₀g ?_ ?_
  · intro h
    have h2 := (mem_pointSubmodule_projection_iff (j.base x) _).mp h
    rw [hbase x] at h2
    exact hw₀V h2
  · rw [conormal_indep i x hw₀V hv₀
      (by rw [hg, LinearMap.mem_ker, map_sub, hw₀g, hv₀g, sub_self])]
    exact (sup_inf_pointSubmodule_eq_iff_notMem_linearSubspace k V hx'c hpc hpne
      (conormal_le i x hv₀)).mpr hpN
  · exact isSeparable_residueField_of_isClosed _
      (projectiveSpaceOfModuleToSpec k ↥(pointSubmodule k V p)) x hxc

/-- **For a general centre the projection is defined on a closed subvariety other than `𝐏(V)`,
finite there and unramified at a given nonsingular closed point.** The centres to avoid are the
points of `X` and those of the linear subspace cut out by the conormal space of `X` at `x`. That
subspace is proper because `X`, being a proper closed subvariety of the irreducible `𝐏(V)`, has
smaller dimension, and its complement meets that of `X` because `𝐏(V)` is irreducible. This is
the common input of both parts of Tag 0B1Q, and it holds in every codimension. -/
public theorem exists_isOpen_isFinite_unramifiedAt_projection_restrict
    {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i]
    [IsVariety k (i ≫ projectiveSpaceOfModuleToSpec k V)] (hX : ¬ IsIso i)
    (x : X) (hxc : IsClosed ({x} : Set X)) (hxreg : x ∈ regularLocus X) :
    ∃ U : (projectiveSpaceOfModule k V).Opens,
      (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
          j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = i ∧
          IsFinite (j ≫ projection k V (pointSubmodule k V p)) ∧
          UnramifiedAt (j ≫ projection k V (pointSubmodule k V p)) x := by
  obtain ⟨n, hV⟩ : ∃ n, Module.finrank k V = n + 1 :=
    ⟨Module.finrank k V - 1, by have := Module.finrank_pos (R := k) (M := V); omega⟩
  have hx'c := isClosed_singleton_base i x hxc
  have : IsReduced (projectiveSpaceOfModule k V) := isReduced_projectiveSpaceOfModule k V
  have : IsLocallyNoetherian (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOfModuleToSpec k V)
  have : CompactSpace (projectiveSpaceOfModule k V) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOfModuleToSpec k V)
  have : IsNoetherian (projectiveSpaceOfModule k V) := {}
  have hPdim := topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV
  have hdim : topologicalKrullDim X < (n : WithBot ℕ∞) := by
    rw [← hPdim]
    refine IsClosedImmersion.topologicalKrullDim_lt i hX ?_
    rw [hPdim]
    change ((n : ℕ∞) : WithBot ℕ∞) ≠ ((⊤ : ℕ∞) : WithBot ℕ∞)
    exact fun h => ENat.natCast_ne_top n (WithBot.coe_inj.mp h)
  obtain ⟨g, v₀, hg, hv₀, hv₀g⟩ := exists_dual_ker_pointSubmodule hx'c
  have hNbot := conormal_ne_bot n hV i x hxc hxreg hdim hv₀ hg hv₀g
  have : Nonempty X := ⟨x⟩
  obtain ⟨dX, -, hdXn⟩ := exists_nat_topologicalKrullDim_eq_of_lt hdim
  have hV2 : 2 ≤ Module.finrank k V := by omega
  have hXc : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  have hXne : (Set.range i.base)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro hsurj
    have : Surjective i := ⟨Set.range_eq_univ.mp hsurj⟩
    exact hX (isIso_of_isClosedImmersion_of_surjective i)
  refine ⟨⟨(Set.range i.base)ᶜ ∩ (linearSubspace k V (conormal i x hv₀))ᶜ,
    hXc.isOpen_compl.inter (isClosed_linearSubspace k V _).isOpen_compl⟩, ?_, ?_⟩
  · exact nonempty_inter_compl_linearSubspace hXc.isOpen_compl hXne hNbot
  · rintro p ⟨hpX, hpN⟩ hpc
    exact exists_fac_unramifiedAt i x hxc hv₀ hg hv₀g hV2 p hpc hpX hpN

/-- **Part (1) of Tag 0B1Q at a closed point.** The case of the following theorem in which the
nonsingular point `x` is closed, where the cotangent space of `𝐏(V)` at `i x` is the hyperplane
of degree-one forms vanishing there. -/
private theorem exists_isOpen_isClosedImmersion_projection_restrict_of_isClosed (n : ℕ)
    (hV : Module.finrank k V = n + 1)
    {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i]
    [IsVariety k (i ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X + 1 < (n : WithBot ℕ∞))
    (x : X) (hxc : IsClosed ({x} : Set X)) (hxreg : x ∈ regularLocus X) :
    ∃ U : (projectiveSpaceOfModule k V).Opens,
      (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
          j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = i ∧
            ∃ R : (projectiveSpaceOfModule k ↥(pointSubmodule k V p)).Opens,
              (j ≫ projection k V (pointSubmodule k V p)).base x ∈ R ∧
              IsClosedImmersion ((j ≫ projection k V (pointSubmodule k V p)) ∣_ R) := by
  have hx'c := isClosed_singleton_base i x hxc
  have hdimeq := finrank_cotangentSpace_eq_topologicalKrullDim k
    (i ≫ projectiveSpaceOfModuleToSpec k V) x hxc hxreg
  set dX := Module.finrank (ResidueField (X.presheaf.stalk x))
    (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) with hdXdef
  rw [← hdimeq] at hdim
  have hnat : dX + 1 < n := by exact_mod_cast hdim
  obtain ⟨g, v₀, hg, hv₀, hv₀g⟩ := exists_dual_ker_pointSubmodule hx'c
  have hdim2 : topologicalKrullDim X < (n : WithBot ℕ∞) := by
    rw [← hdimeq]
    exact_mod_cast (show dX < n by omega)
  have hNbot := conormal_ne_bot n hV i x hxc hxreg hdim2 hv₀ hg hv₀g
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hVm : Module.finrank k V = m + 2 := by omega
  have hV2 : 2 ≤ Module.finrank k V := by omega
  have hXc : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  have hXdim : topologicalKrullDim (Set.range i.base) = topologicalKrullDim X :=
    (IsHomeomorph.topologicalKrullDim_eq _
      i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm
  have hXdim2 : topologicalKrullDim (Set.range i.base) < (m : WithBot ℕ∞) := by
    rw [hXdim, ← hdimeq]
    exact_mod_cast (show dX < m by omega)
  obtain ⟨U₀, hU₀open, hU₀ne, hU₀⟩ := exists_isOpen_nonempty_forall_eq_of_isIrreducible k V
    (i.base x) hx'c hVm hXc hXdim2
  refine ⟨⟨U₀ ∩ (linearSubspace k V (conormal i x hv₀))ᶜ,
    hU₀open.inter (isClosed_linearSubspace k V _).isOpen_compl⟩, ?_, ?_⟩
  · exact nonempty_inter_compl_linearSubspace hU₀open hU₀ne hNbot
  · rintro p ⟨hpU₀, hpN⟩ hpc
    obtain ⟨hpX, hfibcond⟩ := hU₀ p hpU₀ hpc
    obtain ⟨j, hj, hfin, hun⟩ :=
      exists_fac_unramifiedAt i x hxc hv₀ hg hv₀g hV2 p hpc hpX hpN
    refine ⟨j, hj, ?_⟩
    have hbase : ∀ y : X, (j.base y).1 = i.base y := by intro y; rw [← hj]; rfl
    have hfibeq : (j ≫ projection k V (pointSubmodule k V p)).base ⁻¹'
        {(j ≫ projection k V (pointSubmodule k V p)).base x} = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      refine ⟨fun hy => ?_, fun hy => by rw [hy]⟩
      have h3 := hfibcond (j.base y) (j.base x)
        (by rw [hbase y]; exact Set.mem_range_self y) (hbase x) hy
      rw [hbase y] at h3
      exact i.isClosedEmbedding.injective h3
    have hNtW : Nontrivial ↥(pointSubmodule k V p) := nontrivial_pointSubmodule p hpc hV2
    have hlft : LocallyOfFiniteType ((j ≫ projection k V (pointSubmodule k V p)) ≫
        projectiveSpaceOfModuleToSpec k ↥(pointSubmodule k V p)) := by
      have : LocallyOfFiniteType (j ≫ projection k V (pointSubmodule k V p)) := inferInstance
      infer_instance
    exact exists_isOpen_restrict_isClosedImmersion_of_unramifiedAt
      (j ≫ projection k V (pointSubmodule k V p))
      (projectiveSpaceOfModuleToSpec k ↥(pointSubmodule k V p)) x hxc hun hfibeq

/-- **Stacks Project, Tag 0B1Q, part (1).** Let `V` have dimension `n + 1`, let `X ⊆ 𝐏(V)` be a
closed subvariety of dimension less than `n - 1` and let `x` be a nonsingular point of `X`. Then
there is a nonempty Zariski open `U ⊆ 𝐏(V)` such that for every closed point `p ∈ U` the
projection `r_p` is defined on `X` and `r_p|_X` is a closed immersion over an open neighbourhood
of `r_p(x)`, that is, an isomorphism of `X` onto `r_p(X)` there.

This is part (1) alone. Both parts together, which is where Tag 0B1Q is registered, are
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_projection_isClosedImmersion_and_etaleAt`.
-/
public theorem exists_isOpen_forall_closedPoint_isClosedImmersion_projection_restrict (n : ℕ)
    (hV : Module.finrank k V = n + 1)
    {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i]
    [IsVariety k (i ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X + 1 < (n : WithBot ℕ∞))
    (x : X) (hxreg : x ∈ regularLocus X) :
    ∃ U : (projectiveSpaceOfModule k V).Opens,
      (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
          j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = i ∧
            ∃ R : (projectiveSpaceOfModule k ↥(pointSubmodule k V p)).Opens,
              (j ≫ projection k V (pointSubmodule k V p)).base x ∈ R ∧
              IsClosedImmersion ((j ≫ projection k V (pointSubmodule k V p)) ∣_ R) := by
  obtain ⟨y, hxy, hyc, hyreg⟩ := exists_isClosed_specializes_mem_regularLocus
    (i ≫ projectiveSpaceOfModuleToSpec k V) hxreg
  obtain ⟨U, hUne, hU⟩ := exists_isOpen_isClosedImmersion_projection_restrict_of_isClosed
    n hV i hdim y hyc hyreg
  refine ⟨U, hUne, fun p hp hpc => ?_⟩
  obtain ⟨j, hj, R, hR, hci⟩ := hU p hp hpc
  exact ⟨j, hj, R, mem_of_specializes _ hxy R hR, hci⟩

/-- **Part (2) of Tag 0B1Q at a closed point.** The case of the following theorem in which the
nonsingular point `x` is closed, where the cotangent space of `𝐏(V)` at `i x` is the hyperplane
of degree-one forms vanishing there. -/
private theorem exists_isOpen_etaleAt_projection_restrict_of_isClosed (n : ℕ)
    (hV : Module.finrank k V = n + 1)
    {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i]
    [IsVariety k (i ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X + 1 = (n : WithBot ℕ∞))
    (x : X) (hxc : IsClosed ({x} : Set X)) (hxreg : x ∈ regularLocus X) :
    ∃ U : (projectiveSpaceOfModule k V).Opens,
      (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
          j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = i ∧
            EtaleAt (j ≫ projection k V (pointSubmodule k V p)) x := by
  have hx'c := isClosed_singleton_base i x hxc
  have hdimeq := finrank_cotangentSpace_eq_topologicalKrullDim k
    (i ≫ projectiveSpaceOfModuleToSpec k V) x hxc hxreg
  set dX := Module.finrank (ResidueField (X.presheaf.stalk x))
    (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) with hdXdef
  rw [← hdimeq] at hdim
  have hnat : dX + 1 = n := by exact_mod_cast hdim
  obtain ⟨g, v₀, hg, hv₀, hv₀g⟩ := exists_dual_ker_pointSubmodule hx'c
  have hdim2 : topologicalKrullDim X < (n : WithBot ℕ∞) := by
    rw [← hdimeq]
    exact_mod_cast (show dX < n by omega)
  have hNbot := conormal_ne_bot n hV i x hxc hxreg hdim2 hv₀ hg hv₀g
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hV2 : 2 ≤ Module.finrank k V := by omega
  have hXc : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  have hXdim : topologicalKrullDim (Set.range i.base) = topologicalKrullDim X := by
    refine (IsHomeomorph.topologicalKrullDim_eq (Set.rangeFactorization i.base) ?_).symm
    rw [isHomeomorph_iff_isEmbedding_surjective]
    exact ⟨Topology.IsEmbedding.of_comp (Continuous.subtype_mk i.base.hom.continuous _)
      continuous_subtype_val i.isClosedEmbedding.isEmbedding,
      fun y => by obtain ⟨a, ha⟩ := y.2; exact ⟨a, Subtype.ext ha⟩⟩
  have hXne : (Set.range i.base)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    have h1 : topologicalKrullDim (Set.range i.base)
        = topologicalKrullDim (projectiveSpaceOfModule k V) := by
      rw [h]
      exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph
    rw [hXdim, topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV, ← hdimeq] at h1
    have h2 : dX = m + 1 := by exact_mod_cast h1
    omega
  refine ⟨⟨(Set.range i.base)ᶜ ∩ (linearSubspace k V (conormal i x hv₀))ᶜ,
    hXc.isOpen_compl.inter (isClosed_linearSubspace k V _).isOpen_compl⟩, ?_, ?_⟩
  · exact nonempty_inter_compl_linearSubspace hXc.isOpen_compl hXne hNbot
  · rintro p ⟨hpX, hpN⟩ hpc
    obtain ⟨j, hj, hfin, hun⟩ :=
      exists_fac_unramifiedAt i x hxc hv₀ hg hv₀g hV2 p hpc hpX hpN
    refine ⟨j, hj, ?_⟩
    have hNtW : Nontrivial ↥(pointSubmodule k V p) := nontrivial_pointSubmodule p hpc hV2
    have hWfr : Module.finrank k ↥(pointSubmodule k V p) = m + 1 := by
      have h1 := Submodule.finrank_quotient_add_finrank (pointSubmodule k V p)
      rw [finrank_quotient_pointSubmodule k V p hpc] at h1
      omega
    have hyc : IsClosed ({(j ≫ projection k V (pointSubmodule k V p)).base x} :
        Set (projectiveSpaceOfModule k ↥(pointSubmodule k V p))) := by
      have he : ({(j ≫ projection k V (pointSubmodule k V p)).base x} :
          Set (projectiveSpaceOfModule k ↥(pointSubmodule k V p)))
          = (j ≫ projection k V (pointSubmodule k V p)).base '' {x} := by simp
      rw [he]
      exact (j ≫ projection k V (pointSubmodule k V p)).isClosedMap _ hxc
    have hregY : IsRegularLocalRing
        ((projectiveSpaceOfModule k ↥(pointSubmodule k V p)).presheaf.stalk
          ((j ≫ projection k V (pointSubmodule k V p)).base x)) :=
      isRegularLocalRing_stalk_projectiveSpaceOfModule k ↥(pointSubmodule k V p) _
    have hregX : IsRegularLocalRing (X.presheaf.stalk x) := hxreg
    have hdimW : topologicalKrullDim X
        = topologicalKrullDim (projectiveSpaceOfModule k ↥(pointSubmodule k V p)) := by
      rw [topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hWfr, ← hdimeq]
      exact_mod_cast (show dX = m by omega)
    have hdim' : ringKrullDim (X.presheaf.stalk x) =
        ringKrullDim ((projectiveSpaceOfModule k ↥(pointSubmodule k V p)).presheaf.stalk
          ((j ≫ projection k V (pointSubmodule k V p)).base x)) :=
      ringKrullDim_stalk_eq_of_topologicalKrullDim_eq k
        (i ≫ projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k ↥(pointSubmodule k V p)) x _ hxc hyc hdimW
    have hLNW : IsLocallyNoetherian (projectiveSpaceOfModule k ↥(pointSubmodule k V p)) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (projectiveSpaceOfModuleToSpec k ↥(pointSubmodule k V p))
    exact etaleAt_of_unramifiedAt_of_ringKrullDim_eq _ x hun hdim'

/-- **Stacks Project, Tag 0B1Q, part (2).** Let `V` have dimension `n + 1`, let `X ⊆ 𝐏(V)` be a
closed subvariety of dimension `n - 1` and let `x` be a nonsingular point of `X`. Then there is
a nonempty Zariski open `U ⊆ 𝐏(V)` such that for every closed point `p ∈ U` the projection `r_p`
is defined on `X` and `r_p|_X : X ⟶ 𝐏(W_p)` is étale at `x`.

This is part (2) alone. Both parts together, which is where Tag 0B1Q is registered, are
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_projection_isClosedImmersion_and_etaleAt`.
-/
public theorem exists_isOpen_etaleAt_projection_restrict (n : ℕ)
    (hV : Module.finrank k V = n + 1)
    {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i]
    [IsVariety k (i ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdim : topologicalKrullDim X + 1 = (n : WithBot ℕ∞))
    (x : X) (hxreg : x ∈ regularLocus X) :
    ∃ U : (projectiveSpaceOfModule k V).Opens,
      (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
          j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = i ∧
            EtaleAt (j ≫ projection k V (pointSubmodule k V p)) x := by
  obtain ⟨y, hxy, hyc, hyreg⟩ := exists_isClosed_specializes_mem_regularLocus
    (i ≫ projectiveSpaceOfModuleToSpec k V) hxreg
  obtain ⟨U, hUne, hU⟩ := exists_isOpen_etaleAt_projection_restrict_of_isClosed
    n hV i hdim y hyc hyreg
  refine ⟨U, hUne, fun p hp hpc => ?_⟩
  obtain ⟨j, hj, het⟩ := hU p hp hpc
  exact ⟨j, hj, etaleAt_of_specializes hxy het⟩

/-! ### The whole of Stacks 0B1Q -/

/-- **Stacks Project, Tag 0B1Q.** Let `V` be a vector space of dimension `n + 1` over an
algebraically closed field, let `X ⊆ 𝐏(V)` be a closed subvariety and let `x` be a nonsingular
point of `X`. Then

1. if `dim X < n - 1`, there is a nonempty Zariski open `U ⊆ 𝐏(V)` such that for every closed
   point `p ∈ U` the projection `r_p` is defined on `X` and `r_p|_X : X → r_p(X)` is an
   isomorphism over an open neighbourhood of `r_p(x)`;
2. if `dim X = n - 1`, there is a nonempty Zariski open `U ⊆ 𝐏(V)` such that for every closed
   point `p ∈ U` the projection `r_p` is defined on `X` and `r_p|_X : X ⟶ 𝐏(W_p)` is étale
   at `x`.

Each part keeps its own dimension condition as the hypothesis of its clause, as the source
states them. That `r_p` is defined on `X` is the morphism `j` lifting the closed immersion `i`
through the domain of definition of the projection away from `p`. In part (1) the isomorphism
onto the image over a neighbourhood `R` of `r_p(x)` is spelled as `r_p|_X` restricted over `R`
being a closed immersion, which is the same thing: a closed immersion over `R` is an
isomorphism of its source onto its scheme-theoretic image, and that image is `r_p(X) ∩ R`.
`WithBot ℕ∞` has no subtraction, so `dim X < n - 1` and `dim X = n - 1` are written
`dim X + 1 < n` and `dim X + 1 = n`. -/
@[stacks 0B1Q "both parts, for a closed subvariety of the projective space of a vector space of \
dimension n + 1 over an algebraically closed field and a nonsingular point x of it, each part \
under its own dimension condition exactly as the source states it: (1) for dim X < n - 1 a \
nonempty Zariski open of centres p for which r_p|_X is an isomorphism over a neighbourhood of \
r_p(x), spelled as the restriction of r_p|_X over that neighbourhood being a closed immersion, \
which is the same thing since a closed immersion over an open R is an isomorphism onto its \
scheme-theoretic image r_p(X) ∩ R; (2) for dim X = n - 1 a nonempty Zariski open of centres p \
for which r_p|_X : X ⟶ 𝐏(W_p) is étale at x. Both parts also deliver the source's 'r_p is \
defined on X' as the lift j of the closed immersion i through the domain of definition of the \
projection away from p. WithBot ℕ∞ has no subtraction, so the two dimension conditions are \
written dim X + 1 < n and dim X + 1 = n."]
public theorem exists_isOpen_projection_isClosedImmersion_and_etaleAt (n : ℕ)
    (hV : Module.finrank k V = n + 1)
    {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i]
    [IsVariety k (i ≫ projectiveSpaceOfModuleToSpec k V)]
    (x : X) (hxreg : x ∈ regularLocus X) :
    (topologicalKrullDim X + 1 < (n : WithBot ℕ∞) →
        ∃ U : (projectiveSpaceOfModule k V).Opens,
          (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
          ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
            ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
              j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = i ∧
                ∃ R : (projectiveSpaceOfModule k ↥(pointSubmodule k V p)).Opens,
                  (j ≫ projection k V (pointSubmodule k V p)).base x ∈ R ∧
                  IsClosedImmersion ((j ≫ projection k V (pointSubmodule k V p)) ∣_ R)) ∧
      (topologicalKrullDim X + 1 = (n : WithBot ℕ∞) →
        ∃ U : (projectiveSpaceOfModule k V).Opens,
          (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
          ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
            ∃ j : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
              j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = i ∧
                EtaleAt (j ≫ projection k V (pointSubmodule k V p)) x) :=
  ⟨fun hdim => exists_isOpen_forall_closedPoint_isClosedImmersion_projection_restrict n hV i
      hdim x hxreg,
    fun hdim => exists_isOpen_etaleAt_projection_restrict n hV i hdim x hxreg⟩

end Core

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
