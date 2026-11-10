module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPointsAlgebra
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Two closed points of an irreducible closed subset lie on a curve

Let `Y` be a scheme of finite type over a field. This file proves that two distinct closed points
of an irreducible closed subset of `Y` lie on a common curve of `Y`, an irreducible closed subset
of dimension one. The source uses this, without stating it, in the closing sentence of
[Stacks, Example 0EJ1], where it is what makes a zigzag with `k` descending legs cost at least `k`
curves.

The irreducible closed subset is cut down step by step, keeping both points, until its dimension is
one. Each step is `Stacks.Algebraization.CurveThroughPoints.exists_specializes_specializes`: in
dimension at least two there is a point other than the generic point specializing to both points,
whose closure is the next, smaller subset. That step is commutative algebra in the function field,
carried out in `StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPointsAlgebra`, and it
does not need the two points to have a common affine neighbourhood.

## Main results

* `Stacks.Algebraization.CurveThroughPoints.exists_specializes_specializes`: the step.
* `Stacks.Algebraization.CurveThroughPoints.topologicalKrullDim_eq_height`: the dimension of an
  irreducible closed subset is its height among irreducible closed subsets.
* `Stacks.Algebraization.CurveThroughPoints.exists_dim_one_of_mem`: the curve.

## Implementation notes

The `k`-algebra structures on rings of sections, stalks and residue fields are the canonical ones
through the structure morphism, as `sectionsAlgebra`, `stalkAlgebra` and `residueAlgebra`; the
last is the one of `AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_trdeg`.

## References

* [Stacks Project, Tag 0EJ1](https://stacks.math.columbia.edu/tag/0EJ1)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace IsLocalRing
open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

namespace Stacks.Algebraization.CurveThroughPoints

variable {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))

/-- The `k`-algebra structure of a ring of sections, through the structure morphism. -/
@[instance_reducible]
def sectionsAlgebra (V : Y.Opens) : Algebra k Γ(Y, V) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.presheaf.map (homOfLE le_top).op).hom.toAlgebra

/-- The `k`-algebra structure of a stalk, through the structure morphism. -/
@[instance_reducible]
def stalkAlgebra (x : Y) : Algebra k (Y.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
    Y.presheaf.germ ⊤ x (show x ∈ (⊤ : Y.Opens) from trivial)).hom.toAlgebra

/-- The `k`-algebra structure of a residue field, through the structure morphism; it is the
one of `AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_trdeg`. -/
@[instance_reducible]
def residueAlgebra (x : Y) : Algebra k (Y.residueField x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation x).hom.toAlgebra

/-- The germ map at a point of an open, as a `k`-algebra map. -/
def germAlgHom (V : Y.Opens) (x : Y) (hx : x ∈ V) :
    letI := sectionsAlgebra f V
    letI := stalkAlgebra f x
    Γ(Y, V) →ₐ[k] Y.presheaf.stalk x :=
  letI := sectionsAlgebra f V
  letI := stalkAlgebra f x
  { (Y.presheaf.germ V x hx).hom with
    commutes' := fun c => by
      change Y.presheaf.germ V x hx (Y.presheaf.map (homOfLE le_top).op _) =
        Y.presheaf.germ ⊤ x (show x ∈ (⊤ : Y.Opens) from trivial) _
      exact Y.presheaf.germ_res_apply (homOfLE le_top) x hx _ }

/-- The map from the stalk at a specialization of `η` to the residue field at `η`, as a
`k`-algebra map. -/
def toResidueAlgHom {η x : Y} (h : η ⤳ x) :
    letI := stalkAlgebra f x
    letI := residueAlgebra f η
    Y.presheaf.stalk x →ₐ[k] Y.residueField η :=
  letI := stalkAlgebra f x
  letI := residueAlgebra f η
  { (Y.presheaf.stalkSpecializes h ≫ Y.residue η).hom with
    commutes' := fun c => by
      change (Y.presheaf.stalkSpecializes h ≫ Y.residue η).hom
          ((Y.presheaf.germ ⊤ x (show x ∈ (⊤ : Y.Opens) from trivial)).hom _) =
            (Y.Γevaluation η).hom _
      rw [← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
      rfl }

/-- The germ at `x` of a section over `V`, mapped to the residue field at a generization `η` of
`x`, is the evaluation of the section at `η`. -/
theorem toResidueAlgHom_germAlgHom {η x : Y} (h : η ⤳ x) (V : Y.Opens) (hx : x ∈ V)
    (a : Γ(Y, V)) :
    letI := sectionsAlgebra f V
    letI := stalkAlgebra f x
    letI := residueAlgebra f η
    toResidueAlgHom f h (germAlgHom f V x hx a) = Y.evaluation V η (h.mem_open V.isOpen hx) a := by
  change (Y.presheaf.stalkSpecializes h ≫ Y.residue η).hom ((Y.presheaf.germ V x hx).hom a) = _
  rw [← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  rfl

/-- If `Y` is locally of finite type over `k`, the ring of sections over an affine open is a
finitely generated `k`-algebra. -/
theorem finiteType_sections [LocallyOfFiniteType f] {V : Y.Opens} (hV : IsAffineOpen V) :
    letI := sectionsAlgebra f V
    Algebra.FiniteType k Γ(Y, V) := by
  change RingHom.FiniteType _
  have hcomp : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      Y.presheaf.map (homOfLE le_top).op).hom =
      (f.appLE ⊤ V (by simp)).hom.comp ((Scheme.ΓSpecIso (.of k)).inv).hom := rfl
  rw [hcomp]
  refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _ ?_)
  · exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (Q := @RingHom.FiniteType)
      f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
  · exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2

omit f in
/-- The prime of a point in the ring of an affine open is the contraction of the maximal ideal of
its stalk. -/
theorem primeIdealOf_asIdeal {V : Y.Opens} (hV : IsAffineOpen V) {x : Y} (hx : x ∈ V) :
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal =
      (maximalIdeal (Y.presheaf.stalk x)).comap (Y.presheaf.germ V x hx).hom := by
  rw [hV.primeIdealOf_eq_map_closedPoint]
  rfl

omit f in
/-- For a closed point `x` of an affine open `V`, the contraction to `Γ(Y, V)` of the maximal ideal
of the stalk at `x` is a maximal ideal. -/
theorem isMaximal_comap_germ {V : Y.Opens} (hV : IsAffineOpen V) {x : Y} (hx : x ∈ V)
    (hxc : IsClosed ({x} : Set Y)) :
    ((maximalIdeal (Y.presheaf.stalk x)).comap (Y.presheaf.germ V x hx).hom).IsMaximal := by
  rw [← primeIdealOf_asIdeal hV hx, ← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  have : ({hV.primeIdealOf ⟨x, hx⟩} : Set (Spec Γ(Y, V))) = hV.fromSpec ⁻¹' {x} := by
    ext P
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      exact hV.fromSpec_primeIdealOf ⟨x, hx⟩
    · intro h
      apply hV.fromSpec.isOpenEmbedding.injective
      rw [h, hV.fromSpec_primeIdealOf ⟨x, hx⟩]
  have h2 : IsClosed (hV.fromSpec ⁻¹' {x}) := hxc.preimage hV.fromSpec.continuous
  rwa [← this] at h2

omit f in
/-- For `x` in an affine open `V`, every element `w` of the stalk at `x` satisfies `b * w = a` for
germs of sections `a`, `b` over `V` with the germ of `b` a unit. -/
theorem exists_germ_mul_eq {V : Y.Opens} (hV : IsAffineOpen V) {x : Y} (hx : x ∈ V)
    (w : Y.presheaf.stalk x) :
    ∃ a b : Γ(Y, V), Y.presheaf.germ V x hx b ∉ maximalIdeal (Y.presheaf.stalk x) ∧
      Y.presheaf.germ V x hx b * w = Y.presheaf.germ V x hx a := by
  let : Algebra Γ(Y, V) (Y.presheaf.stalk x) := (Y.presheaf.germ V x hx).hom.toAlgebra
  have := hV.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hab⟩ :=
    IsLocalization.surj (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl w
  refine ⟨a, b, ?_, ?_⟩
  · rwa [Ideal.mem_primeCompl_iff, primeIdealOf_asIdeal hV hx] at hb
  · rwa [mul_comm]

/-- **Through two closed points of an irreducible closed subset of dimension at least two passes a
smaller irreducible closed subset.** Let `Y` be locally of finite type over a field and `W ⊆ Y`
irreducible closed with `dim W ≥ 2`. For closed points `p`, `q` of `W` there is a point `t` of `W`,
not its generic point, specializing to both. The two points need not have a common affine
neighbourhood; see `Stacks.Algebraization.CurveThroughPoints.exists_prime_specializing`. -/
theorem exists_specializes_specializes [LocallyOfFiniteType f] (W : IrreducibleCloseds Y)
    (hW : 2 ≤ topologicalKrullDim (W : Set Y)) {p q : Y} (hpW : p ∈ (W : Set Y))
    (hqW : q ∈ (W : Set Y)) (hp : IsClosed ({p} : Set Y)) (hq : IsClosed ({q} : Set Y)) :
    ∃ t : Y, t ∈ (W : Set Y) ∧ closure ({t} : Set Y) ≠ (W : Set Y) ∧ t ⤳ p ∧ t ⤳ q := by
  classical
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨η, hη⟩ := QuasiSober.sober W.isIrreducible' W.isClosed'
  have hηx : ∀ {x}, x ∈ (W : Set Y) → η ⤳ x := fun hx => hη.specializes hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  obtain ⟨_, ⟨U', hU', rfl⟩, hqU', -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ q) isOpen_univ
  have hηU : η ∈ U := (hηx hpW).mem_open U.isOpen hpU
  have hηU' : η ∈ U' := (hηx hqW).mem_open U'.isOpen hqU'
  obtain ⟨r, ⟨⟨hrW, hrU⟩, hrU'⟩, hrc⟩ := nonempty_inter_closedPoints
    (Z := (W : Set Y) ∩ U ∩ U') ⟨η, ⟨hη.mem, hηU⟩, hηU'⟩
    ((W.isClosed'.isLocallyClosed.inter U.isOpen.isLocallyClosed).inter
      U'.isOpen.isLocallyClosed)
  have hr : IsClosed ({r} : Set Y) := mem_closedPoints_iff.mp hrc
  let hA : ∀ V : Y.Opens, Algebra k Γ(Y, V) := fun V => sectionsAlgebra f V
  let hS : ∀ x : Y, Algebra k (Y.presheaf.stalk x) := fun x => stalkAlgebra f x
  let : Algebra k (Y.residueField η) := residueAlgebra f η
  have := finiteType_sections f hU
  have := finiteType_sections f hU'
  set ρp := toResidueAlgHom f (hηx hpW)
  set ρq := toResidueAlgHom f (hηx hqW)
  set ρr := toResidueAlgHom f (hηx hrW)
  set gp := germAlgHom f U p hpU
  set gq := germAlgHom f U' q hqU'
  set gr := germAlgHom f U r hrU
  set gr' := germAlgHom f U' r hrU'
  have hpr : ρp.comp gp = ρr.comp gr := AlgHom.ext fun a => by
    simp only [AlgHom.comp_apply, ρp, ρr, gp, gr, toResidueAlgHom_germAlgHom]
  have hqr : ρq.comp gq = ρr.comp gr' := AlgHom.ext fun a => by
    simp only [AlgHom.comp_apply, ρq, ρr, gq, gr', toResidueAlgHom_germAlgHom]
  have hdim : 2 ≤ (Cardinal.toENat (Algebra.trdeg k (Y.residueField η)) : WithBot ℕ∞) := by
    rwa [← topologicalKrullDim_closure_singleton_eq_trdeg k Y f η, hη]
  have hgen : ∀ z : Y.residueField η, ∃ a b : Γ(Y, U), ρr (gr b) ≠ 0 ∧
      z = ρr (gr a) / ρr (gr b) := by
    intro z
    obtain ⟨w, rfl⟩ := Y.residue_surjective η z
    obtain ⟨a, b, hb, hab⟩ := exists_germ_mul_eq hU hηU w
    have hb0 : Y.residue η (Y.presheaf.germ U η hηU b) ≠ 0 :=
      fun h => hb ((residue_eq_zero_iff _).mp h)
    have hρ : ∀ c, ρr (gr c) = Y.residue η (Y.presheaf.germ U η hηU c) :=
      fun c => toResidueAlgHom_germAlgHom f _ U hrU c
    refine ⟨a, b, by rwa [hρ b], ?_⟩
    rw [hρ a, hρ b, eq_div_iff hb0, mul_comm, ← map_mul, hab]
  obtain ⟨Q, hQ, hkerQ, hQker, hQp, hQq⟩ := exists_prime_specializing ρp ρq ρr gp gq gr gr'
    hpr hqr (isMaximal_comap_germ hU hpU hp) (isMaximal_comap_germ hU' hqU' hq)
    (isMaximal_comap_germ hU hrU hr) (isMaximal_comap_germ hU' hrU' hr) (exists_germ_mul_eq hU hpU)
    (exists_germ_mul_eq hU' hqU') (exists_germ_mul_eq hU hrU) hgen hdim
  -- the point `η` of `Spec 𝒪_{Y,r}`
  have hkerP : (RingHom.ker ρr).IsPrime := RingHom.ker_isPrime ρr
  have hηP : Y.fromSpecStalk r ⟨RingHom.ker ρr, hkerP⟩ = η := by
    have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (hηx hrW)
    have h2 : (Spec.map (Y.presheaf.stalkSpecializes (hηx hrW))
        (closedPoint (Y.presheaf.stalk η)) : PrimeSpectrum (Y.presheaf.stalk r)) =
          ⟨RingHom.ker ρr, hkerP⟩ := by
      refine PrimeSpectrum.ext ?_
      ext x
      change Y.presheaf.stalkSpecializes (hηx hrW) x ∈ maximalIdeal _ ↔ ρr x = 0
      rw [← residue_eq_zero_iff]
      rfl
    calc Y.fromSpecStalk r ⟨RingHom.ker ρr, hkerP⟩
        = Y.fromSpecStalk r (Spec.map (Y.presheaf.stalkSpecializes (hηx hrW))
            (closedPoint (Y.presheaf.stalk η))) := by rw [h2]
      _ = (Spec.map (Y.presheaf.stalkSpecializes (hηx hrW)) ≫ Y.fromSpecStalk r)
            (closedPoint (Y.presheaf.stalk η)) := rfl
      _ = Y.fromSpecStalk η (closedPoint (Y.presheaf.stalk η)) := by rw [h1]
      _ = η := Scheme.fromSpecStalk_closedPoint
  set P : PrimeSpectrum (Y.presheaf.stalk r) := ⟨Q, hQ⟩ with hPdef
  set t := Y.fromSpecStalk r P with htdef
  have hηt : η ⤳ t := by
    rw [← hηP]
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp hkerQ).map (Y.fromSpecStalk r).continuous
  have hcl : closure ({η} : Set Y) = (W : Set Y) := hη
  have htW : t ∈ (W : Set Y) := by
    rw [← hcl]; exact specializes_iff_mem_closure.mp hηt
  have hne : closure ({t} : Set Y) ≠ (W : Set Y) := by
    intro h
    have htη : t = η := (show IsGenericPoint t (W : Set Y) from h).eq hη
    have hPeq : P = ⟨RingHom.ker ρr, hkerP⟩ :=
      (Y.fromSpecStalk r).isEmbedding.injective (by rw [hηP]; exact htη)
    apply hQker
    have := congrArg PrimeSpectrum.asIdeal hPeq
    exact this.le
  have hchart : ∀ {V : Y.Opens} (hV : IsAffineOpen V) (hrV : r ∈ V),
      t = hV.fromSpec (PrimeSpectrum.comap (Y.presheaf.germ V r hrV).hom P) := by
    intro V hV hrV
    rw [htdef, ← hV.fromSpecStalk_eq_fromSpecStalk hrV]
    rfl
  have hspec : ∀ {V : Y.Opens} (hV : IsAffineOpen V) (hrV : r ∈ V) {x : Y} (hxV : x ∈ V),
      Q.comap (Y.presheaf.germ V r hrV).hom ≤
        (maximalIdeal (Y.presheaf.stalk x)).comap (Y.presheaf.germ V x hxV).hom → t ⤳ x := by
    intro V hV hrV x hxV hQx
    have hle : PrimeSpectrum.comap (Y.presheaf.germ V r hrV).hom P ≤ hV.primeIdealOf ⟨x, hxV⟩ := by
      change Q.comap _ ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
      rw [primeIdealOf_asIdeal hV hxV]
      exact hQx
    have h := ((PrimeSpectrum.le_iff_specializes _ _).mp hle).map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf ⟨x, hxV⟩, ← hchart hV hrV] at h
  exact ⟨t, htW, hne, hspec hU hrU hpU hQp, hspec hU' hrU' hqU' hQq⟩


omit f in
/-- The dimension of an irreducible closed subset is its height among irreducible closed
subsets. -/
theorem topologicalKrullDim_eq_height {T : Type*} [TopologicalSpace T] (Z : IrreducibleCloseds T) :
    topologicalKrullDim (Z : Set T) = Order.height Z := by
  refine le_antisymm ?_ (height_le_topologicalKrullDim Z)
  let g : IrreducibleCloseds (Z : Set T) → Set.Iic Z := fun A =>
    ⟨⟨Subtype.val '' (A : Set (Z : Set T)),
      A.isIrreducible.image _ continuous_subtype_val.continuousOn,
      Z.isClosed.isClosedMap_subtype_val _ A.isClosed⟩, by
        rintro _ ⟨x, -, rfl⟩
        exact x.2⟩
  have hg : StrictMono g := fun A B hAB => Subtype.mk_lt_mk.mpr <| SetLike.coe_ssubset_coe.mp <|
    Subtype.val_injective.image_strictMono (SetLike.coe_ssubset_coe.mpr hAB)
  rw [topologicalKrullDim, Order.height_eq_krullDim_Iic]
  exact Order.krullDim_le_of_strictMono g hg

/-- The closure of a point of an irreducible closed subset is contained in it. -/
private theorem closureSingleton_le {W : IrreducibleCloseds Y} {x : Y} (hx : x ∈ (W : Set Y)) :
    closureSingleton x ≤ W := by
  rw [← SetLike.coe_subset_coe, coe_closureSingleton]
  exact closure_minimal (Set.singleton_subset_iff.mpr hx) W.isClosed'

/-- **Any two distinct closed points of an irreducible closed subset lie on a curve.** For `Y` of
finite type over a field, two distinct closed points `p`, `q` of an irreducible closed subset
`W ⊆ Y` lie on an irreducible closed subset of `Y` of dimension one.

`W` is cut down, keeping `p` and `q`, by
`Stacks.Algebraization.CurveThroughPoints.exists_specializes_specializes` until its dimension is
one; the dimension of `Y` is finite, so this terminates. -/
@[sga "6 X 7.11" "special case"]
theorem exists_dim_one_of_mem [LocallyOfFiniteType f] [QuasiCompact f] (W : IrreducibleCloseds Y)
    {p q : Y} (hpW : p ∈ (W : Set Y)) (hqW : q ∈ (W : Set Y)) (hp : IsClosed ({p} : Set Y))
    (hq : IsClosed ({q} : Set Y)) (hpq : p ≠ q) :
    ∃ C : IrreducibleCloseds Y, topologicalKrullDim (C : Set Y) = 1 ∧ p ∈ (C : Set Y) ∧
      q ∈ (C : Set Y) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have hfin : Order.height W ≠ ⊤ := by
    have h1 := Order.height_le_krullDim W
    have h2 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k f
    intro h
    rw [h] at h1
    exact h2 (top_le_iff.mp h1)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Order.height W ≤ N := ⟨(Order.height W).toNat,
    (ENat.natCast_toNat hfin).ge⟩
  induction N generalizing W with
  | zero =>
    exfalso
    have hW0 : Order.height W = 0 := nonpos_iff_eq_zero.mp (by exact_mod_cast hN)
    have hmin : ∀ C : IrreducibleCloseds Y, C ≤ W → C = W := fun C hC => by
      by_contra hne
      have := Order.height_strictMono (lt_of_le_of_ne hC hne)
        ((Order.height_mono hC).trans_lt (lt_top_iff_ne_top.mpr (by simp [hW0])))
      rw [hW0] at this
      exact not_lt_zero this
    have hp' := hmin (closureSingleton p) (closureSingleton_le hpW)
    have hq' := hmin (closureSingleton q) (closureSingleton_le hqW)
    have : closure ({p} : Set Y) = closure {q} := by
      rw [← coe_closureSingleton, ← coe_closureSingleton, hp', hq']
    rw [hp.closure_eq, hq.closure_eq, Set.singleton_eq_singleton_iff] at this
    exact hpq this
  | succ N ih =>
    by_cases h2 : 2 ≤ topologicalKrullDim (W : Set Y)
    · obtain ⟨t, htW, hne, htp, htq⟩ := exists_specializes_specializes f W h2 hpW hqW hp hq
      have hTW : closureSingleton t < W := by
        refine lt_of_le_of_ne (closureSingleton_le htW) fun h => hne ?_
        rw [← coe_closureSingleton, h]
      have hlt := Order.height_strictMono hTW (lt_of_le_of_lt (Order.height_mono hTW.le)
        (lt_top_iff_ne_top.mpr hfin))
      refine ih (closureSingleton t) ?_ ?_ (ne_top_of_lt hlt) ?_
      · rw [coe_closureSingleton]
        exact specializes_iff_mem_closure.mp htp
      · rw [coe_closureSingleton]
        exact specializes_iff_mem_closure.mp htq
      · exact Order.le_of_lt_succ (by simpa using lt_of_lt_of_le hlt hN)
    · refine ⟨W, ?_, hpW, hqW⟩
      push Not at h2
      rw [topologicalKrullDim_eq_height] at h2 ⊢
      -- the height is at least one, since `{p} < W`
      have hlt : closureSingleton p < W := by
        refine lt_of_le_of_ne (closureSingleton_le hpW) fun h => ?_
        have hqp : q ∈ (closureSingleton p : Set Y) := h ▸ hqW
        rw [coe_closureSingleton, hp.closure_eq] at hqp
        exact hpq hqp.symm
      have h1 : 1 ≤ Order.height W := by
        have := Order.height_strictMono hlt (lt_of_le_of_lt (Order.height_mono hlt.le)
          (lt_top_iff_ne_top.mpr hfin))
        exact Order.one_le_iff_pos.mpr (lt_of_le_of_lt bot_le this)
      have h2' : Order.height W ≤ 1 := by
        have : ((Order.height W : ℕ∞) : WithBot ℕ∞) < ((2 : ℕ∞) : WithBot ℕ∞) := h2
        have h3 : Order.height W < 2 := WithBot.coe_lt_coe.mp this
        exact Order.le_of_lt_succ (by simpa [one_add_one_eq_two] using h3)
      exact_mod_cast le_antisymm h2' h1

end Stacks.Algebraization.CurveThroughPoints

end
