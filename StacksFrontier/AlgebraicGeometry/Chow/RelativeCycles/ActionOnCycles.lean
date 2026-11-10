module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksCore.Tactic.StacksAttribute

/-!
# The action of a family of relative cycles on cycles on the base

Let `f : X ⟶ Y` be locally of finite type over a Chow situation `C`, let `α` be a family of
`r`-cycles on the fibres of `X/Y` and let `β` be an `e`-cycle on `Y`. The *action* of `α` on
`β` is the `(r + e)`-cycle on `X` obtained by taking, over each point of the support of `β`,
the corresponding fibrewise cycle: its coefficient at `x` is the coefficient of `β` at `f x`
times the coefficient of `α_{f x}` at the point of the fibre determined by `x`. This file
constructs that cycle and proves the action bilinear.

Two facts make the construction work. The coefficient function has locally finite support
because over an affine open of `Y` only finitely many points carry a nonzero coefficient of
`β`, and over each of them the part of the fibre lying in an affine open of `X` is compact, so
only finitely many points carry a nonzero fibrewise coefficient. And a point carrying a
nonzero coefficient has delta-dimension `r + e`, because transcendence degree is additive in
a tower and the fibre contributes exactly `r`.

## Main definitions

* `Stacks.Chow.capCoeff` — the coefficient function of the action.
* `Stacks.Chow.cap` — the action, as a cycle of delta-dimension `r + e`.

## Main results

* `Stacks.Chow.relativeDimension_comp_add_of_trdeg` — relative dimension over the base adds the
  transcendence degree of the residue field extension of the first morphism.
* `Stacks.Chow.fiber_trdeg_eq` — that transcendence degree is the one of the corresponding
  extension on the scheme-theoretic fibre.
* `Stacks.Chow.capCoeff_locallyFiniteSupport`, `Stacks.Chow.capCoeff_deltaDimension` — the two
  conditions making the coefficient function a cycle of the expected dimension.
* `Stacks.Chow.cap_add_left`, `Stacks.Chow.cap_add_right` — bilinearity of the action.

## Implementation notes

The coefficient is read at generic points rather than as a sum of closures of fibrewise
components; the two descriptions agree because the closure of a point of a fibre is cut out by
its generic point. The point of the fibre over `f x` determined by `x` is
`Scheme.Hom.asFiber`, so no choice of a fibre identification enters.

## References

* [Stacks Project, Tag 0H66](https://stacks.math.columbia.edu/tag/0H66)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow


/-- Relative dimension over the base adds the transcendence degree of the residue field
extension of the first morphism: additivity of transcendence degree in a tower. -/
theorem relativeDimension_comp_add_of_trdeg
    {P Z S : Scheme.{u}} (δ : DimensionFunction S)
    (p : P ⟶ Z) (q : Z ⟶ S)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] (x : P) (r : ℕ)
    (htrdeg : letI : Algebra (Z.residueField (p x)) (P.residueField x) :=
      (p.residueFieldMap x).hom.toAlgebra
      Cardinal.toNat (Algebra.trdeg (Z.residueField (p x)) (P.residueField x)) = r) :
    relativeDimension δ (p ≫ q) x =
      relativeDimension δ q (p x) + (r : ℤ) := by
  let K : Type u := S.residueField (q (p x))
  let L : Type u := Z.residueField (p x)
  let M : Type u := P.residueField x
  let : Algebra K L := (q.residueFieldMap (p x)).hom.toAlgebra
  let : Algebra L M := (p.residueFieldMap x).hom.toAlgebra
  let : Algebra K M := ((p ≫ q).residueFieldMap x).hom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun a => by
    change ((p ≫ q).residueFieldMap x).hom a =
      (p.residueFieldMap x).hom ((q.residueFieldMap (p x)).hom a)
    rw [Scheme.residueFieldMap_comp p q x]
    rfl
  let : Algebra.EssFiniteType K L :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap q (p x))
  let : Algebra.EssFiniteType L M :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap p x)
  unfold relativeDimension
  simp only [Scheme.Hom.comp_apply]
  change δ (q (p x)) +
      (Cardinal.toNat (Algebra.trdeg K M) : ℤ) =
    δ (q (p x)) + (Cardinal.toNat (Algebra.trdeg K L) : ℤ) + (r : ℤ)
  rw [← trdeg_add_eq K L (A := M),
    Cardinal.toNat_add (trdeg_lt_aleph0 K L) (trdeg_lt_aleph0 L M), htrdeg]
  omega

/-- A surjective local ring homomorphism induces a surjection of residue fields. -/
private theorem residueFieldMap_surjective_of_surjective
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] (hφ : Function.Surjective φ) :
    Function.Surjective (IsLocalRing.ResidueField.map φ) := by
  intro y
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := B) y
  obtain ⟨a, ha⟩ := hφ b
  refine ⟨IsLocalRing.residue A a, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue, ha]

/-- A preimmersion induces an isomorphism of residue fields: the stalk map is surjective and
the induced map of residue fields is injective. -/
private noncomputable def residueFieldMap_equiv_of_isPreimmersion
    {A B : Scheme.{u}} (g : A ⟶ B) [IsPreimmersion g] (x : A) :
    B.residueField (g x) ≃+* A.residueField x := by
  have hsurj : Function.Surjective (g.residueFieldMap x).hom :=
    residueFieldMap_surjective_of_surjective (g.stalkMap x).hom (g.stalkMap_surjective x)
  exact RingEquiv.ofBijective (g.residueFieldMap x).hom
    ⟨RingHom.injective _, hsurj⟩

/-- Composing two identifications of residue fields along equalities of points is the
identification along the composite equality, on elements. -/
private theorem residueFieldCongr_hom_apply_trans {X : Scheme.{u}} {a b c : X}
    (h₁ : a = b) (h₂ : b = c) (h₃ : a = c) (t : X.residueField a) :
    (X.residueFieldCongr h₂).hom.hom ((X.residueFieldCongr h₁).hom.hom t) =
      (X.residueFieldCongr h₃).hom.hom t := by
  subst h₁ h₂
  rfl

/-- The residue field map of `f` is natural with respect to identifications of residue fields
along an equality of points, on elements. -/
private theorem residueFieldMap_residueFieldCongr_inv_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    {x' x : X} (h : x' = x) (a : Y.residueField (f x)) :
    (f.residueFieldMap x').hom ((Y.residueFieldCongr (congrArg f h)).inv.hom a) =
      (X.residueFieldCongr h).inv.hom ((f.residueFieldMap x).hom a) := by
  subst h
  rfl

/-- The square of residue fields at the point of the fibre of `f` through `x` commutes. -/
private theorem residueFieldMap_fiberToSpecResidueField_comm {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X)
    (hy : (Y.fromSpecResidueField (f x)) (f.fiberToSpecResidueField (f x) (f.asFiber x)) = f x) :
    ((Y.residueFieldCongr hy).inv ≫ (Y.fromSpecResidueField (f x)).residueFieldMap
        (f.fiberToSpecResidueField (f x) (f.asFiber x))) ≫
      (f.fiberToSpecResidueField (f x)).residueFieldMap (f.asFiber x) =
    f.residueFieldMap x ≫ (X.residueFieldCongr (f.fiberι_asFiber x)).inv ≫
      (f.fiberι (f x)).residueFieldMap (f.asFiber x) := by
  let y : Y := f x
  let F := f.fiber y
  let z : F := f.asFiber x
  let q := f.fiberToSpecResidueField y
  let i := f.fiberι y
  have hix : i z = x := f.fiberι_asFiber x
  let j := (Y.residueFieldCongr hy).inv ≫ (Y.fromSpecResidueField y).residueFieldMap (q z)
  let d := (Y.residueFieldCongr (congrArg f hix)).inv
  have hpt : f (i z) = (Y.fromSpecResidueField y) (q z) :=
    congrArg (fun g : F ⟶ Y => g z) (f.fiber_fac y)
  have h := Scheme.Hom.residueFieldMap_congr (f.fiber_fac y) z
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at h
  apply CommRingCat.hom_ext
  ext a
  have hsource : (Y.residueFieldCongr hpt).hom.hom (d.hom a) =
      (Y.residueFieldCongr hy).inv.hom a :=
    residueFieldCongr_hom_apply_trans (congrArg f hix).symm hpt hy.symm a
  have h' := congrArg (fun t => t.hom (d.hom a)) h
  calc
    (q.residueFieldMap z).hom (j.hom a) =
        (q.residueFieldMap z).hom
          (((Y.fromSpecResidueField y).residueFieldMap (q z)).hom
            ((Y.residueFieldCongr hy).inv.hom a)) := rfl
    _ = (q.residueFieldMap z).hom
          (((Y.fromSpecResidueField y).residueFieldMap (q z)).hom
            ((Y.residueFieldCongr hpt).hom.hom (d.hom a))) := by
          rw [hsource]
    _ = (i.residueFieldMap z).hom ((f.residueFieldMap (i z)).hom (d.hom a)) := h'.symm
    _ = (i.residueFieldMap z).hom
          ((X.residueFieldCongr hix).inv.hom ((f.residueFieldMap x).hom a)) := by
          rw [residueFieldMap_residueFieldCongr_inv_apply f hix a]

/-- Transcendence degree is unchanged when the base field and the extension are replaced by
isomorphic ones, compatibly with the structure maps. -/
private theorem trdeg_toNat_eq_of_comm {K A L M : Type u} [Field K] [Field A] [Field L] [Field M]
    (j : K ≃+* A) (g : A →+* L) (e : L ≃+* M) (h : K →+* M) (hc : ∀ a, e (g (j a)) = h a) :
    letI : Algebra K M := h.toAlgebra
    letI : Algebra A L := g.toAlgebra
    Cardinal.toNat (Algebra.trdeg K M) = Cardinal.toNat (Algebra.trdeg A L) := by
  let : Algebra K M := h.toAlgebra
  let : Algebra A L := g.toAlgebra
  let : Algebra K A := j.toRingHom.toAlgebra
  let : Algebra A M := (e.toRingHom.comp g).toAlgebra
  let eA : L ≃ₐ[A] M := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  have : Algebra.IsAlgebraic K A := ⟨fun a => by
    obtain ⟨b, rfl⟩ := j.surjective a
    exact isAlgebraic_algebraMap b⟩
  have : IsScalarTower K A M := IsScalarTower.of_algebraMap_eq fun a => (hc a).symm
  have htrdegAdd := trdeg_add_eq K A (A := M)
  rw [trdeg_eq_zero, zero_add] at htrdegAdd
  rw [← htrdegAdd, ← AlgEquiv.trdeg_eq eA]

/-- The transcendence degree of the residue field extension that `f` induces at `x` is the
transcendence degree of the extension induced at the corresponding point of the scheme-theoretic
fibre through `x` by the structure morphism of that fibre to the spectrum of the residue field of
the base point.

The fibre inclusion is a preimmersion, so it induces an isomorphism of residue fields at `x`, and
the residue field of the base point embeds algebraically into the residue field of the base point
of the fibre, so contributes no transcendence degree. -/
theorem fiber_trdeg_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    letI : Algebra
        ((Spec (.of (Y.residueField (f x)))).residueField
          (f.fiberToSpecResidueField (f x) (f.asFiber x)))
        ((f.fiber (f x)).residueField (f.asFiber x)) :=
      ((f.fiberToSpecResidueField (f x)).residueFieldMap (f.asFiber x)).hom.toAlgebra
    Cardinal.toNat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) =
      Cardinal.toNat (Algebra.trdeg
        ((Spec (.of (Y.residueField (f x)))).residueField
          (f.fiberToSpecResidueField (f x) (f.asFiber x)))
        ((f.fiber (f x)).residueField (f.asFiber x))) := by
  let y : Y := f x
  let F := f.fiber y
  let z : F := f.asFiber x
  let q := f.fiberToSpecResidueField y
  let : Algebra ((Spec (.of (Y.residueField y))).residueField (q z)) (F.residueField z) :=
    (q.residueFieldMap z).hom.toAlgebra
  have htrdegX :
      let : Algebra (Y.residueField y) (X.residueField x) :=
        (f.residueFieldMap x).hom.toAlgebra
      Cardinal.toNat (Algebra.trdeg (Y.residueField y) (X.residueField x)) =
        Cardinal.toNat (Algebra.trdeg
          ((Spec (.of (Y.residueField y))).residueField (q z)) (F.residueField z)) := by
    let i := f.fiberι y
    have hix : i z = x := f.fiberι_asFiber x
    let e₀ := residueFieldMap_equiv_of_isPreimmersion i z
    let e : F.residueField z ≃+* X.residueField x :=
      e₀.symm.trans (X.residueFieldCongr hix).commRingCatIsoToRingEquiv
    have hy : (Y.fromSpecResidueField y) (q z) = y := by simp [q]
    let A := (Spec (.of (Y.residueField y))).residueField (q z)
    let j := (Y.residueFieldCongr hy).inv ≫
      (Y.fromSpecResidueField y).residueFieldMap (q z)
    let jEq : Y.residueField y ≃+* A :=
      (Y.residueFieldCongr hy).commRingCatIsoToRingEquiv.symm.trans
        (residueFieldMap_equiv_of_isPreimmersion (Y.fromSpecResidueField y) (q z))
    have hmaps : j ≫ q.residueFieldMap z =
        f.residueFieldMap x ≫ (X.residueFieldCongr hix).inv ≫ i.residueFieldMap z :=
      residueFieldMap_fiberToSpecResidueField_comm f x hy
    refine trdeg_toNat_eq_of_comm jEq (q.residueFieldMap z).hom e (f.residueFieldMap x).hom
      fun a => ?_
    change e ((q.residueFieldMap z).hom (j.hom a)) = (f.residueFieldMap x).hom a
    calc
      e ((q.residueFieldMap z).hom (j.hom a)) =
          e ((i.residueFieldMap z).hom
            ((X.residueFieldCongr hix).inv.hom ((f.residueFieldMap x).hom a))) :=
        congrArg (fun t : CommRingCat.Hom _ _ => e (t.hom a)) hmaps
      _ = (f.residueFieldMap x).hom a := by
        change (X.residueFieldCongr hix).hom.hom
          (e₀.symm ((i.residueFieldMap z).hom
            ((X.residueFieldCongr hix).inv.hom ((f.residueFieldMap x).hom a)))) = _
        have he₀ (b : X.residueField (i z)) :
            e₀.symm ((i.residueFieldMap z).hom b) = b :=
          e₀.symm_apply_apply b
        rw [he₀]
        exact congrArg (fun t : CommRingCat.Hom _ _ => t.hom
          ((f.residueFieldMap x).hom a)) (Iso.inv_hom_id (X.residueFieldCongr hix))
  simpa [y, F, z, q] using htrdegX

/-- At a point where the fibrewise cycle has a nonzero coefficient, the residue field extension
of `f` has transcendence degree `r`: on the fibre, delta-dimension is just transcendence degree
over the residue field of the base point. -/
private theorem fiber_trdeg_eq_of_cycle_coeff {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {r : ℕ}
    (α : FamilyOfCycles f r)
    (x : X)
    (hx : (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) ≠ 0) :
    letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Cardinal.toNat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) = r := by
  let y : Y := f x
  let F := f.fiber y
  let z : F := f.asFiber x
  let q := f.fiberToSpecResidueField y
  have : LocallyOfFiniteType q := by
    change LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y))
    infer_instance
  let C := fieldChowSituation (Y.residueField y)
  have hrel : relativeDimension C.dimensionFunction q z = (r : ℤ) :=
    (mem_cyclesOfDimension_iff_forall_point C q (r : ℤ) (α y : AlgebraicCycle F ℤ)).mp
      (α y).property z hx
  have hzero : C.dimensionFunction (q z) = 0 :=
    fieldChowSituation_dimensionFunction_eq_zero (Y.residueField y) (q z)
  have htrdeg :
      let : Algebra ((Spec (.of (Y.residueField y))).residueField (q z))
        (F.residueField z) := (q.residueFieldMap z).hom.toAlgebra
      Cardinal.toNat (Algebra.trdeg ((Spec (.of (Y.residueField y))).residueField (q z))
        (F.residueField z)) = r := by
    unfold relativeDimension at hrel
    simp only [hzero, zero_add] at hrel
    exact_mod_cast hrel
  exact (fiber_trdeg_eq f x).trans htrdeg

/-- For a morphism locally of finite type, the part of a fibre lying inside an affine open that
maps into an affine open of the base is compact. -/
private theorem fiber_preimage_affine_isCompact {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (s : Y)
    (U : Y.Opens) (hU : IsAffineOpen U) (hs : s ∈ U)
    (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) :
    IsCompact {z : f.fiber s | f.fiberι s z ∈ V} := by
  let g := f.resLE U V hVU
  let su : U.toScheme := ⟨s, hs⟩
  have : IsAffine (U.toScheme) := hU
  have : IsAffine (V.toScheme) := hV
  have : IsAffineHom g := isAffineHom_of_isAffine g
  let φ : g.fiber su → f.fiber s := fun t =>
    (f.fiberHomeo s).symm ⟨V.ι (g.fiberι su t), by
      have hgs : g (g.fiberι su t) = su := (g.range_fiberι su).le ⟨t, rfl⟩
      have heq := congrArg (fun k : V.toScheme ⟶ Y => k (g.fiberι su t))
        (Scheme.Hom.resLE_comp_ι f hVU)
      change U.ι (g (g.fiberι su t)) = f (V.ι (g.fiberι su t)) at heq
      change f (V.ι (g.fiberι su t)) = s
      rw [← heq, hgs]
      rfl⟩
  have hφ : Continuous φ := by
    dsimp [φ]
    fun_prop
  have hφι (t : g.fiber su) :
      f.fiberι s (φ t) = V.ι (g.fiberι su t) := by
    simp [φ]
  have hrange : Set.range φ = {z : f.fiber s | f.fiberι s z ∈ V} := by
    ext z
    refine ⟨?_, fun hz => ?_⟩
    · rintro ⟨t, rfl⟩
      change f.fiberι s (φ t) ∈ V
      rw [hφι]
      exact (g.fiberι su t).2
    · let v : V.toScheme := ⟨f.fiberι s z, hz⟩
      have hfx : f (V.ι v) = s := by
        simpa [v] using ((f.range_fiberι s).le ⟨z, rfl⟩ : f (f.fiberι s z) = s)
      have hgs : g v = su := by
        apply Subtype.ext
        change (f.resLE U V hVU v).1 = s
        rwa [Scheme.Hom.coe_resLE_apply]
      let t : g.fiber su := (g.fiberHomeo su).symm ⟨v, hgs⟩
      refine ⟨t, ?_⟩
      apply (f.fiberι s).isEmbedding.injective
      simp [φ, t, v]
  exact hrange ▸ isCompact_range hφ

/-- The coefficient of the action of a family of fibre cycles on a cycle of the base. -/
def capCoeff {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {r : ℕ} (α : FamilyOfCycles f r)
    (β : AlgebraicCycle Y ℤ) (x : X) : ℤ :=
  β (f x) * (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x)

/-- The coefficients of the action have locally finite support. -/
theorem capCoeff_locallyFiniteSupport {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    {r : ℕ} (α : FamilyOfCycles f r)
    (β : AlgebraicCycle Y ℤ) :
    LocallyFiniteSupport (capCoeff f α β) := by
  classical
  intro x
  let y := f x
  obtain ⟨O, hO, hβfinite⟩ :=
    (Function.locallyFinsupp.locallyFiniteSupport β : LocallyFiniteSupport (β : Y → ℤ)) y
  obtain ⟨O', hO'O, hO'open, hyO'⟩ := mem_nhds_iff.mp hO
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUO⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyO' hO'open
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (by simpa [y] using hyU) (f ⁻¹ᵁ (U : Y.Opens)).2
  let T : Set Y := {s | s ∈ (U : Set Y) ∧ (β : Y → ℤ) s ≠ 0}
  have hT : T.Finite := hβfinite.subset fun s hs => ⟨hO'O (hUO hs.1), hs.2⟩
  let E (s : Y) (hs : s ∈ (U : Set Y)) : Set (f.fiber s) :=
    {z | f.fiberι s z ∈ V ∧ (α s : AlgebraicCycle (f.fiber s) ℤ) z ≠ 0}
  have hE : ∀ s hs, (E s hs).Finite := fun s hs =>
    ((Function.locallyFinsupp.locallyFiniteSupport (α s : AlgebraicCycle (f.fiber s) ℤ)
      ).finite_inter_support_of_isCompact
      (fiber_preimage_affine_isCompact f s U hU hs V hV hVU)).subset fun _ hz => ⟨hz.1, hz.2⟩
  let : Fintype {s : Y // s ∈ T} := hT.fintype
  let (s : {s : Y // s ∈ T}) : Fintype (E s.1 s.2.1) := (hE s.1 s.2.1).fintype
  let D := Σ s : {s : Y // s ∈ T}, {z : f.fiber s.1 // z ∈ E s.1 s.2.1}
  let g : D → X := fun p => f.fiberι p.1.1 p.2.1
  have hfiniteV : ((V : Set X) ∩ (capCoeff f α β).support).Finite := by
    apply (Set.finite_range g).subset
    intro x hx
    have hprod : (β : Y → ℤ) (f x) *
        (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) ≠ 0 := by
      simpa [capCoeff] using hx.2
    rcases mul_ne_zero_iff.mp hprod with ⟨hβx, hαx⟩
    let s : {s : Y // s ∈ T} := ⟨f x, hVU hx.1, hβx⟩
    let z : f.fiber (f x) := f.asFiber x
    have hzE : z ∈ E s.1 s.2.1 :=
      ⟨by simpa [z, s, Scheme.Hom.fiberι_asFiber] using hx.1, hαx⟩
    refine ⟨⟨s, ⟨z, hzE⟩⟩, ?_⟩
    simp [g, s, z, Scheme.Hom.fiberι_asFiber]
  refine ⟨(V : Set X), V.2.mem_nhds hxV, ?_⟩
  simpa [Function.mem_support] using hfiniteV

/-- A nonzero component of the action has the expected delta-dimension. -/
theorem capCoeff_deltaDimension
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (s : Y ⟶ C.S) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    {r : ℕ} (α : FamilyOfCycles f r)
    {e : ℤ} (β : CycleGroup C s e)
    (Z : IrreducibleCloseds X)
    (hZ : capCoeff f α (β : AlgebraicCycle Y ℤ) Z.isIrreducible.genericPoint ≠ 0) :
    letI : LocallyOfFiniteType (f ≫ s) := inferInstance
    deltaDimension C (f ≫ s) Z = (r : ℤ) + e := by
  let x := Z.isIrreducible.genericPoint
  obtain ⟨hβ, hα⟩ : β.1 (f x) ≠ 0 ∧
      (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) ≠ 0 :=
    mul_ne_zero_iff.mp hZ
  have hβrel : relativeDimension C.dimensionFunction s (f x) = (e : ℤ) :=
    (mem_cyclesOfDimension_iff_forall_point C s e β.1).mp β.2 (f x) hβ
  have hcomp := relativeDimension_comp_add_of_trdeg C.dimensionFunction f s x r
    (fiber_trdeg_eq_of_cycle_coeff f α x hα)
  rw [hβrel] at hcomp
  rw [deltaDimension_eq_of_isGenericPoint C (f ≫ s) Z x
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)]
  omega

/-- The action of a family of fibre cycles on a cycle of the base. -/
def cap (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (s : Y ⟶ C.S) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    {r : ℕ} (α : FamilyOfCycles f r)
    {e : ℤ} (β : CycleGroup C s e) :
    letI : LocallyOfFiniteType (f ≫ s) := inferInstance
    CycleGroup C (f ≫ s) ((r : ℤ) + e) := by
  letI : LocallyOfFiniteType (f ≫ s) := inferInstance
  let γ : AlgebraicCycle X ℤ := {
    toFun := capCoeff f α (β : AlgebraicCycle Y ℤ)
    supportWithinDomain' := Set.subset_univ _
    supportLocallyFiniteWithinDomain' := fun x _ =>
      capCoeff_locallyFiniteSupport f α (β : AlgebraicCycle Y ℤ) x }
  exact ⟨γ, fun Z hZ => capCoeff_deltaDimension C s f α β Z hZ⟩

/-- The coefficient of `cap C s f α β` at a point `x` of `X` is `capCoeff f α β x`. -/
@[simp] theorem cap_apply (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (s : Y ⟶ C.S) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    {r : ℕ} (α : FamilyOfCycles f r)
    {e : ℤ} (β : CycleGroup C s e) (x : X) :
    letI : LocallyOfFiniteType (f ≫ s) := inferInstance
    (cap C s f α β : AlgebraicCycle X ℤ) x =
      capCoeff f α (β : AlgebraicCycle Y ℤ) x := rfl

/-- The action is additive in the family of fibre cycles. -/
@[stacks 0H66 "additivity in the family of fibre cycles"]
theorem cap_add_left (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (s : Y ⟶ C.S) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [LocallyOfFiniteType f] {r : ℕ}
    (α₁ α₂ : FamilyOfCycles f r)
    {e : ℤ} (β : CycleGroup C s e) :
    letI : LocallyOfFiniteType (f ≫ s) := inferInstance
    cap C s f (α₁ + α₂) β = cap C s f α₁ β + cap C s f α₂ β := by
  ext x
  simp [cap_apply, capCoeff, mul_add]

/-- The action is additive in the cycle on the base. -/
@[stacks 0H66 "additivity in the cycle on the base"]
theorem cap_add_right (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (s : Y ⟶ C.S) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [LocallyOfFiniteType f] {r : ℕ}
    (α : FamilyOfCycles f r)
    {e : ℤ} (β₁ β₂ : CycleGroup C s e) :
    letI : LocallyOfFiniteType (f ≫ s) := inferInstance
    cap C s f α (β₁ + β₂) = cap C s f α β₁ + cap C s f α β₂ := by
  ext x
  simp [cap_apply, capCoeff, add_mul]

end Stacks.Chow
