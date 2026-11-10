module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowRank0BFG
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rational points of an abelian variety over a separably closed field are divisible

Let `A` be an abelian variety over a separably closed field `k` on which multiplication by every
integer invertible in `k` is étale, and let `n` be an integer invertible in `k`. Then every
`k`-rational point of `A` is `[n]` of a `k`-rational point of `A`. A `k`-rational point of `A` is
a section `g` of the structure morphism, `g ≫ A.hom = 𝟙`, and multiplication by `n` is
`((𝟙 A) ^ n).left`, the `n`-th power of the identity in the group of endomorphisms of `A`.

## Main definitions

* `Stacks.Groupoids.EtaleZPowIdOfIsUnit`: multiplication by `d` on a group scheme over `k` is
  étale whenever `d` is invertible in `k`.

## Main results

* `AlgebraicGeometry.exists_comp_eq_id_of_etale_of_isSepClosed`: a nonempty scheme étale over a
  separably closed field has a rational point, i.e. its structure morphism has a section.
* `Stacks.Groupoids.surjective_zpow_id_left_of_etale`: if multiplication by `d` on an abelian
  variety is étale then it is surjective.
* `Stacks.Groupoids.etaleZPowIdOfIsUnit_of_isIso_hom`: `EtaleZPowIdOfIsUnit` holds for a group
  scheme whose structure morphism is an isomorphism.
* `Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed`: if `EtaleZPowIdOfIsUnit` holds
  for an abelian variety `A` over a separably closed field `k`, then every `k`-rational point of
  `A` is `[n]` of a `k`-rational point, for `n` invertible in `k`.

## References

* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 03RO](https://stacks.math.columbia.edu/tag/03RO)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- A nonempty scheme étale over a separably closed field has a rational point: its structure
morphism has a section. -/
@[sga "4 VIII 3.2" "partial"]
theorem exists_comp_eq_id_of_etale_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of k)) [Etale f] (x : U) :
    ∃ s : Spec (.of k) ⟶ U, s ≫ f = 𝟙 (Spec (.of k)) := by
  obtain ⟨I, K, hK, hAlg, hFin, hSep, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k f).mp inferInstance
  let (i : I) : Field (K i) := hK i
  let (i : I) : Algebra k (K i) := hAlg i
  let (i : I) : Module.Finite k (K i) := hFin i
  let (i : I) : Algebra.IsSeparable k (K i) := hSep i
  obtain ⟨⟨i, -⟩, -⟩ := (sigmaMk fun j ↦ Spec (CommRingCat.of (K j))).surjective (e.hom x)
  have hbij : Function.Bijective (algebraMap k (K i)) := IsSepClosed.algebraMap_bijective k (K i)
  have hid : CommRingCat.ofHom (algebraMap k (K i)) ≫
      CommRingCat.ofHom (RingEquiv.ofBijective (algebraMap k (K i)) hbij).symm.toRingHom =
        𝟙 (CommRingCat.of k) := by
    ext a
    simpa using (RingEquiv.ofBijective (algebraMap k (K i)) hbij).symm_apply_apply a
  refine ⟨Spec.map (CommRingCat.ofHom
      (RingEquiv.ofBijective (algebraMap k (K i)) hbij).symm.toRingHom) ≫
    Sigma.ι (fun j ↦ Spec (CommRingCat.of (K j))) i ≫ e.inv, ?_⟩
  rw [← he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Sigma.ι_comp_desc, ← Spec.map_comp, hid,
    Spec.map_id]

end AlgebraicGeometry

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Multiplication by `d` on an abelian variety is surjective if it is étale. -/
theorem surjective_zpow_id_left_of_etale [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (h : Etale ((𝟙 A : A ⟶ A) ^ d).left) :
    Surjective ((𝟙 A : A ⟶ A) ^ d).left := by
  obtain ⟨hflat, -, hfp⟩ := Etale.iff_flat_and_formallyUnramified.mp h
  have := isProper_zpow_id_left A d
  exact ⟨Set.range_eq_univ.mp <| IsClopen.eq_univ
    ⟨(Scheme.Hom.isClosedMap _).isClosed_range, (Scheme.Hom.isOpenMap _).isOpen_range⟩
    (Set.range_nonempty _)⟩

/-- Multiplication by an integer `d` on `A` is étale whenever `d` is invertible in the ground
field. -/
def EtaleZPowIdOfIsUnit (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A] : Prop :=
  ∀ d : ℤ, IsUnit ((d : ℤ) : k) → Etale ((𝟙 A : A ⟶ A) ^ d).left

/-- `EtaleZPowIdOfIsUnit k A` holds for a group scheme `A` whose structure morphism is an
isomorphism. -/
theorem etaleZPowIdOfIsUnit_of_isIso_hom [IsIso A.hom] : EtaleZPowIdOfIsUnit k A := by
  intro d _
  have hid : ((𝟙 A : A ⟶ A) ^ d).left = 𝟙 A.left :=
    (cancel_mono A.hom).mp (by rw [zpow_id_left_comp_hom, Category.id_comp])
  rw [hid]
  infer_instance

/-- Let `A` be an abelian variety over a separably closed field `k` on which multiplication by
every integer invertible in `k` is étale, let `n` be an integer invertible in `k`, and let `g` be
a `k`-rational point of `A`. Then `g = [n] ∘ g'` for some `k`-rational point `g'` of `A`. -/
theorem exists_comp_zpow_id_left_eq_of_isSepClosed [IsSepClosed k]
    [AlgebraicGeometry.IsAbelianVariety k A] (h03RP : EtaleZPowIdOfIsUnit k A)
    (n : ℤ) (hn : IsUnit ((n : ℤ) : k))
    (g : Spec (.of k) ⟶ A.left) (hg : g ≫ A.hom = 𝟙 (Spec (.of k))) :
    ∃ g' : Spec (.of k) ⟶ A.left, g' ≫ A.hom = 𝟙 (Spec (.of k)) ∧
      g' ≫ ((𝟙 A : A ⟶ A) ^ n).left = g := by
  have hE : Etale ((𝟙 A : A ⟶ A) ^ n).left := h03RP n hn
  have := surjective_zpow_id_left_of_etale A n hE
  obtain ⟨p, -⟩ := (pullback.snd ((𝟙 A : A ⟶ A) ^ n).left g).surjective
    (Nonempty.some (inferInstanceAs (Nonempty ↥(Spec (CommRingCat.of k)))))
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_etale_of_isSepClosed k
    (pullback.snd ((𝟙 A : A ⟶ A) ^ n).left g) p
  have key : (s ≫ pullback.fst ((𝟙 A : A ⟶ A) ^ n).left g) ≫
      ((𝟙 A : A ⟶ A) ^ n).left = g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  refine ⟨s ≫ pullback.fst ((𝟙 A : A ⟶ A) ^ n).left g, ?_, key⟩
  simpa only [Category.assoc, zpow_id_left_comp_hom, hg] using congrArg (· ≫ A.hom) key

end Stacks.Groupoids

end
