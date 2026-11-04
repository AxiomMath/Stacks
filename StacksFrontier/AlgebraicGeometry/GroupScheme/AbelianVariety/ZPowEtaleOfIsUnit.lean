module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.SeparablyClosedDivisiblePoints
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowEtale
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowTangentLeftUnit
public import StacksFrontier.AlgebraicGeometry.GroupScheme.UnramifiedTranslation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchConnected
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Multiplication by an integer invertible in the ground field is étale

For every abelian variety `A` over a field `k` and every integer `d` invertible in `k`,
multiplication by `d` on `A` is étale and surjective. This is the étale clause of
[Stacks, Tag 03RP], in the form `Stacks.Groupoids.EtaleZPowIdOfIsUnit`, and the "if" half of
[Stacks, Tag 0BFH].

## Main results

* `Stacks.Groupoids.unramified_natCast_zpow_id_left`: multiplication by `n + 1` is unramified
  when `n + 1` is invertible in `k`.
* `Stacks.Groupoids.etaleAt_natCast_zpow_id_left_unit`: it is étale at the identity.
* `Stacks.Groupoids.etale_zpow_id_left_of_isUnit`: multiplication by `d` is étale for every
  integer `d` invertible in `k`.
* `Stacks.Groupoids.etaleZPowIdOfIsUnit`: the étale clause of Tag 03RP for every abelian
  variety.
* `Stacks.Groupoids.surjective_zpow_id_left_of_isUnit`: multiplication by `d` is surjective.

## Implementation notes

The source proof goes through Tag 0BFG (finite local freeness of `[d]`), which needs the theorem
of the cube; this proof does not. It runs as follows.

1. *Unramified at the identity.* The differential of `[n]` at the identity is multiplication by
   `n` (`AlgebraicGeometry.injective_tangentMap_pow_id_left`, from Tag 0BF5), which is injective
   when `n` is invertible, so `[n]` is unramified there by Tag 0B2G.
2. *Unramified everywhere.* `[n]` is a homomorphism because an abelian variety is commutative
   (Tag 0BFD), and a homomorphism unramified along the unit section is unramified
   (`AlgebraicGeometry.unramifiedAt_of_forall_unramifiedAt_unit`).
3. *Étale at the identity.* `[n]` fixes the identity, so its local homomorphism there is a local
   endomorphism of the regular local ring `𝒪_{A,e}`, and unramifiedness makes the fibre ring a
   field. Miracle flatness (Tag 00R4) gives flatness, and flat and unramified is étale.
4. *Étale everywhere.* Étaleness on a neighbourhood of the identity makes the image of `[n]`
   contain a nonempty open set, so `[n]` sends the generic point to the generic point. An
   abelian variety is smooth, hence normal, hence geometrically unibranch, so the criterion of
   Tag 0GS8 — an unramified morphism into a geometrically unibranch integral scheme is étale at
   every point that specializes from a point over the generic point — applies everywhere.

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Tag 0GS8](https://stacks.math.columbia.edu/tag/0GS8)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

omit [GrpObj A] in
/-- An integer invertible in the ground field is invertible in every residue field of a scheme
over it. -/
theorem isUnit_natCast_residueField (n : ℕ) (hn : IsUnit ((n : ℤ) : k)) (x : A.left) :
    IsUnit ((n : A.left.residueField x)) := by
  let ψ : k →+* A.left.residueField x :=
    (A.hom.residueFieldMap x).hom.comp (((Spec (.of k)).residue (A.hom x)).hom.comp
      (((Spec (.of k)).presheaf.germ ⊤ (A.hom x) trivial).hom.comp
        (Scheme.ΓSpecIso (.of k)).inv.hom))
  have h := hn.map ψ
  rwa [Int.cast_natCast, map_natCast] at h

/-- Multiplication by an integer on a commutative group object is multiplicative. -/
theorem mul_comp_zpow_id [IsCommMonObj A] (d : ℤ) :
    (fst A A * snd A A) ≫ (𝟙 A) ^ d = (fst A A ≫ (𝟙 A) ^ d) * (snd A A ≫ (𝟙 A) ^ d) := by
  rw [GrpObj.comp_zpow, GrpObj.comp_zpow, GrpObj.comp_zpow, Category.comp_id,
    Category.comp_id, Category.comp_id, mul_zpow]

/-- **Multiplication by an integer invertible in the ground field on an abelian variety is
unramified.** It is unramified at the identity by the tangent-space computation
`AlgebraicGeometry.unramifiedAt_pow_id_left`, and a homomorphism of group schemes unramified
along the unit section is unramified everywhere,
`AlgebraicGeometry.unramifiedAt_of_forall_unramifiedAt_unit`. -/
theorem unramified_natCast_zpow_id_left [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ)
    (hn : IsUnit (((n + 1 : ℕ) : ℤ) : k)) :
    Unramified ((𝟙 A) ^ ((n + 1 : ℕ) : ℤ)).left := by
  have := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have := locallyOfFinitePresentation_zpow_id_left A ((n + 1 : ℕ) : ℤ)
  refine ⟨unramifiedAt_of_forall_unramifiedAt_unit _ (mul_comp_zpow_id A _) fun s => ?_⟩
  exact unramifiedAt_pow_id_left A s n (isUnit_natCast_residueField A (n + 1) hn _)

/-- **Multiplication by an integer invertible in the ground field on an abelian variety is
étale at the identity.** It is unramified there, so the fibre ring of its local homomorphism
at the identity is the residue field, of dimension zero; the source and target local rings are
the same regular local ring, so miracle flatness (Tag 00R4) makes the local homomorphism flat,
and flat and unramified is étale (Tag 02GU). -/
theorem etaleAt_natCast_zpow_id_left_unit [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ)
    (hn : IsUnit (((n + 1 : ℕ) : ℤ) : k)) (s : Spec (.of k)) :
    EtaleAt ((𝟙 A) ^ ((n + 1 : ℕ) : ℤ)).left ((η[A]).left s) := by
  have := smooth_hom A
  have := locallyOfFinitePresentation_zpow_id_left A ((n + 1 : ℕ) : ℤ)
  have hU := unramified_natCast_zpow_id_left A n hn
  set φ := ((𝟙 A) ^ ((n + 1 : ℕ) : ℤ)).left with hφ
  have hu : UnramifiedAt φ ((η[A]).left s) := hU.unramifiedAt _
  have hfix : φ ((η[A]).left s) = (η[A]).left s := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun g => g s)
      (AlgebraicGeometry.unit_left_comp_zpow_id_left A ((n + 1 : ℕ) : ℤ))
  have := isRegularLocalRing_stalk_of_smooth_over_field A.hom ((η[A]).left s)
  have := isRegularLocalRing_stalk_of_smooth_over_field A.hom (φ ((η[A]).left s))
  have hmax' := ((unramifiedAt_tfae φ ((η[A]).left s)).out 1 7).1 hu
  have hmax := hmax'.1
  have hflat : (φ.stalkMap ((η[A]).left s)).hom.Flat := by
    refine flat_stalkMap_of_ringKrullDim_quotient_eq_zero φ _ ?_ ?_
    · rw [hmax]
      exact ringKrullDim_eq_zero_of_isField
        ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance)
    · rw [hfix]
  have hsub := ((unramifiedAt_tfae φ ((η[A]).left s)).out 1 3).1 hu
  have h14 := (etaleAt_tfae φ ((η[A]).left s)).out 1 4
  exact h14.2 ⟨hflat, hsub⟩

/-- Multiplication by an integer invertible in the ground field on an abelian variety sends the
generic point to the generic point. It is étale at the identity, hence étale on an open
neighbourhood of it, whose image is therefore a nonempty open subset and so contains the generic
point; the generic point of the source specializes to a preimage of it. -/
theorem natCast_zpow_id_left_genericPoint [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ)
    (hn : IsUnit (((n + 1 : ℕ) : ℤ) : k)) :
    ((𝟙 A) ^ ((n + 1 : ℕ) : ℤ)).left (genericPoint A.left) = genericPoint A.left := by
  set φ := ((𝟙 A) ^ ((n + 1 : ℕ) : ℤ)).left with hφ
  let s : Spec (.of k) := Nonempty.some inferInstance
  obtain ⟨U, hU, heU, V, hV, hUV, het⟩ := etaleAt_natCast_zpow_id_left_unit A n hn s
  have : Etale (φ.resLE V U hUV) := etale_resLE_of_appLE_etale φ U hU V hV hUV het
  obtain ⟨hflat, -, hfp⟩ := Etale.iff_flat_and_formallyUnramified.mp
    (inferInstance : Etale (φ.resLE V U hUV))
  have hW : IsOpen (Set.range (U.ι ≫ φ)) := by
    rw [← Scheme.Hom.resLE_comp_ι φ hUV]
    have hc : ⇑(φ.resLE V U hUV ≫ V.ι) = V.ι ∘ φ.resLE V U hUV := rfl
    rw [hc, Set.range_comp]
    exact V.ι.isOpenEmbedding.isOpenMap _ (Scheme.Hom.isOpenMap _).isOpen_range
  obtain ⟨u, hu⟩ : genericPoint A.left ∈ Set.range (U.ι ≫ φ) :=
    ((genericPoint_spec A.left).mem_open_set_iff hW).2
      ⟨_, Set.mem_univ _, ⟨⟨_, heU⟩, rfl⟩⟩
  have hsp : φ (genericPoint A.left) ⤳ genericPoint A.left := by
    have h := (genericPoint_specializes (U.ι u)).map φ.continuous
    have h' : φ (U.ι u) = genericPoint A.left := hu
    rwa [h'] at h
  refine ((genericPoint_spec A.left).eq ?_).symm
  rw [isGenericPoint_iff_specializes]
  exact fun y => ⟨fun _ => Set.mem_univ y, fun _ => hsp.trans (genericPoint_specializes y)⟩

/-- **Multiplication by a positive integer invertible in the ground field on an abelian variety
is étale.** It is unramified, the abelian variety is integral and normal, hence geometrically
unibranch, and it sends the generic point to the generic point, so the criterion of Tag 0GS8
applies at every point. -/
theorem etale_natCast_zpow_id_left [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ)
    (hn : IsUnit (((n + 1 : ℕ) : ℤ) : k)) :
    Etale ((𝟙 A) ^ ((n + 1 : ℕ) : ℤ)).left := by
  have := smooth_hom A
  have := locallyOfFinitePresentation_zpow_id_left A ((n + 1 : ℕ) : ℤ)
  have : IsNormal A.left := isNormal_of_smooth_over_field A.hom
  have hU := unramified_natCast_zpow_id_left A n hn
  refine (etale_iff_forall_etaleAt _).2 fun x => ?_
  exact etaleAt_of_unramifiedAt_of_specializes_genericPoint _
    (isGeometricallyUnibranch_of_isNormal _) (genericPoint_specializes x)
    (natCast_zpow_id_left_genericPoint A n hn) (hU.unramifiedAt x)

/-- **Multiplication by an integer invertible in the ground field on an abelian variety is
étale.** This is the implication "`d` invertible in `k` ⟹ `[d]` étale" of [Stacks, Tag 0BFH],
for every abelian variety over every field. The sign of `d` is removed by inversion, and `d = 0`
is never invertible. -/
theorem etale_zpow_id_left_of_isUnit [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (hd : IsUnit ((d : ℤ) : k)) :
    Etale ((𝟙 A) ^ d).left := by
  have key : ∀ n : ℕ, IsUnit (((n : ℤ)) : k) → Etale ((𝟙 A) ^ (n : ℤ)).left
    | 0, hn => by simp at hn
    | m + 1, hn => etale_natCast_zpow_id_left A m hn
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · exact key n hd
  · exact (etale_zpow_id_neg_iff A _).2 (key n ((isUnit_intCast_neg_iff _).1 hd))

/-- **The étale clause of [Stacks, Tag 03RP].** For every abelian variety `A`
over a field `k`, multiplication by every integer invertible in `k` is étale. -/
theorem etaleZPowIdOfIsUnit [AlgebraicGeometry.IsAbelianVariety k A] :
    EtaleZPowIdOfIsUnit k A :=
  fun d hd => etale_zpow_id_left_of_isUnit A d hd

/-- **Multiplication by an integer invertible in the ground field on an abelian variety is
surjective.** It is étale, `Stacks.Groupoids.etale_zpow_id_left_of_isUnit`, and an étale
endomorphism of an abelian variety is surjective,
`Stacks.Groupoids.surjective_zpow_id_left_of_etale`. -/
@[sga "7 IX 2.2.1" "special case"]
theorem surjective_zpow_id_left_of_isUnit [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (hd : IsUnit ((d : ℤ) : k)) :
    Surjective ((𝟙 A) ^ d).left :=
  surjective_zpow_id_left_of_etale A d (etale_zpow_id_left_of_isUnit A d hd)

end Stacks.Groupoids
