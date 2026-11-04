module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechConerveTensor

/-!
# The low degrees of the Čech conerve of an algebra map, as tensor powers

For a commutative `B`-algebra `C` the Čech conerve `(C/B)•` of the structure arrow `B ⟶ C` is
an abstract wide pushout: its value in degree `n` is characterised by a universal property and
is never literally the `(n + 1)`-fold tensor power of `C` over `B`. Every computation with a
concrete tensor power therefore needs an explicit identification, one degree at a time. This
file supplies them in degrees `0`, `1` and `2`, together with the images of the Čech
coprojections and of the coface maps between those degrees.

Degrees `0`, `1`, `2` are exactly the degrees that a descent datum for `C / B` lives in: the
module in degree `0`, the transition isomorphism in degree `1`, and the cocycle condition in
degree `2`.

## Main definitions

* `Stacks.Descent.cechDegZeroIso` is the identification `(C/B)₀ ≅ C`.
* `Stacks.Descent.cechSquare` is `C ⊗[B] C` and `Stacks.Descent.cechDegOneIso` the
  identification `(C/B)₁ ≅ C ⊗[B] C`.
* `Stacks.Descent.cechCube` is `C ⊗[B] C ⊗[B] C` and `Stacks.Descent.cechDegTwoIso` the
  identification `(C/B)₂ ≅ C ⊗[B] C ⊗[B] C`.

## Main results

* `Stacks.Descent.cechι_zero_comp_cechDegOneFwd` and
  `Stacks.Descent.cechι_one_comp_cechDegOneFwd` identify the two Čech coprojections in degree
  `1` with the two inclusions of `C` into `C ⊗[B] C`; the three lemmas
  `Stacks.Descent.cechι_zero_comp_cechDegTwoFwd`,
  `Stacks.Descent.cechι_one_comp_cechDegTwoFwd` and
  `Stacks.Descent.cechι_two_comp_cechDegTwoFwd` do the same in degree `2`.
* `Stacks.Descent.cechDegZeroIso_inv_comp_map_delta_zero` and
  `Stacks.Descent.cechDegZeroIso_inv_comp_map_delta_one` identify the two coface maps
  `(C/B)₀ ⟶ (C/B)₁` with `c ↦ 1 ⊗ c` and `c ↦ c ⊗ 1`.
* `Stacks.Descent.cechDegOneBwd_comp_map_delta_zero`,
  `Stacks.Descent.cechDegOneBwd_comp_map_delta_one` and
  `Stacks.Descent.cechDegOneBwd_comp_map_delta_two` identify the three coface maps
  `(C/B)₁ ⟶ (C/B)₂` with `c ⊗ c' ↦ 1 ⊗ c ⊗ c'`, `c ⊗ c' ↦ c ⊗ 1 ⊗ c'` and
  `c ⊗ c' ↦ c ⊗ c' ⊗ 1`. These are the three positions in which a transition isomorphism in
  degree `1` is pulled back to degree `2`.

## Implementation notes

Each comparison is given in both directions by the two universal properties available: the map
out of `(C/B)ₙ` is a `WidePushout.desc` and the map into it an `Algebra.TensorProduct.lift`. The
two composites are then checked on the Čech coprojections and on the tensor inclusions
respectively, so no formula on a general element is ever needed.

The coface maps are read off from `CategoryTheory.Arrow.cechι_comp_map`: a coface map carries
the `i`-th coprojection of the source degree to the `β(i)`-th coprojection of the target
degree, so it suffices to evaluate the order homomorphism of `SimplexCategory.δ`.

Everything is stated for a `B`-algebra `C` with `B` and `C` in a single universe, matching
`Stacks.Descent.algebraArrow`. `Stacks.Descent.algebraMapArrow_eq` transports the results to
the universe-lifted arrow used to form the Čech conerve of a general algebra map.

## References

* [Stacks Project, Tag 023K](https://stacks.math.columbia.edu/tag/023K)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Arrow
open scoped TensorProduct

universe u

namespace Stacks.Descent

variable (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]

/-! ### Two values of the coface order homomorphisms -/

/-- A coface map omits an index above the one it is applied to: `δ i` fixes `j` when `j < i`. -/
lemma delta_toOrderHom_of_castSucc_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : j.castSucc < i) : (SimplexCategory.δ i).toOrderHom j = j.castSucc := by
  simpa [SimplexCategory.δ] using Fin.succAbove_of_castSucc_lt i j h

/-- A coface map shifts an index at or above the one it is applied to: `δ i` sends `j` to
`j + 1` when `i ≤ j`. -/
lemma delta_toOrderHom_of_le_castSucc {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : i ≤ j.castSucc) : (SimplexCategory.δ i).toOrderHom j = j.succ := by
  simpa [SimplexCategory.δ] using Fin.succAbove_of_le_castSucc i j h

/-- Two morphisms out of `M ⊗[B] N` agree when they agree on both tensor inclusions. -/
private theorem tensor_hom_ext {M N : Type u} [CommRing M] [CommRing N] [Algebra B M]
    [Algebra B N] {T : CommAlgCat.{u} B} {f g : CommAlgCat.of B (M ⊗[B] N) ⟶ T}
    (h₁ : (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :
        CommAlgCat.of B M ⟶ CommAlgCat.of B (M ⊗[B] N)) ≫ f =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft ≫ g)
    (h₂ : (ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :
        CommAlgCat.of B N ⟶ CommAlgCat.of B (M ⊗[B] N)) ≫ f =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeRight ≫ g) : f = g :=
  CommAlgCat.hom_ext
    (Algebra.TensorProduct.ext (congrArg CommAlgCat.Hom.hom h₁) (congrArg CommAlgCat.Hom.hom h₂))

/-! ### Degree zero -/

/-- The retraction of the unique Čech coprojection in degree `0`. -/
noncomputable def cechDegZeroBwd :
    (algebraArrow B C).cechConerve.obj (.mk 0) ⟶ (algebraArrow B C).right :=
  WidePushout.desc (arrows := cechLegs (algebraArrow B C) (.mk 0)) (algebraArrow B C).hom
    (fun _ => 𝟙 _) (fun _ => by simp)

/-- **The degree-`0` part of the Čech conerve of `B ⟶ C` is `C`.** There is only one
coprojection, and it is an isomorphism. -/
noncomputable def cechDegZeroIso :
    (algebraArrow B C).cechConerve.obj (.mk 0) ≅ (algebraArrow B C).right where
  hom := cechDegZeroBwd B C
  inv := cechι (f := algebraArrow B C) (.mk 0) 0
  hom_inv_id := by
    apply cech_hom_ext (f := algebraArrow B C)
    intro i
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    rw [← Category.assoc, Category.comp_id,
      show cechι (f := algebraArrow B C) (.mk 0) 0 ≫ cechDegZeroBwd B C = 𝟙 _ from
        WidePushout.ι_desc _ _ _ _ 0, Category.id_comp]
  inv_hom_id := WidePushout.ι_desc _ _ _ _ 0

/-! ### Degree one -/

/-- `C ⊗[B] C`, as a commutative `B`-algebra. -/
noncomputable abbrev cechSquare : CommAlgCat.{u} B := CommAlgCat.of B (C ⊗[B] C)

/-- The comparison `(C/B)₁ ⟶ C ⊗[B] C`, carrying the two coprojections to the two tensor
inclusions. -/
noncomputable def cechDegOneFwd :
    (algebraArrow B C).cechConerve.obj (.mk 1) ⟶ cechSquare B C :=
  WidePushout.desc (arrows := cechLegs (algebraArrow B C) (.mk 1))
    (ConcreteCategory.ofHom (Algebra.ofId B _))
    (fun i => i.cases (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft)
      (fun _ => ConcreteCategory.ofHom Algebra.TensorProduct.includeRight))
    (fun _ => algebraArrow_left_hom_ext B C _ _)

/-- The comparison `C ⊗[B] C ⟶ (C/B)₁`, inverse to `cechDegOneFwd`. -/
noncomputable def cechDegOneBwd :
    cechSquare B C ⟶ (algebraArrow B C).cechConerve.obj (.mk 1) :=
  ConcreteCategory.ofHom (Algebra.TensorProduct.lift
    (cechι (f := algebraArrow B C) (.mk 1) 0).hom
    (cechι (f := algebraArrow B C) (.mk 1) 1).hom (fun _ _ => Commute.all _ _))

/-- `cechDegOneFwd` carries the zeroth Čech coprojection in degree `1` to `c ↦ c ⊗ 1`. -/
@[simp]
lemma cechι_zero_comp_cechDegOneFwd :
    cechι (f := algebraArrow B C) (.mk 1) 0 ≫ cechDegOneFwd B C =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :=
  WidePushout.ι_desc _ _ _ _ 0

/-- `cechDegOneFwd` carries the first Čech coprojection in degree `1` to `c ↦ 1 ⊗ c`. -/
@[simp]
lemma cechι_one_comp_cechDegOneFwd :
    cechι (f := algebraArrow B C) (.mk 1) 1 ≫ cechDegOneFwd B C =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :=
  WidePushout.ι_desc _ _ _ _ 1

/-- `cechDegOneBwd` carries `c ↦ c ⊗ 1` to the zeroth Čech coprojection in degree `1`. -/
@[simp]
lemma includeLeft_comp_cechDegOneBwd :
    (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :
        CommAlgCat.of B C ⟶ cechSquare B C) ≫ cechDegOneBwd B C =
      cechι (f := algebraArrow B C) (.mk 1) 0 :=
  CommAlgCat.hom_ext
    (Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _))

/-- `cechDegOneBwd` carries `c ↦ 1 ⊗ c` to the first Čech coprojection in degree `1`. -/
@[simp]
lemma includeRight_comp_cechDegOneBwd :
    (ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :
        CommAlgCat.of B C ⟶ cechSquare B C) ≫ cechDegOneBwd B C =
      cechι (f := algebraArrow B C) (.mk 1) 1 :=
  CommAlgCat.hom_ext
    (Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _))

/-- **The degree-`1` part of the Čech conerve of `B ⟶ C` is `C ⊗[B] C`.** -/
noncomputable def cechDegOneIso :
    (algebraArrow B C).cechConerve.obj (.mk 1) ≅ cechSquare B C where
  hom := cechDegOneFwd B C
  inv := cechDegOneBwd B C
  hom_inv_id := by
    apply cech_hom_ext (f := algebraArrow B C)
    intro i
    rw [← Category.assoc, Category.comp_id]
    induction i using Fin.cases with
    | zero => rw [cechι_zero_comp_cechDegOneFwd, includeLeft_comp_cechDegOneBwd]
    | succ j =>
      obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      rw [show (0 : Fin 1).succ = (1 : Fin 2) from rfl,
        cechι_one_comp_cechDegOneFwd, includeRight_comp_cechDegOneBwd]
  inv_hom_id := by
    refine CommAlgCat.hom_ext (Algebra.TensorProduct.ext ?_ ?_)
    · have h : (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :
          CommAlgCat.of B C ⟶ cechSquare B C) ≫ cechDegOneBwd B C ≫ cechDegOneFwd B C =
            ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft := by
        rw [← Category.assoc, includeLeft_comp_cechDegOneBwd, cechι_zero_comp_cechDegOneFwd]
      exact congrArg CommAlgCat.Hom.hom h
    · have h : (ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :
          CommAlgCat.of B C ⟶ cechSquare B C) ≫ cechDegOneBwd B C ≫ cechDegOneFwd B C =
            ConcreteCategory.ofHom Algebra.TensorProduct.includeRight := by
        rw [← Category.assoc, includeRight_comp_cechDegOneBwd, cechι_one_comp_cechDegOneFwd]
      exact congrArg CommAlgCat.Hom.hom h

/-! ### Degree two -/

/-- `C ⊗[B] C ⊗[B] C`, as a commutative `B`-algebra. -/
noncomputable abbrev cechCube : CommAlgCat.{u} B := CommAlgCat.of B (C ⊗[B] (C ⊗[B] C))

/-- The comparison `(C/B)₂ ⟶ C ⊗[B] C ⊗[B] C`, carrying the three coprojections to the three
tensor positions. -/
noncomputable def cechDegTwoFwd :
    (algebraArrow B C).cechConerve.obj (.mk 2) ⟶ cechCube B C :=
  WidePushout.desc (arrows := cechLegs (algebraArrow B C) (.mk 2))
    (ConcreteCategory.ofHom (Algebra.ofId B _))
    (fun i => i.cases (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft)
      (fun j => j.cases
        ((ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :
            CommAlgCat.of B C ⟶ cechSquare B C) ≫
          ConcreteCategory.ofHom Algebra.TensorProduct.includeRight)
        (fun _ => (ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :
            CommAlgCat.of B C ⟶ cechSquare B C) ≫
          ConcreteCategory.ofHom Algebra.TensorProduct.includeRight)))
    (fun _ => algebraArrow_left_hom_ext B C _ _)

/-- The comparison `C ⊗[B] C ⟶ (C/B)₂` onto the last two tensor positions. -/
noncomputable def cechDegTwoTail :
    cechSquare B C ⟶ (algebraArrow B C).cechConerve.obj (.mk 2) :=
  ConcreteCategory.ofHom (Algebra.TensorProduct.lift
    (cechι (f := algebraArrow B C) (.mk 2) 1).hom
    (cechι (f := algebraArrow B C) (.mk 2) 2).hom (fun _ _ => Commute.all _ _))

/-- The comparison `C ⊗[B] C ⊗[B] C ⟶ (C/B)₂`, inverse to `cechDegTwoFwd`. -/
noncomputable def cechDegTwoBwd :
    cechCube B C ⟶ (algebraArrow B C).cechConerve.obj (.mk 2) :=
  ConcreteCategory.ofHom (Algebra.TensorProduct.lift
    (cechι (f := algebraArrow B C) (.mk 2) 0).hom (cechDegTwoTail B C).hom
    (fun _ _ => Commute.all _ _))

/-- `cechDegTwoFwd` carries the zeroth Čech coprojection in degree `2` to `c ↦ c ⊗ 1 ⊗ 1`. -/
@[simp]
lemma cechι_zero_comp_cechDegTwoFwd :
    cechι (f := algebraArrow B C) (.mk 2) 0 ≫ cechDegTwoFwd B C =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :=
  WidePushout.ι_desc _ _ _ _ 0

/-- `cechDegTwoFwd` carries the first Čech coprojection in degree `2` to `c ↦ 1 ⊗ c ⊗ 1`. -/
@[simp]
lemma cechι_one_comp_cechDegTwoFwd :
    cechι (f := algebraArrow B C) (.mk 2) 1 ≫ cechDegTwoFwd B C =
      (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :
          CommAlgCat.of B C ⟶ cechSquare B C) ≫
        ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :=
  WidePushout.ι_desc _ _ _ _ 1

/-- `cechDegTwoFwd` carries the second Čech coprojection in degree `2` to `c ↦ 1 ⊗ 1 ⊗ c`. -/
@[simp]
lemma cechι_two_comp_cechDegTwoFwd :
    cechι (f := algebraArrow B C) (.mk 2) 2 ≫ cechDegTwoFwd B C =
      (ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :
          CommAlgCat.of B C ⟶ cechSquare B C) ≫
        ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :=
  WidePushout.ι_desc _ _ _ _ 2

/-- `cechDegTwoTail` carries `c ↦ c ⊗ 1` to the first Čech coprojection in degree `2`. -/
@[simp]
lemma includeLeft_comp_cechDegTwoTail :
    (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :
        CommAlgCat.of B C ⟶ cechSquare B C) ≫ cechDegTwoTail B C =
      cechι (f := algebraArrow B C) (.mk 2) 1 :=
  CommAlgCat.hom_ext
    (Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _))

/-- `cechDegTwoTail` carries `c ↦ 1 ⊗ c` to the second Čech coprojection in degree `2`. -/
@[simp]
lemma includeRight_comp_cechDegTwoTail :
    (ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :
        CommAlgCat.of B C ⟶ cechSquare B C) ≫ cechDegTwoTail B C =
      cechι (f := algebraArrow B C) (.mk 2) 2 :=
  CommAlgCat.hom_ext
    (Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _))

/-- `cechDegTwoBwd` carries `c ↦ c ⊗ 1 ⊗ 1` to the zeroth Čech coprojection in degree `2`. -/
@[simp]
lemma includeLeft_comp_cechDegTwoBwd :
    (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :
        CommAlgCat.of B C ⟶ cechCube B C) ≫ cechDegTwoBwd B C =
      cechι (f := algebraArrow B C) (.mk 2) 0 :=
  CommAlgCat.hom_ext
    (Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _))

/-- `cechDegTwoBwd` restricted along `c ⊗ c' ↦ 1 ⊗ c ⊗ c'` is `cechDegTwoTail`. -/
@[simp]
lemma includeRight_comp_cechDegTwoBwd :
    (ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :
        cechSquare B C ⟶ cechCube B C) ≫ cechDegTwoBwd B C = cechDegTwoTail B C :=
  CommAlgCat.hom_ext
    (Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _))

/-- The composite of `cechDegTwoTail` with `cechDegTwoFwd` is `c ⊗ c' ↦ 1 ⊗ c ⊗ c'`. -/
lemma cechDegTwoTail_comp_cechDegTwoFwd :
    cechDegTwoTail B C ≫ cechDegTwoFwd B C =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeRight := by
  refine tensor_hom_ext B ?_ ?_ <;> rw [← Category.assoc]
  · rw [includeLeft_comp_cechDegTwoTail, cechι_one_comp_cechDegTwoFwd]
  · rw [includeRight_comp_cechDegTwoTail, cechι_two_comp_cechDegTwoFwd]

/-- **The degree-`2` part of the Čech conerve of `B ⟶ C` is `C ⊗[B] C ⊗[B] C`.** -/
noncomputable def cechDegTwoIso :
    (algebraArrow B C).cechConerve.obj (.mk 2) ≅ cechCube B C where
  hom := cechDegTwoFwd B C
  inv := cechDegTwoBwd B C
  hom_inv_id := by
    apply cech_hom_ext (f := algebraArrow B C)
    intro i
    rw [← Category.assoc, Category.comp_id]
    induction i using Fin.cases with
    | zero => rw [cechι_zero_comp_cechDegTwoFwd, includeLeft_comp_cechDegTwoBwd]
    | succ j =>
      induction j using Fin.cases with
      | zero =>
        rw [show (0 : Fin 2).succ = (1 : Fin 3) from rfl, cechι_one_comp_cechDegTwoFwd,
          Category.assoc, includeRight_comp_cechDegTwoBwd, includeLeft_comp_cechDegTwoTail]
      | succ k =>
        obtain rfl : k = 0 := Fin.fin_one_eq_zero k
        rw [show ((0 : Fin 1).succ).succ = (2 : Fin 3) from rfl,
          cechι_two_comp_cechDegTwoFwd, Category.assoc, includeRight_comp_cechDegTwoBwd,
          includeRight_comp_cechDegTwoTail]
  inv_hom_id := by
    refine CommAlgCat.hom_ext (Algebra.TensorProduct.ext ?_ ?_)
    · have h : (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :
          CommAlgCat.of B C ⟶ cechCube B C) ≫ cechDegTwoBwd B C ≫ cechDegTwoFwd B C =
            ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft := by
        rw [← Category.assoc, includeLeft_comp_cechDegTwoBwd, cechι_zero_comp_cechDegTwoFwd]
      exact congrArg CommAlgCat.Hom.hom h
    · have h : (ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :
          cechSquare B C ⟶ cechCube B C) ≫ cechDegTwoBwd B C ≫ cechDegTwoFwd B C =
            ConcreteCategory.ofHom Algebra.TensorProduct.includeRight := by
        rw [← Category.assoc, includeRight_comp_cechDegTwoBwd,
          cechDegTwoTail_comp_cechDegTwoFwd]
      exact congrArg CommAlgCat.Hom.hom h

/-! ### The coface maps under the identifications -/

/-- The zeroth coface map `(C/B)₀ ⟶ (C/B)₁` is `c ↦ 1 ⊗ c`. -/
lemma cechDegZeroIso_inv_comp_map_delta_zero :
    (cechDegZeroIso B C).inv ≫
        (algebraArrow B C).cechConerve.map (SimplexCategory.δ (0 : Fin 2)) ≫
        cechDegOneFwd B C =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeRight := by
  rw [← Category.assoc]
  change cechι (f := algebraArrow B C) (.mk 0) 0 ≫
    (algebraArrow B C).cechConerve.map (SimplexCategory.δ (0 : Fin 2)) ≫ _ = _
  rw [← Category.assoc, cechι_comp_map, delta_zero_toOrderHom,
    show (0 : Fin 1).succ = (1 : Fin 2) from rfl, cechι_one_comp_cechDegOneFwd]

/-- The first coface map `(C/B)₀ ⟶ (C/B)₁` is `c ↦ c ⊗ 1`. -/
lemma cechDegZeroIso_inv_comp_map_delta_one :
    (cechDegZeroIso B C).inv ≫
        (algebraArrow B C).cechConerve.map (SimplexCategory.δ (1 : Fin 2)) ≫
        cechDegOneFwd B C =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft := by
  rw [← Category.assoc]
  change cechι (f := algebraArrow B C) (.mk 0) 0 ≫
    (algebraArrow B C).cechConerve.map (SimplexCategory.δ (1 : Fin 2)) ≫ _ = _
  rw [← Category.assoc, cechι_comp_map,
    delta_toOrderHom_of_castSucc_lt 1 0 (by decide), Fin.castSucc_zero,
    cechι_zero_comp_cechDegOneFwd]

/-- The zeroth coface map `(C/B)₁ ⟶ (C/B)₂` is `c ⊗ c' ↦ 1 ⊗ c ⊗ c'`. -/
lemma cechDegOneBwd_comp_map_delta_zero :
    cechDegOneBwd B C ≫
        (algebraArrow B C).cechConerve.map (SimplexCategory.δ (0 : Fin 3)) ≫
        cechDegTwoFwd B C =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeRight := by
  refine tensor_hom_ext B ?_ ?_ <;> rw [← Category.assoc]
  · rw [includeLeft_comp_cechDegOneBwd, ← Category.assoc, cechι_comp_map, delta_zero_toOrderHom,
      show (0 : Fin 2).succ = (1 : Fin 3) from rfl, cechι_one_comp_cechDegTwoFwd]
  · rw [includeRight_comp_cechDegOneBwd, ← Category.assoc, cechι_comp_map, delta_zero_toOrderHom,
      show (1 : Fin 2).succ = (2 : Fin 3) from rfl, cechι_two_comp_cechDegTwoFwd]

/-- The first coface map `(C/B)₁ ⟶ (C/B)₂` is `c ⊗ c' ↦ c ⊗ 1 ⊗ c'`. -/
lemma cechDegOneBwd_comp_map_delta_one :
    cechDegOneBwd B C ≫
        (algebraArrow B C).cechConerve.map (SimplexCategory.δ (1 : Fin 3)) ≫
        cechDegTwoFwd B C =
      (ConcreteCategory.ofHom (Algebra.TensorProduct.map (AlgHom.id B C)
        (Algebra.TensorProduct.includeRight : C →ₐ[B] C ⊗[B] C)) :
          cechSquare B C ⟶ cechCube B C) := by
  refine tensor_hom_ext B ?_ ?_ <;> rw [← Category.assoc]
  · rw [includeLeft_comp_cechDegOneBwd, ← Category.assoc, cechι_comp_map,
      delta_toOrderHom_of_castSucc_lt 1 0 (by decide), Fin.castSucc_zero,
      cechι_zero_comp_cechDegTwoFwd]
    exact CommAlgCat.hom_ext
      ((Algebra.TensorProduct.map_comp_includeLeft (AlgHom.id B C) _).trans
        (AlgHom.comp_id _)).symm
  · rw [includeRight_comp_cechDegOneBwd, ← Category.assoc, cechι_comp_map,
      delta_toOrderHom_of_le_castSucc 1 1 (by decide),
      show (1 : Fin 2).succ = (2 : Fin 3) from rfl, cechι_two_comp_cechDegTwoFwd]
    exact CommAlgCat.hom_ext (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id B C) _).symm

/-- The second coface map `(C/B)₁ ⟶ (C/B)₂` is `c ⊗ c' ↦ c ⊗ c' ⊗ 1`. -/
lemma cechDegOneBwd_comp_map_delta_two :
    cechDegOneBwd B C ≫
        (algebraArrow B C).cechConerve.map (SimplexCategory.δ (2 : Fin 3)) ≫
        cechDegTwoFwd B C =
      (ConcreteCategory.ofHom (Algebra.TensorProduct.map (AlgHom.id B C)
        (Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] C)) :
          cechSquare B C ⟶ cechCube B C) := by
  refine tensor_hom_ext B ?_ ?_ <;> rw [← Category.assoc]
  · rw [includeLeft_comp_cechDegOneBwd, ← Category.assoc, cechι_comp_map,
      delta_toOrderHom_of_castSucc_lt 2 0 (by decide), Fin.castSucc_zero,
      cechι_zero_comp_cechDegTwoFwd]
    exact CommAlgCat.hom_ext
      ((Algebra.TensorProduct.map_comp_includeLeft (AlgHom.id B C) _).trans
        (AlgHom.comp_id _)).symm
  · rw [includeRight_comp_cechDegOneBwd, ← Category.assoc, cechι_comp_map,
      delta_toOrderHom_of_castSucc_lt 2 1 (by decide),
      show (1 : Fin 2).castSucc = (1 : Fin 3) from rfl, cechι_one_comp_cechDegTwoFwd]
    exact CommAlgCat.hom_ext (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id B C) _).symm

end Stacks.Descent

end
