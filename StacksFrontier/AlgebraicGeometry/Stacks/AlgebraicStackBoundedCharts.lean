module

public import Mathlib.SetTheory.Cardinal.Free
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSigmaCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
import all StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses

/-!
# An algebraic stack from smooth charts of finite type with boundedly many points

Let `𝒳` be a stack in groupoids over the big fppf site of a scheme `S` with diagonal representable
by algebraic spaces, and let `a i : (Sch/W i) ⟶ 𝒳` be smooth 1-morphisms from schemes `W i`
locally of finite type over `S`, jointly surjective on field objects. If the isomorphism classes
of objects of `𝒳` over the spectra of fields of cardinality at most `size S` are bounded by one
cardinal below the cutoff of the site, then `𝒳` is an algebraic stack.

This is the set-theoretic half of the step "set `W = ∐ W_i`" of the proof of Stacks 0DLN. There the
`W i` are atlases of the restrictions of `𝒳` to the members of an affine open covering of `S`,
and nothing bounds their sizes, so their coproduct need not be a scheme of the site (the cutoff
of the site need not be a regular cardinal). One replaces the family by a subfamily of affine
opens of the `W i`, one for each isomorphism class of field-valued objects realized by them:
each affine open has size at most `size S` (Stacks 04T7), every point of `𝒳` is realized over a
residue field of a point of one of them, hence over a field of cardinality at most `size S`, and
there are fewer than `B.cutoff` such classes.

## Main definitions

* `AlgebraicGeometry.Stack.SmallFieldData`: a maximal ideal of the free commutative ring on a set
  of cardinality `size S`, together with a morphism of the spectrum of its residue field to `S`;
  up to isomorphism these are all the fields of cardinality at most `size S` over `S`.

## Main results

* `AlgebraicGeometry.Stack.mk_smallFieldData_lt`: there are fewer than `B.cutoff` of them.
* `AlgebraicGeometry.Stack.exists_smallFieldRing_quotient_equiv`: every field of cardinality at
  most `size S` is one of them.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_boundedCharts`: the statement above, for a category
  fibred in groupoids at the universes of the site.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_boundedCharts_largeHoms`: the same for a category
  whose morphisms are not small, such as `Complexes_{X/B}` of Stacks 0DLE, through the small
  model of `AlgebraicGeometry.Stack.locallySmall_of_isAlgebraicSpaceIsomPresheaf` and Stacks 03YQ
  in independent universes.

## Implementation notes

The joint surjectivity of the kept subfamily is checked on objects (Stacks 06D4): an object over a
field lifts, after an extension `L` of the field, to an object `x` of some `(Sch/W i)`, i.e. a
morphism `Spec L ⟶ W i`; it lands in an affine open, factors through the residue field of its
image point, and that residue field is identified with a quotient of the free ring. The kept
chart for the resulting class carries an isomorphic object over the same small field, and the
lift through the kept chart is assembled by the cartesian property of the arrows of a category
fibred in groupoids.

## References

* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.Stack

universe u w

section FieldData

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The free commutative ring on a set of cardinality `size S`. Its residue fields at maximal
ideals are, up to isomorphism, all the fields of cardinality at most `size S`. -/
abbrev smallFieldRing : Type u := FreeCommRing S.size.out

/-- **Data of a small field over `S`**: a maximal ideal `m` of `smallFieldRing S` and a morphism
`Spec (smallFieldRing S ⧸ m) ⟶ S`. Every field of cardinality at most `size S` with a morphism of
its spectrum to `S` is isomorphic to one of these. -/
def SmallFieldData : Type u :=
  Σ m : {I : Ideal (smallFieldRing S) // I.IsMaximal},
    Spec (CommRingCat.of (smallFieldRing S ⧸ m.1)) ⟶ S

/-- The free commutative ring `smallFieldRing S` has cardinality at most `size S`. -/
theorem mk_smallFieldRing_le : #(smallFieldRing S) ≤ S.size := by
  rw [mk_freeCommRing, mk_out]
  exact max_le le_rfl S.aleph0_le_size

/-- Every quotient of `smallFieldRing S` has cardinality at most `size S`. -/
theorem mk_quotient_smallFieldRing_le (I : Ideal (smallFieldRing S)) :
    #(smallFieldRing S ⧸ I) ≤ S.size :=
  (mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (mk_smallFieldRing_le S)

/-- The spectrum of a quotient of `smallFieldRing S` has size at most `size S`. -/
theorem size_spec_quotient_smallFieldRing_le (I : Ideal (smallFieldRing S)) :
    (Spec (CommRingCat.of (smallFieldRing S ⧸ I))).size ≤ S.size := by
  rw [Scheme.size_Spec]
  exact max_le S.aleph0_le_size (mk_quotient_smallFieldRing_le S I)

include hS in
/-- The spectrum of the residue field of small field data over `S` is a scheme of the site `B`. -/
theorem contains_spec_smallFieldData (d : SmallFieldData S) :
    B.Contains (Spec (CommRingCat.of (smallFieldRing S ⧸ d.1.1))) :=
  (size_spec_quotient_smallFieldRing_le S d.1.1).trans_lt hS

/-- The object of the big fppf site of `S` named by small field data. -/
def SmallFieldData.obj (d : SmallFieldData S) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_spec_smallFieldData B S hS d) d.2

/-- A scheme has at most `2 ^ #(affine opens)` points: a point is determined by the affine
opens containing it. -/
theorem mk_le_two_power_mk_affineOpens (T : Scheme.{u}) : #T ≤ 2 ^ #T.affineOpens := by
  let m : T → Set T.affineOpens := fun x => {A | x ∈ A.1}
  have hm : Function.Injective m := by
    intro x y h
    apply (T.isBasis_affineOpens.eq_iff).mpr
    rintro _ ⟨A, hA, rfl⟩
    exact Set.ext_iff.mp h ⟨A, hA⟩
  exact (mk_le_of_injective hm).trans mk_set.le

/-- A residue field of a scheme has cardinality at most the size of the scheme. -/
theorem mk_residueField_le_size (T : Scheme.{u}) (x : T) : #(T.residueField x) ≤ T.size := by
  have h := Scheme.size_le_of_mono_quasiCompact (T.fromSpecResidueField x)
  rw [Scheme.size_Spec] at h
  exact (le_max_right _ _).trans h

/-- The morphisms to `S` from the spectrum of a field of cardinality at most `size S` are at most
`2 ^ size S` in number. -/
theorem mk_hom_spec_le_two_pow_size {K : Type u} [Field K] (hK : #K ≤ S.size) :
    #(Spec (CommRingCat.of K) ⟶ S) ≤ 2 ^ S.size := by
  rw [mk_congr (Scheme.SpecToEquivOfField K S), mk_sigma]
  refine (sum_le_sum _ (fun _ => 2 ^ S.size) fun x => ?_).trans ?_
  · refine (mk_le_of_injective (f := fun φ : S.residueField x ⟶ CommRingCat.of K =>
        (⇑φ.hom : S.residueField x → K)) (fun φ ψ h => by ext y; exact congrFun h y)).trans ?_
    rw [mk_arrow, lift_id, lift_id]
    calc #K ^ #(S.residueField x) ≤ S.size ^ #(S.residueField x) := power_le_power_right hK
      _ ≤ S.size ^ S.size :=
          power_le_power_left (aleph0_pos.trans_le S.aleph0_le_size).ne'
            (mk_residueField_le_size S x)
      _ = 2 ^ S.size := power_self_eq S.aleph0_le_size
  · rw [sum_const']
    calc #S * 2 ^ S.size ≤ 2 ^ S.size * 2 ^ S.size :=
          mul_le_mul_left ((mk_le_two_power_mk_affineOpens S).trans
            (power_le_power_left two_ne_zero S.mk_affineOpens_le_size)) _
      _ = 2 ^ S.size := mul_eq_self (S.aleph0_le_size.trans (cantor _).le)

/-- There are at most `2 ^ size S` small field data over `S`. -/
theorem mk_smallFieldData_le : #(SmallFieldData S) ≤ 2 ^ S.size := by
  have hI : #{I : Ideal (smallFieldRing S) // I.IsMaximal} ≤ 2 ^ S.size :=
    (mk_subtype_le _).trans ((mk_le_of_injective (f := fun I : Ideal (smallFieldRing S) =>
      (I : Set (smallFieldRing S))) (fun I J h => SetLike.coe_injective h)).trans
      (mk_set.le.trans (power_le_power_left two_ne_zero (mk_smallFieldRing_le S))))
  rw [SmallFieldData, mk_sigma]
  refine (sum_le_sum _ (fun _ => 2 ^ S.size) fun m => ?_).trans ?_
  · let : m.1.IsMaximal := m.2
    let : Field (smallFieldRing S ⧸ m.1) := Ideal.Quotient.field m.1
    exact mk_hom_spec_le_two_pow_size S (mk_quotient_smallFieldRing_le S m.1)
  · rw [sum_const']
    exact (mul_le_mul_left hI _).trans
      (mul_eq_self (S.aleph0_le_size.trans (cantor _).le)).le

include hS in
/-- There are fewer than `B.cutoff` small field data over a scheme of the site. -/
theorem mk_smallFieldData_lt : #(SmallFieldData S) < B.cutoff :=
  (mk_smallFieldData_le S).trans_lt (B.cutoff_isStrongPrelimit hS)

/-- **Every field of cardinality at most `size S` is a residue field of `smallFieldRing S`.** -/
theorem exists_smallFieldRing_quotient_equiv {K : Type u} [Field K] (hK : #K ≤ S.size) :
    ∃ m : {I : Ideal (smallFieldRing S) // I.IsMaximal},
      Nonempty (smallFieldRing S ⧸ m.1 ≃+* K) := by
  classical
  have hle : #K ≤ #S.size.out := by rwa [mk_out]
  obtain ⟨ι⟩ := hle
  let φ : S.size.out → K := Function.invFun ι
  have hφ : Function.Surjective φ := Function.invFun_surjective ι.injective
  let f : smallFieldRing S →+* K := FreeCommRing.lift φ
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨FreeCommRing.of x, FreeCommRing.lift_of φ x⟩
  exact ⟨⟨RingHom.ker f, RingHom.ker_isMaximal_of_surjective f hf⟩,
    ⟨RingHom.quotientKerEquivOfSurjective hf⟩⟩

end FieldData

section Selection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A type whose cardinality, lifted, is bounded by a cardinal of the lower universe is small. -/
private theorem small_of_lift_mk_le (C : Type (u + 1)) (κ : Cardinal.{u})
    (h : #C ≤ Cardinal.lift.{u + 1} κ) : Small.{u} C := by
  have h' : #C ≤ #(ULift.{u + 1} κ.out) := by rwa [mk_uLift, mk_out]
  obtain ⟨f⟩ := h'
  exact small_of_injective (f.trans Equiv.ulift.toEmbedding).injective

/-- The chart of a family of scheme charts restricted to an affine open of one of them. -/
private theorem isRelativelySmooth_openSubHom
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (T : BigFppfOver B S hS) (A : T.left.obj.Opens) (a : schemeFibredCategory B S hS T ⟶ 𝒳)
    (ha : IsRelativelySmooth B S hS a) :
    IsRelativelySmooth B S hS
      (schemeFibredCategoryMap B S hS (BigFppfOver.openSubHom B S hS T A) ≫ a) := by
  refine isRelativelySmooth_comp B S hS _ a
    ⟨isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS _,
      hasRelativeProperty_schemeFibredCategoryMap B S hS
        (Space.smoothMorphismProperty B S hS) _ ?_⟩ ha
  apply Space.isSmooth_yoneda_map
  show Smooth A.ι
  infer_instance

/-- An affine open of a scheme locally of finite type over `S` has size at most that of `S`. -/
private theorem size_openSubObj_le (T : BigFppfOver B S hS)
    (hT : LocallyOfFiniteType (B.inclusion.map T.hom)) (A : T.left.obj.affineOpens) :
    (A.1 : Scheme.{u}).size ≤ S.size := by
  have : IsAffine (A.1 : Scheme.{u}) := A.2
  have : LocallyOfFiniteType (A.1.ι ≫ B.inclusion.map T.hom) := inferInstance
  exact Scheme.size_le_of_locallyOfFiniteType (A.1.ι ≫ B.inclusion.map T.hom)

/-- **An algebraic stack from smooth charts locally of finite type, with boundedly many points.**
Let `𝒳` be a stack in groupoids over the big fppf site of `S` with diagonal representable by
algebraic spaces, and let `a i : (Sch/W i) ⟶ 𝒳` be smooth 1-morphisms, jointly surjective on
field objects, from schemes `W i` locally of finite type over `S`. Suppose the isomorphism classes
of objects of `𝒳` over the spectrum of any field of cardinality at most `size S` are bounded by a
single cardinal below the cutoff of the site. Then `𝒳` is an algebraic stack.

No bound on the sizes of the `W i` or on their number is assumed: one affine open of one of the
`W i` is kept for each isomorphism class of field-valued objects of cardinality at most `size S`
that the affine opens realize, and the coproduct of those is in the site
(`AlgebraicGeometry.Stack.isAlgebraicStack_of_sigmaCharts`). -/
theorem isAlgebraicStack_of_boundedCharts
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (hstack : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    {ι : Type u} (W : ι → BigFppfOver B S hS) (a : ∀ i, schemeFibredCategory B S hS (W i) ⟶ 𝒳)
    (hsmooth : ∀ i, IsRelativelySmooth B S hS (a i))
    (hlft : ∀ i, LocallyOfFiniteType (B.inclusion.map (W i).hom))
    (hsurj : ∀ (U : BigFppfOver B S hS), IsFieldObject B S hS U →
      ∀ (y : 𝒳.val.obj), 𝒳.val.p.obj y = U →
        ∃ (i : ι) (V : BigFppfOver B S hS), IsFieldObject B S hS V ∧
          ∃ (f : V ⟶ U) (x : (schemeFibredCategory B S hS (W i)).val.obj),
            (schemeFibredCategory B S hS (W i)).val.p.obj x = V ∧
            ∃ α : (CatFiberedInGroupoids.homFunctor (a i)).obj x ⟶ y, 𝒳.val.p.IsHomLift f α)
    (hsize : ∃ κ : Cardinal.{u}, κ < B.cutoff ∧
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k], U.left.1 = Spec (.of k) →
        #k ≤ S.size →
        Cardinal.lift.{u, u + 1} #(Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber U))) ≤
          Cardinal.lift.{u + 1, u} κ) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.val := by
  classical
  obtain ⟨κ, hκ, hbound⟩ := hsize
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  -- the affine opens of the charts, as charts
  let Rr := Σ i, (W i).left.obj.affineOpens
  let V : Rr → BigFppfOver B S hS := fun r => BigFppfOver.openSubObj B S hS (W r.1) r.2.1
  let incl : ∀ r, V r ⟶ W r.1 := fun r => BigFppfOver.openSubHom B S hS (W r.1) r.2.1
  let b : ∀ r, schemeFibredCategory B S hS (V r) ⟶ 𝒳 := fun r =>
    schemeFibredCategoryMap B S hS (incl r) ≫ a r.1
  let U : SmallFieldData S → BigFppfOver B S hS := SmallFieldData.obj B S hS
  -- the classes of the field-valued points of those charts
  let Q := Σ r : Rr, Σ d : SmallFieldData S, (U d ⟶ V r)
  let C := Σ d : SmallFieldData S, Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber (U d)))
  let cls : Q → C := fun q => ⟨q.2.1, Quotient.mk _
    ⟨(CatFiberedInGroupoids.homFunctor (b q.1)).obj (Over.mk q.2.2),
      Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p (b q.1)) (Over.mk q.2.2)⟩⟩
  let J := Set.range cls
  have hC : #C ≤ Cardinal.lift.{u + 1} (#(SmallFieldData S) * κ) := by
    rw [mk_sigma]
    refine (sum_le_sum _ (fun _ => Cardinal.lift.{u + 1} κ) fun d => ?_).trans ?_
    · let : d.1.1.IsMaximal := d.1.2
      let : Field (smallFieldRing S ⧸ d.1.1) := Ideal.Quotient.field d.1.1
      have h := hbound (U d) (smallFieldRing S ⧸ d.1.1) rfl
        (mk_quotient_smallFieldRing_le S d.1.1)
      rwa [Cardinal.lift_id'.{u, u + 1}] at h
    · rw [sum_const, lift_mul, Cardinal.lift_id'.{u, u + 1}]
  have hJ : #J ≤ Cardinal.lift.{u + 1} (#(SmallFieldData S) * κ) :=
    (mk_le_of_injective Subtype.val_injective).trans hC
  have hcut : #(SmallFieldData S) * κ < B.cutoff :=
    mul_lt_of_lt B.aleph0_lt_cutoff.le (mk_smallFieldData_lt B S hS) hκ
  have : Small.{u} J := small_of_lift_mk_le J _ hJ
  let J' := Shrink.{u} J
  let e : J' ≃ J := (equivShrink J).symm
  let σ : J → Q := fun c => c.2.choose
  have hσ : ∀ c, cls (σ c) = c.1 := fun c => c.2.choose_spec
  let W' : J' → BigFppfOver B S hS := fun j => V (σ (e j)).1
  let a' : ∀ j, schemeFibredCategory B S hS (W' j) ⟶ 𝒳 := fun j => b (σ (e j)).1
  have hsizeV : ∀ r : Rr, ((BigFppfOver.toScheme B S hS).obj (V r)).size ≤ S.size :=
    fun r => size_openSubObj_le B S hS (W r.1) (hlft r.1) r.2
  refine isAlgebraicStack_of_sigmaCharts B S hS hstack hdiag W' a'
    (fun j => isRelativelySmooth_openSubHom B S hS (W (σ (e j)).1.1) (σ (e j)).1.2.1
      (a (σ (e j)).1.1) (hsmooth _)) ?_ ?_
  · intro U0 hU0 y hy
    obtain ⟨i, V0, hV0, f, x, hx, α, hα⟩ := hsurj U0 hU0 y hy
    change x.left = V0 at hx
    subst hx
    obtain ⟨L, hL, ⟨eL⟩⟩ := id hV0
    let : Field L := hL
    let T := BigFppfOver.toScheme B S hS
    -- the point of `W i` named by `x`, and an affine open around it
    let w : (W i).left.obj := T.map x.hom (eL.inv (IsLocalRing.closedPoint L))
    obtain ⟨_, ⟨A, hA, rfl⟩, hwA, -⟩ :=
      (W i).left.obj.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
    let r : Rr := ⟨i, ⟨A, hA⟩⟩
    have : IsOpenImmersion (T.map (incl r)) := by
      show IsOpenImmersion (Scheme.Opens.ι (X := (W i).left.obj) A); infer_instance
    have hrange : Set.range (T.map x.hom) ⊆ Set.range (T.map (incl r)) := by
      rintro _ ⟨z, rfl⟩
      have hz : z = eL.inv (IsLocalRing.closedPoint L) := by
        have h1 : eL.inv (eL.hom z) = z := by
          rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
        rw [← h1, Subsingleton.elim (eL.hom z) (IsLocalRing.closedPoint L)]
      show T.map x.hom z ∈ Set.range (Scheme.Opens.ι (X := (W i).left.obj) A)
      rw [Scheme.Opens.range_ι, hz]
      exact hwA
    let xr : T.obj x.left ⟶ T.obj (V r) :=
      IsOpenImmersion.lift (T.map (incl r)) (T.map x.hom) hrange
    have hxr : xr ≫ T.map (incl r) = T.map x.hom := IsOpenImmersion.lift_fac _ _ hrange
    -- its residue field point and a small field datum realizing it
    let ψ : Spec (CommRingCat.of L) ⟶ T.obj (V r) := eL.inv ≫ xr
    let pt := Scheme.SpecToEquivOfField L (T.obj (V r)) ψ
    have hψ : Spec.map pt.2 ≫ (T.obj (V r)).fromSpecResidueField pt.1 = ψ := by
      have h := (Scheme.SpecToEquivOfField L (T.obj (V r))).symm_apply_apply ψ
      rwa [Scheme.SpecToEquivOfField_symm_apply] at h
    have hK : #((T.obj (V r)).residueField pt.1) ≤ S.size :=
      (mk_residueField_le_size _ pt.1).trans (hsizeV r)
    obtain ⟨m, ⟨e'⟩⟩ := exists_smallFieldRing_quotient_equiv S hK
    let ts : Spec (CommRingCat.of (smallFieldRing S ⧸ m.1)) ⟶ T.obj (V r) :=
      Spec.map (CommRingCat.ofHom e'.symm.toRingHom) ≫
        (T.obj (V r)).fromSpecResidueField pt.1
    let d : SmallFieldData S := ⟨m, ts ≫ B.inclusion.map (V r).hom⟩
    let t : U d ⟶ V r := Over.homMk (ObjectProperty.homMk ts) (by
      apply ObjectProperty.hom_ext
      rfl)
    let gs : T.obj x.left ⟶ Spec (CommRingCat.of (smallFieldRing S ⧸ m.1)) :=
      eL.hom ≫ Spec.map (CommRingCat.ofHom e'.toRingHom ≫ pt.2)
    have hgt : gs ≫ ts = xr := by
      have h1 : Spec.map (CommRingCat.ofHom e'.toRingHom ≫ pt.2) ≫
          Spec.map (CommRingCat.ofHom e'.symm.toRingHom) = Spec.map pt.2 := by
        rw [← Spec.map_comp]
        congr 1
        ext z
        simp
      simp only [gs, ts, Category.assoc]
      rw [reassoc_of% h1, hψ, Iso.hom_inv_id_assoc]
    have hxw : B.inclusion.map x.hom.left ≫ B.inclusion.map (W i).hom =
        B.inclusion.map x.left.hom := by
      rw [← Functor.map_comp, Over.w x.hom]
    have hVhom : B.inclusion.map (V r).hom = T.map (incl r) ≫ B.inclusion.map (W i).hom := rfl
    let g : x.left ⟶ U d := BigFppfOver.homMk B S hS (contains_spec_smallFieldData B S hS d) d.2 gs
      (by
        show gs ≫ ts ≫ B.inclusion.map (V r).hom = _
        rw [← Category.assoc, hgt, hVhom, ← Category.assoc, hxr]
        exact hxw)
    -- the kept chart for the class of `(r, d, t)`
    let q : Q := ⟨r, d, t⟩
    let c : J := ⟨cls q, q, rfl⟩
    let j : J' := (equivShrink J) c
    have hspec : cls (σ (e j)) = cls q := by
      rw [hσ]
      show ((equivShrink J).symm ((equivShrink J) c)).1 = cls q
      rw [Equiv.symm_apply_apply]
    have key : ∀ q' : Q, cls q' = cls q → ∃ V₁ : BigFppfOver B S hS, IsFieldObject B S hS V₁ ∧
        ∃ (f₁ : V₁ ⟶ U0) (x₁ : (schemeFibredCategory B S hS (V q'.1)).val.obj),
          (schemeFibredCategory B S hS (V q'.1)).val.p.obj x₁ = V₁ ∧
          ∃ α₁ : (CatFiberedInGroupoids.homFunctor (b q'.1)).obj x₁ ⟶ y,
            𝒳.val.p.IsHomLift f₁ α₁ := by
      rintro ⟨r', d', t'⟩ hspec
      dsimp only [cls] at hspec
      obtain ⟨hd, hh⟩ := Sigma.mk.inj_iff.mp hspec
      subst hd
      obtain ⟨φ⟩ := Quotient.exact (eq_of_heq hh)
      -- the lift through the kept chart
      refine ⟨x.left, hV0, f, Over.mk (g ≫ t'), rfl, ?_⟩
      let β' := (CatFiberedInGroupoids.homFunctor (b r')).map
        (Over.homMk g rfl : Over.mk (g ≫ t') ⟶ Over.mk t')
      have hβ' : 𝒳.val.p.IsHomLift g β' := by
        have : (schemeFibredCategory B S hS (V r')).val.p.IsHomLift g
            (Over.homMk g rfl : Over.mk (g ≫ t') ⟶ Over.mk t') :=
          IsHomLift.map (Over.forget (V r')) (Over.homMk g rfl : Over.mk (g ≫ t') ⟶ Over.mk t')
        exact BasedFunctor.preserves_isHomLift (b r').hom g _
      have hφ : 𝒳.val.p.IsHomLift (𝟙 (U d)) φ.hom.1 := φ.hom.2
      let γ := β' ≫ φ.hom.1
      have hγ : 𝒳.val.p.IsHomLift g γ := inferInstance
      let β := (CatFiberedInGroupoids.homFunctor (b r)).map
        (Over.homMk g rfl : Over.mk (g ≫ t) ⟶ Over.mk t)
      have hβ : 𝒳.val.p.IsHomLift g β := by
        have : (schemeFibredCategory B S hS (V r)).val.p.IsHomLift g
            (Over.homMk g rfl : Over.mk (g ≫ t) ⟶ Over.mk t) :=
          IsHomLift.map (Over.forget (V r)) (Over.homMk g rfl : Over.mk (g ≫ t) ⟶ Over.mk t)
        exact BasedFunctor.preserves_isHomLift (b r).hom g _
      have hβc : 𝒳.val.p.IsStronglyCartesian g β :=
        𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift g β
      let χ := Functor.IsStronglyCartesian.map 𝒳.val.p g β (g := 𝟙 x.left) (f' := g)
        (Category.id_comp g).symm γ
      have hχ : 𝒳.val.p.IsHomLift (𝟙 x.left) χ := inferInstance
      have hμw : (𝟙 x.left ≫ x.hom : x.left ⟶ W i) = (g ≫ t) ≫ incl r := by
        apply BigFppfOver.map_toScheme_injective B S hS
        show 𝟙 _ ≫ T.map x.hom = (gs ≫ ts) ≫ T.map (incl r)
        rw [Category.id_comp, hgt, hxr]
      let μ : (Over.mk ((g ≫ t) ≫ incl r) : Over (W i)) ⟶ x := Over.homMk (𝟙 x.left) hμw
      let δ := (CatFiberedInGroupoids.homFunctor (a i)).map μ
      have hδ : 𝒳.val.p.IsHomLift (𝟙 x.left) δ := by
        have : (schemeFibredCategory B S hS (W i)).val.p.IsHomLift (𝟙 x.left) μ :=
          IsHomLift.map (Over.forget (W i)) μ
        exact BasedFunctor.preserves_isHomLift (a i).hom (𝟙 x.left) μ
      have hδα : 𝒳.val.p.IsHomLift f (δ ≫ α) := IsHomLift.comp_lift_id_left 𝒳.val.p f α δ
      let χ' : (CatFiberedInGroupoids.homFunctor (b r')).obj (Over.mk (g ≫ t')) ⟶
          (CatFiberedInGroupoids.homFunctor (a i)).obj (Over.mk ((g ≫ t) ≫ incl r)) := χ
      have hχ' : 𝒳.val.p.IsHomLift (𝟙 x.left) χ' := hχ
      exact ⟨χ' ≫ δ ≫ α, IsHomLift.comp_lift_id_left 𝒳.val.p f (δ ≫ α) χ'⟩
    exact ⟨j, key _ hspec⟩
  · -- the coproduct of the kept charts is in the site
    let κ' := max (#(SmallFieldData S) * κ) S.size
    have hκ' : κ' < B.cutoff := max_lt hcut hS
    refine lt_of_le_of_lt (schemeSize_coproduct_le _ κ'
      (S.aleph0_le_size.trans (le_max_right _ _)) ?_ fun j => (hsizeV _).trans (le_max_right _ _))
      hκ'
    have h1 : Cardinal.lift.{u + 1} #J' = #J := by
      have h := Cardinal.lift_mk_eq'.mpr ⟨e⟩
      rwa [Cardinal.lift_id'.{u, u + 1}] at h
    have h2 : Cardinal.lift.{u + 1} #J' ≤ Cardinal.lift.{u + 1} (#(SmallFieldData S) * κ) :=
      h1 ▸ hJ
    exact (Cardinal.lift_le.mp h2).trans (le_max_left _ _)

end Selection


section LargeHoms

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

universe v

/-- **`AlgebraicGeometry.Stack.isAlgebraicStack_of_boundedCharts` for a category whose morphisms
are not small.** The same statement for a category fibred in groupoids over the big fppf site of
`S` whose total category has its morphisms in an arbitrary universe, such as `Complexes_{X/B}` of
Stacks 0DLE. The charts are 1-morphisms `(Sch/W i) ⟶ 𝒳` of based categories, representable by
algebraic spaces and smooth in the sense of the atlas clause of Stacks 026O.

The diagonal being representable by algebraic spaces, the total category is locally small
(`AlgebraicGeometry.Stack.locallySmall_of_isAlgebraicSpaceIsomPresheaf`), so it has a small model
equivalent to it over the site; every hypothesis transports to the small model, and algebraicity
transports back by Stacks 03YQ in independent universes. -/
theorem isAlgebraicStack_of_boundedCharts_largeHoms
    {𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS)}
    (hfib : 𝒳.p.IsFiberedInGroupoids)
    (hstack : 𝒳.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS (CatFiberedInGroupoids.mk 𝒳 hfib))
    {ι : Type u} (W : ι → BigFppfOver B S hS)
    (a : ∀ i, (schemeFibredCategory B S hS (W i)).val ⥤ᵇ 𝒳)
    (hsmooth : ∀ i (V : BigFppfOver B S hS) (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.obj)
      (_hy : y ⋙ 𝒳.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom)
          (schemeFibredCategory B S hS (W i)).val.p 𝒳.p y (a i).toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsSmooth B S hS (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom)
    (hlft : ∀ i, LocallyOfFiniteType (B.inclusion.map (W i).hom))
    (hsurj : ∀ (U : BigFppfOver B S hS), IsFieldObject B S hS U →
      ∀ (y : 𝒳.obj), 𝒳.p.obj y = U →
        ∃ (i : ι) (V : BigFppfOver B S hS), IsFieldObject B S hS V ∧
          ∃ (f : V ⟶ U) (x : (schemeFibredCategory B S hS (W i)).val.obj),
            (schemeFibredCategory B S hS (W i)).val.p.obj x = V ∧
            ∃ α : (a i).obj x ⟶ y, 𝒳.p.IsHomLift f α)
    (hsize : ∃ κ : Cardinal.{u}, κ < B.cutoff ∧
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k], U.left.1 = Spec (.of k) →
        #k ≤ S.size →
        Cardinal.lift.{u, u + 1} #(Quotient (isIsomorphicSetoid (𝒳.p.Fiber U))) ≤
          Cardinal.lift.{u + 1, u} κ) :
    IsAlgebraicStack.{u, w} B S hS 𝒳 := by
  classical
  have : LocallySmall.{u} 𝒳.obj := locallySmall_of_isAlgebraicSpaceIsomPresheaf B S hS
    (CatFiberedInGroupoids.mk 𝒳 hfib)
    ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS _).mp hdiag)
  let e := BasedCategory.shrinkHomsEquivalenceOver 𝒳
  let E : BasedCategory.Equivalence 𝒳 𝒳.shrinkHoms := e.toBasedEquivalence
  have hfibs : (𝒳.shrinkHoms).p.IsFiberedInGroupoids :=
    StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e.symm hfib
  let 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk 𝒳.shrinkHoms hfibs
  have hstack' : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS) :=
    (BasedCategory.isStack_iff_of_equivalence E (BigFppfOver.topology B S hS)).mp hstack
  have h₃ : IsRepresentableFromSchemes B S hS (CatFiberedInGroupoids.mk 𝒳 hfib) :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS _).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS _).mp hdiag)
  have h₃' : IsRepresentableFromSchemes B S hS 𝒴 :=
    isRepresentableFromSchemes_of_equivalenceOver B S hS
      (𝒳 := CatFiberedInGroupoids.mk 𝒳 hfib) (𝒴 := 𝒴) E h₃
  have hdiag' : HasRepresentableDiagonal B S hS 𝒴 :=
    (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).mpr
      ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒴).mpr h₃')
  have hequiv : Functor.IsEquivalence E.functor.toFunctor := E.equiv.isEquivalence_functor
  have hinvE : Functor.IsEquivalence E.inverse.toFunctor := E.symm.equiv.isEquivalence_functor
  let a' : ∀ i, schemeFibredCategory B S hS (W i) ⟶ 𝒴 := fun i =>
    Bicategory.InducedBicategory.mkHom (BasedFunctor.comp (a i) E.functor)
  have hsmooth' : ∀ i, IsRelativelySmooth B S hS (a' i) := by
    intro i
    have hid : Functor.IsEquivalence
        (BasedFunctor.id (schemeFibredCategory B S hS (W i)).val).toFunctor := by
      show Functor.IsEquivalence (𝟭 _)
      infer_instance
    exact ⟨h₃' _ _, relativeProperty_of_equivalences B S hS (Space.smoothMorphismProperty B S hS)
      (𝒳' := schemeFibredCategory B S hS (W i)) (𝒴' := 𝒴)
      (𝒳 := schemeFibredCategory B S hS (W i)) (𝒴 := CatFiberedInGroupoids.mk 𝒳 hfib)
      (BasedFunctor.comp (a i) E.functor) (a i) (BasedFunctor.id _) E.inverse
      (whiskerUnitIsoOver B S hS E (a i)) (hsmooth i)⟩
  refine isAlgebraicStack_of_equivalenceOver B S hS e.symm
    (isAlgebraicStack_of_boundedCharts B S hS hstack' hdiag' W a' hsmooth' hlft ?_ ?_)
  · intro U hU y hy
    obtain ⟨i, V, hV, f, x, hx, α, hα⟩ := hsurj U hU (E.inverse.obj y)
      ((E.inverse.w_obj y).trans hy)
    let c : E.functor.obj (E.inverse.obj y) ⟶ y := E.counitIso.hom.app y
    have hc : 𝒴.val.p.IsHomLift (𝟙 U) c := E.counitIso.hom.isHomLift hy
    exact ⟨i, V, hV, f, x, hx, E.functor.map α ≫ c,
      IsHomLift.comp_lift_id_right 𝒴.val.p f (E.functor.map α) c⟩
  · obtain ⟨κ, hκ, hbound⟩ := hsize
    refine ⟨κ, hκ, fun U k _ hU hk => (le_trans ?_ (hbound U k hU hk))⟩
    -- the isomorphism classes over `U` of the small model inject into those of `𝒳`
    let G := Functor.fiberFunctorOfCompEq E.inverse.w U
    let H := Functor.fiberFunctorOfCompEq E.functor.w U
    let m : Quotient (isIsomorphicSetoid (𝒴.val.p.Fiber U)) →
        Quotient (isIsomorphicSetoid (𝒳.p.Fiber U)) :=
      Quotient.lift (fun z => Quotient.mk _ (G.obj z)) (fun z₁ z₂ ⟨φ⟩ =>
        Quotient.sound ⟨G.mapIso φ⟩)
    have hm : Function.Injective m := by
      intro c₁ c₂ h
      induction c₁ using Quotient.inductionOn with | h z₁ =>
      induction c₂ using Quotient.inductionOn with | h z₂ =>
      obtain ⟨φ⟩ := Quotient.exact h
      let c₁ : z₁.1 ⟶ E.functor.obj (E.inverse.obj z₁.1) := E.counitIso.inv.app z₁.1
      have hc₁ : 𝒴.val.p.IsHomLift (𝟙 U) c₁ := E.counitIso.inv.isHomLift z₁.2
      let c₂ : E.functor.obj (E.inverse.obj z₂.1) ⟶ z₂.1 := E.counitIso.hom.app z₂.1
      have hc₂ : 𝒴.val.p.IsHomLift (𝟙 U) c₂ := E.counitIso.hom.isHomLift z₂.2
      let c₃ : E.functor.obj (E.inverse.obj z₁.1) ⟶ E.functor.obj (E.inverse.obj z₂.1) :=
        Functor.Fiber.fiberInclusion.map (H.map φ.hom)
      have hc₃ : 𝒴.val.p.IsHomLift (𝟙 U) c₃ := (H.map φ.hom).2
      let ψ : z₁.1 ⟶ z₂.1 := c₁ ≫ c₃ ≫ c₂
      have hψ : 𝒴.val.p.IsHomLift (𝟙 U) ψ := by
        have : 𝒴.val.p.IsHomLift (𝟙 U) (c₃ ≫ c₂) := IsHomLift.comp_lift_id_left 𝒴.val.p (𝟙 U) c₂ c₃
        exact IsHomLift.comp_lift_id_left 𝒴.val.p (𝟙 U) (c₃ ≫ c₂) c₁
      exact Quotient.sound ⟨fiberIsoOfHomLift B S hS 𝒴.val.p hfibs U ψ hψ⟩
    rw [Cardinal.lift_le]
    exact mk_le_of_injective hm

end LargeHoms

end AlgebraicGeometry.Stack

end
