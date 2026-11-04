module

public import StacksFrontier.Algebra.Category.CommAlgCat.CoconeOfRingCocone
public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.FlatProjection
public import StacksFrontier.RingTheory.WeaklyEtale.Flat
public import StacksFrontier.RingTheory.Flat.TowerLTensor

@[expose] public section

/-!
# Descent and sources of weakly étale ring maps

For ring maps `A → B → C`, faithful flatness of `B → C` allows flatness of the
multiplication map for `C` over `A` to descend to the multiplication map for `B` over `A`;
consequently, weak étaleness of `A → C` descends to `A → B`. Dually, an algebra map between
two weakly étale algebras over the same base ring is itself weakly étale. Finally,
localizations and étale algebras are weakly étale, as is the apex of a filtered colimit of
weakly étale algebras over a fixed commutative base ring.

## Main definitions

No new definitions are introduced.

## Main results

* `flat_lmul'_and_weaklyEtale_of_faithfullyFlat` (Stacks 092K): faithfully flat descent of
  flatness of the multiplication map and of weak étaleness.
* `weaklyEtale_of_comp` (Stacks 092L): if `A → B` and `A → C` are weakly étale, then a
  compatible map `B → C` is weakly étale.
* `weaklyEtale_of_isLocalization_etale_filteredColimit` (Stacks 092N): records the three
  standard constructions of weakly étale algebras.

## Implementation notes

The composability of the three ring maps is expressed by `IsScalarTower A B C`. Flatness of
the multiplication map `S ⊗[R] S → S` is expressed by
`(Algebra.TensorProduct.lmul' R (S := S)).Flat`.

For the filtered colimit statement, the filtered system is expressed as a functor
`J ⥤ CommAlgCat.{w} A`, with the index category and algebra carriers in universe `w`,
independently of the base ring universe `u`. The explicit `Small.{max u (w + 1)} J` instance
is retained, although redundant here. The first two constructions allow the algebra carrier in
an independent universe `v`. The algebra structures and transition maps are compatible with
the fixed base ring by construction, and the conclusion is independent of a chosen model of
the colimit.

Flatness of the colimit and its multiplication map follow from the equational criterion:
finite families lift to a common stage, where a vanishing relation becomes trivial. The lift of
a finite family and the passage from a colimit of algebras to a colimit of rings are
`AlgebraicGeometry.exists_fin_alg_lift` and
`Stacks.CommAlgCat.isColimit_forgetToCommRing`;
the underlying type cocone is then colimiting because the forgetful functor from commutative
rings to types preserves filtered colimits.

## References

* [Stacks Project, Tag 092K](https://stacks.math.columbia.edu/tag/092K)
* [Stacks Project, Tag 092L](https://stacks.math.columbia.edu/tag/092L)
* [Stacks Project, Tag 092N](https://stacks.math.columbia.edu/tag/092N)
* [Olivier, *Anneaux absolument plats universels et épimorphismes à buts réduits*][Olivier-AF]
-/

universe u v w

section FaithfullyFlatDescent

open TensorProduct LinearMap
open AlgebraTensorModule

private theorem flat_of_flat_of_faithfullyFlat
    (R S M : Type*) [CommRing R] [CommRing S] [CommRing M]
    [Algebra R S] [Algebra S M] [Algebra R M] [IsScalarTower R S M]
    [Module.Flat R M] [Module.FaithfullyFlat S M] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ f hf
  rw [← coe_lTensor (A := S),
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective
      (R := S) (M := M) (f := lTensor S S f),
    ← lTensor_baseChange_injective_iff]
  have : Module.Flat R (M ⊗[S] S) :=
    Module.Flat.of_linearEquiv ((TensorProduct.rid S M).restrictScalars R)
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- Let `A → B → C` be compatible maps of commutative rings and suppose that `C` is
faithfully flat over `B`. Then flatness of the multiplication map `C ⊗[A] C → C` descends
to the multiplication map `B ⊗[A] B → B`; consequently, if `A → C` is weakly étale, then
`A → B` is weakly étale. -/
@[stacks 092K]
theorem flat_lmul'_and_weaklyEtale_of_faithfullyFlat
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.FaithfullyFlat B C] :
    ((Algebra.TensorProduct.lmul' A (S := C)).Flat →
      (Algebra.TensorProduct.lmul' A (S := B)).Flat) ∧
    (Algebra.WeaklyEtale A C → Algebra.WeaklyEtale A B) := by
  have hBC : (algebraMap B C).Flat :=
    RingHom.flat_algebraMap_iff.mpr Module.FaithfullyFlat.toFlat
  let f : B →ₐ[A] C := IsScalarTower.toAlgHom A B C
  let q : B ⊗[A] B →ₐ[A] C ⊗[A] C := Algebra.TensorProduct.map f f
  have hq : q.Flat := hBC.tensorProductMap hBC
  have heq : (Algebra.TensorProduct.lmul' A (S := C)).comp q =
      f.comp (Algebra.TensorProduct.lmul' A (S := B)) := by
    ext <;> simp [q, f]
  have first (hC : (Algebra.TensorProduct.lmul' A (S := C)).Flat) :
      (Algebra.TensorProduct.lmul' A (S := B)).Flat := by
    have hcomp : (f.comp (Algebra.TensorProduct.lmul' A (S := B))).Flat := by
      rw [← heq]
      exact hq.comp hC
    let : Algebra (B ⊗[A] B) B :=
      (Algebra.TensorProduct.lmul' A (S := B)).toRingHom.toAlgebra
    let : Algebra (B ⊗[A] B) C :=
      ((algebraMap B C).comp
        (Algebra.TensorProduct.lmul' A (S := B)).toRingHom).toAlgebra
    let : IsScalarTower (B ⊗[A] B) B C :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    apply RingHom.flat_algebraMap_iff.mp
    have : Module.Flat (B ⊗[A] B) C := by
      rw [← RingHom.flat_algebraMap_iff]
      exact hcomp
    exact flat_of_flat_of_faithfullyFlat (B ⊗[A] B) B C
  refine ⟨first, fun hC ↦ ?_⟩
  let _ : Algebra.WeaklyEtale A C := hC
  exact ⟨flat_of_flat_of_faithfullyFlat A B C,
    first (Algebra.WeaklyEtale.flat_lmul' A C)⟩

end FaithfullyFlatDescent

section BetweenWeaklyEtale

open scoped TensorProduct

/-- If `A → B` and `A → C` are weakly étale, then a compatible algebra map `B → C`
is weakly étale. -/
@[stacks 092L]
theorem weaklyEtale_of_comp (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : Algebra.WeaklyEtale A B) (hAC : Algebra.WeaklyEtale A C) :
    Algebra.WeaklyEtale B C := by
  constructor
  · exact flat_of_flat_of_mul_flat A B (Algebra.WeaklyEtale.flat_lmul' A B) C
      (Algebra.WeaklyEtale.flat (R := A) (S := C))
  · let X := C ⊗[A] C
    let Y := C ⊗[B] C
    let f : X →ₐ[A] Y := Algebra.TensorProduct.mapOfCompatibleSMul B A A C C
    let algXY : Algebra X Y := f.toRingHom.toAlgebra
    let : SMul X Y := algXY.toSMul
    let : Module X Y := algXY.toModule
    let algYC : Algebra Y C :=
      (Algebra.TensorProduct.lmul' B (S := C)).toRingHom.toAlgebra
    let : SMul Y C := algYC.toSMul
    let : Module Y C := algYC.toModule
    let algXC : Algebra X C :=
      (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.toAlgebra
    let : SMul X C := algXC.toSMul
    let : Module X C := algXC.toModule
    let : IsScalarTower X Y C := .of_algebraMap_eq' (by
      show (Algebra.TensorProduct.lmul' A (S := C)).toRingHom =
        (Algebra.TensorProduct.lmul' B (S := C)).toRingHom.comp f.toRingHom
      ext x <;>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lmul'_apply_tmul,
          mul_one, one_mul, f] <;>
        rw [Algebra.TensorProduct.mapOfCompatibleSMul_tmul] <;> simp)
    have hf : Function.Surjective (algebraMap X Y) := by
      show Function.Surjective f
      exact Algebra.TensorProduct.mapOfCompatibleSMul_surjective B A A C C
    have hmul : (Algebra.TensorProduct.lmul' X (S := Y)).Flat := by
      exact RingHom.Flat.of_bijective (LinearMap.mul'_bijective_of_surjective X Y hf)
    exact flat_of_flat_of_mul_flat X Y hmul C
      (Algebra.WeaklyEtale.flat_lmul' A C)

end BetweenWeaklyEtale

section Sources

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

private abbrev tensorMap {A : Type u} [CommRing A]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{w} A} (c : Cocone F) (j : J) :
    (F.obj j ⊗[A] F.obj j) →ₐ[A] (c.pt ⊗[A] c.pt) :=
  Algebra.TensorProduct.map (c.ι.app j).hom (c.ι.app j).hom

private abbrev tensorTransition {A : Type u} [CommRing A]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{w} A) {j k : J} (g : j ⟶ k) :
    (F.obj j ⊗[A] F.obj j) →ₐ[A] (F.obj k ⊗[A] F.obj k) :=
  Algebra.TensorProduct.map (F.map g).hom (F.map g).hom

/-- A cocone leg composed with a transition map is the cocone leg of the source. -/
private lemma hom_map_hom_apply {A : Type u} [CommRing A]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{w} A} (c : Cocone F) {j k : J} (g : j ⟶ k) (a : F.obj j) :
    (c.ι.app k).hom ((F.map g).hom a) = (c.ι.app j).hom a :=
  congrArg (fun h : (F.obj j) →ₐ[A] c.pt => h a) (congrArg CommAlgCat.Hom.hom (c.w g))

private lemma tensorMap_transition {A : Type u} [CommRing A]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{w} A} (c : Cocone F) {j k : J} (g : j ⟶ k)
    (z : F.obj j ⊗[A] F.obj j) :
    tensorMap c k (tensorTransition F g z) = tensorMap c j z := by
  have heq : (c.ι.app k).hom.comp (F.map g).hom = (c.ι.app j).hom :=
    AlgHom.ext (hom_map_hom_apply c g)
  show ((Algebra.TensorProduct.map (c.ι.app k).hom (c.ι.app k).hom).comp
    (Algebra.TensorProduct.map (F.map g).hom (F.map g).hom)) z = _
  rw [← Algebra.TensorProduct.map_comp, heq]

private lemma exists_tensor_lift {A : Type u} [CommRing A]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{w} A} {c : Cocone F} (hc : IsColimit c)
    (z : c.pt ⊗[A] c.pt) :
    ∃ (j : J) (y : F.obj j ⊗[A] F.obj j), tensorMap c j y = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨IsFiltered.nonempty.some, 0, map_zero _⟩
  | tmul x y =>
      obtain ⟨j, a, ha⟩ := AlgebraicGeometry.exists_lift_of_isColimit hc x
      obtain ⟨k, b, hb⟩ := AlgebraicGeometry.exists_lift_of_isColimit hc y
      let m := IsFiltered.max j k
      let fj := IsFiltered.leftToMax j k
      let fk := IsFiltered.rightToMax j k
      refine ⟨m, (F.map fj).hom a ⊗ₜ[A] (F.map fk).hom b, ?_⟩
      simp only [tensorMap, Algebra.TensorProduct.map_tmul]
      rw [hom_map_hom_apply, hom_map_hom_apply]
      exact congrArg₂ (fun a b => a ⊗ₜ[A] b) ha hb
  | add x y hx hy =>
      obtain ⟨j, a, ha⟩ := hx
      obtain ⟨k, b, hb⟩ := hy
      let m := IsFiltered.max j k
      let fj := IsFiltered.leftToMax j k
      let fk := IsFiltered.rightToMax j k
      refine ⟨m, tensorTransition F fj a + tensorTransition F fk b, ?_⟩
      rw [map_add, tensorMap_transition, tensorMap_transition, ha, hb]

private lemma exists_fin_tensor_lift {A : Type u} [CommRing A]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{w} A} {c : Cocone F} (hc : IsColimit c)
    {n : ℕ} (z : Fin n → c.pt ⊗[A] c.pt) :
    ∃ (j : J) (y : Fin n → F.obj j ⊗[A] F.obj j),
      ∀ i, tensorMap c j (y i) = z i := by
  induction n with
  | zero => exact ⟨IsFiltered.nonempty.some, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨j, y, hy⟩ := ih (fun i ↦ z i.castSucc)
      obtain ⟨k, t, ht⟩ := exists_tensor_lift hc (z (Fin.last n))
      let m := IsFiltered.max j k
      let fj := IsFiltered.leftToMax j k
      let fk := IsFiltered.rightToMax j k
      refine ⟨m, Fin.lastCases (tensorTransition F fk t)
        (fun i ↦ tensorTransition F fj (y i)), ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun q ↦ ?_) i
      · simpa using (tensorMap_transition c fk t).trans ht
      · simpa using (tensorMap_transition c fj (y q)).trans (hy q)

private lemma lmul_map {A : Type u} [CommRing A]
    {S : Type v} [CommRing S] [Algebra A S]
    {T : Type w} [CommRing T] [Algebra A T]
    (h : S →ₐ[A] T) (z : S ⊗[A] S) :
    h ((Algebra.TensorProduct.lmul' A) z) =
      (Algebra.TensorProduct.lmul' A)
        ((Algebra.TensorProduct.map h h) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.lmul'_apply_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma flat_lmul_of_isColimit {A : Type u} [CommRing A]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{w} A) (c : Cocone F) (hc : IsColimit c)
    (hcD : IsColimit ((forget (CommAlgCat A)).mapCocone c))
    (hF : ∀ j, Algebra.WeaklyEtale A (F.obj j)) :
    (Algebra.TensorProduct.lmul' A (S := c.pt)).Flat := by
  let D : J ⥤ Type w := F ⋙ forget (CommAlgCat A)
  let cD : Cocone D := (forget (CommAlgCat A)).mapCocone c
  let L := Algebra.TensorProduct.lmul' A (S := c.pt)
  let : Algebra (c.pt ⊗[A] c.pt) c.pt := L.toRingHom.toAlgebra
  show Module.Flat (c.pt ⊗[A] c.pt) c.pt
  apply Module.Flat.of_forall_isTrivialRelation
  intro n f x hx
  change ∑ i, L (f i) * x i = 0 at hx
  obtain ⟨j, a, ha⟩ := exists_fin_tensor_lift hc f
  obtain ⟨k, y, hy⟩ := AlgebraicGeometry.exists_fin_alg_lift hc x
  let m := IsFiltered.max j k
  let fj : j ⟶ m := IsFiltered.leftToMax j k
  let fk : k ⟶ m := IsFiltered.rightToMax j k
  let a' : Fin n → F.obj m ⊗[A] F.obj m := fun i ↦ tensorTransition F fj (a i)
  let y' : Fin n → F.obj m := fun i ↦ (F.map fk).hom (y i)
  have ha' : ∀ i, tensorMap c m (a' i) = f i := fun i ↦
    (tensorMap_transition c fj (a i)).trans (ha i)
  have hy' : ∀ i, (c.ι.app m).hom (y' i) = x i := fun i ↦
    (hom_map_hom_apply c fk (y i)).trans (hy i)
  let r : F.obj m := ∑ i, (Algebra.TensorProduct.lmul' A) (a' i) * y' i
  have hr : (c.ι.app m).hom r = 0 := by
    calc
      (c.ι.app m).hom r =
          ∑ i, (c.ι.app m).hom ((Algebra.TensorProduct.lmul' A) (a' i)) *
            (c.ι.app m).hom (y' i) := by simp [r]
      _ = ∑ i, L (f i) * x i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [lmul_map, ha' i, hy' i]
      _ = 0 := hx
  have hr' := (Types.FilteredColimit.isColimit_eq_iff' hcD r (0 : F.obj m)).mp (by
    show (c.ι.app m).hom r = (c.ι.app m).hom 0
    simpa only [map_zero] using hr)
  obtain ⟨l, g, hg⟩ := hr'
  let a'' : Fin n → F.obj l ⊗[A] F.obj l :=
    fun i ↦ tensorTransition F g (a' i)
  let y'' : Fin n → F.obj l := fun i ↦ (F.map g).hom (y' i)
  have ha'' : ∀ i, tensorMap c l (a'' i) = f i := fun i ↦
    (tensorMap_transition c g (a' i)).trans (ha' i)
  have hy'' : ∀ i, (c.ι.app l).hom (y'' i) = x i := fun i ↦
    (hom_map_hom_apply c g (y' i)).trans (hy' i)
  have hg' : ∑ i, (Algebra.TensorProduct.lmul' A) (a'' i) * y'' i = 0 := by
    change (F.map g).hom r = (F.map g).hom 0 at hg
    simpa [r, a'', y'', map_sum, map_mul, lmul_map] using hg
  let : Algebra (F.obj l ⊗[A] F.obj l) (F.obj l) :=
    (Algebra.TensorProduct.lmul' A).toRingHom.toAlgebra
  have hflat : Module.Flat (F.obj l ⊗[A] F.obj l) (F.obj l) := by
    let : Algebra.WeaklyEtale A (F.obj l) := hF l
    exact Algebra.WeaklyEtale.flat_lmul' A (F.obj l)
  let : Module.Flat (F.obj l ⊗[A] F.obj l) (F.obj l) := hflat
  have hrel : Module.IsTrivialRelation a'' y'' :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (by
      show ∑ i, (Algebra.TensorProduct.lmul' A) (a'' i) * y'' i = 0
      exact hg')
  obtain ⟨q, b, z, hz, hb⟩ := hrel
  let zC : Fin q → c.pt := fun t ↦ (c.ι.app l).hom (z t)
  have hfirst : ∀ i, x i = ∑ t, (tensorMap c l (b i t)) •
      zC t := by
    intro i
    calc
      x i = (c.ι.app l).hom (y'' i) := (hy'' i).symm
      _ = (c.ι.app l).hom (∑ t, b i t • z t) := by rw [hz i]
      _ = ∑ t, (tensorMap c l (b i t)) • zC t := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro t _
        show (c.ι.app l).hom ((Algebra.TensorProduct.lmul' A) (b i t) * z t) =
          L (tensorMap c l (b i t)) * zC t
        rw [map_mul, lmul_map]
  have hsecond : ∀ t, ∑ i, f i * tensorMap c l (b i t) = 0 := by
    intro t
    calc
      ∑ i, f i * tensorMap c l (b i t) =
          ∑ i, tensorMap c l (a'' i * b i t) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← ha'' i, map_mul]
      _ = tensorMap c l (∑ i, a'' i * b i t) := by rw [map_sum]
      _ = 0 := by rw [hb t, map_zero]
  exact ⟨q, fun i t ↦ tensorMap c l (b i t), zC, hfirst, hsecond⟩

private lemma weaklyEtale_of_isLocalization (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] : Algebra.WeaklyEtale A B := by
  constructor
  · exact IsLocalization.flat B M
  · apply RingHom.Flat.of_bijective
    let l := Algebra.TensorProduct.lmul' A (S := B)
    let i : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
    have hii : (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) =
        Algebra.TensorProduct.includeRight := by
      apply AlgHom.coe_ringHom_injective
      apply IsLocalization.ringHom_ext M
      ext a
      simp
    refine ⟨?_, ?_⟩
    · exact Function.LeftInverse.injective (g := i) (f := l) (fun x ↦ by
        refine TensorProduct.induction_on x ?_ (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
        · simp [l, i]
        · rw [show i (l (x ⊗ₜ[A] y)) = i (x * y) by simp [l]]
          rw [map_mul]
          have hiy : i y = (Algebra.TensorProduct.includeRight :
              B →ₐ[A] B ⊗[A] B) y := congrArg (fun h : B →ₐ[A] B ⊗[A] B => h y) hii
          rw [hiy]
          simp [i]
        · simp only [map_add, hx, hy])
    · exact Function.RightInverse.surjective (g := i) (f := l) (fun x ↦ by simp [l, i])

/-- The equational flatness proof works for an index in any universe as soon as the
underlying type cocone is colimiting. This isolates the concrete-colimit bridge. -/
private lemma weaklyEtale_of_isColimit_of_forget {A : Type u} [CommRing A]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{w} A) (c : Cocone F) (hc : IsColimit c)
    (hcD : IsColimit ((forget (CommAlgCat A)).mapCocone c))
    (hF : ∀ j, Algebra.WeaklyEtale A (F.obj j)) :
    Algebra.WeaklyEtale A c.pt := by
  let (j : J) : Algebra.WeaklyEtale A (F.obj j) := hF j
  let : Module.Flat A c.pt :=
    AlgebraicGeometry.flat_of_isColimit F c hc hcD (fun _ ↦ inferInstance)
  exact ⟨inferInstance, flat_lmul_of_isColimit F c hc hcD hF⟩

/-- A localization and an étale algebra over a commutative ring are weakly étale, and an
arbitrary filtered colimit of weakly étale algebras is weakly étale. -/
@[stacks 092N]
theorem weaklyEtale_of_isLocalization_etale_filteredColimit
    (A : Type u) [CommRing A] :
    (∀ (B : Type v) [CommRing B] [Algebra A B] (M : Submonoid A)
      [IsLocalization M B], Algebra.WeaklyEtale A B) ∧
    (∀ (B : Type v) [CommRing B] [Algebra A B] [Algebra.Etale A B],
      Algebra.WeaklyEtale A B) ∧
    (∀ (J : Type w) [SmallCategory J] [IsFiltered J] [Small.{max u (w + 1)} J]
      (F : J ⥤ CommAlgCat.{w} A) (c : Cocone F), IsColimit c →
      (∀ j, Algebra.WeaklyEtale A (F.obj j)) → Algebra.WeaklyEtale A c.pt) := by
  constructor
  · intro B _ _ M _
    exact weaklyEtale_of_isLocalization A B M
  constructor
  · intro B _ _ _
    infer_instance
  · intro J _ _ _ F c hc hF
    have hcR := Stacks.CommAlgCat.isColimit_forgetToCommRing hc
    have hcD : IsColimit ((forget (CommAlgCat A)).mapCocone c) :=
      isColimitOfPreserves (forget CommRingCat.{w}) hcR
    exact weaklyEtale_of_isColimit_of_forget F c hc hcD hF

end Sources
