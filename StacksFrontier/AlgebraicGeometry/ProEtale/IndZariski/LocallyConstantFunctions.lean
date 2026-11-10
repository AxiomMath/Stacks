module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Basic
public import StacksFrontier.Topology.Profinite.Defs
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Topology.Category.TopCat.ULift
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.CategoryTheory.CofilteredSystem
public import StacksCore.Tactic.StacksAttribute

/-!
# Realizing a profinite space as an affine spectrum

For a field `k` and a profinite space `T`, the ring of locally constant `k`-valued functions on
`T` is an ind-Zariski `k`-algebra whose spectrum is homeomorphic to `T`. For every presentation
of `T` as a limit of finite discrete spaces, this ring is the filtered colimit of the rings of
functions on the finite stages.

## Main definitions

* `AlgebraicGeometry.ProEtale.functionRingDiagram` is the contravariant diagram of function
  rings.
* `AlgebraicGeometry.ProEtale.functionRingCocone` is its cocone of pullbacks to the limit space.

## Main results

* `AlgebraicGeometry.ProEtale.isIndZariski_locallyConstant` gives the ind-Zariski property.
* `AlgebraicGeometry.ProEtale.primeSpectrum_locallyConstant_homeomorph` identifies the spectrum.
* `AlgebraicGeometry.ProEtale.isColimit_functionRingCocone` gives the finite-stage formula.

## Implementation notes

The finite-stage formula is stated by its colimit universal property, so it applies to any
cofiltered presentation, not only a chosen one. Since each stage is finite discrete, its locally
constant function ring is exactly the ring of all functions on that stage.

The point of `T` corresponding to a prime of the function ring is recovered as the point at
which all functions in the prime vanish; this is what `evalSpectrum` inverts.

## References

* [Stacks Project, Tag 09BJ](https://stacks.math.columbia.edu/tag/09BJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w r

namespace AlgebraicGeometry.ProEtale

/-- A Stacks-profinite space is compact, Hausdorff and totally disconnected: the forward
direction of `isProfiniteStacks_iff_compact_t2_totallyDisconnected`, named locally because it
is used as a one-sided fact several times below. -/
theorem compact_t2_totallyDisconnected_of_isProfiniteStacks
    (T : Type v) [TopologicalSpace T] (hT : IsProfiniteStacks T) :
    CompactSpace T ∧ T2Space T ∧ TotallyDisconnectedSpace T :=
  (isProfiniteStacks_iff_compact_t2_totallyDisconnected T).mp hT

/-- On a discrete space every function is locally constant, so the locally constant functions
are all functions. -/
private noncomputable def locallyConstantAlgEquivPi
    (k : Type u) [CommRing k] (S : Type v) [TopologicalSpace S]
    [DiscreteTopology S] : LocallyConstant S k ≃ₐ[k] (S → k) where
  toFun f := f
  invFun f := ⟨f, IsLocallyConstant.of_discrete f⟩
  left_inv f := by ext x; rfl
  right_inv f := rfl
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' r := rfl

/-- The function ring of a finite discrete space is a finite product of copies of the base ring,
hence a local isomorphism over it. -/
private theorem locallyConstant_isLocalIso_of_finite_discrete
    (k : Type u) [CommRing k] (S : Type v) [TopologicalSpace S]
    [Finite S] [DiscreteTopology S] :
    Algebra.IsLocalIso k (LocallyConstant S k) := by
  have : Algebra.IsLocalIso k (S → k) :=
    Algebra.IsLocalIso.pi_of_finite (R := k) (S := fun _ : S => k)
  exact Algebra.IsLocalIso.of_algEquiv (locallyConstantAlgEquivPi k S).symm

/-- Two elements of stages with the same image in a set-theoretically filtered cocone have the
same image in every cocone. -/
private theorem cocone_app_eq_of_factorization
    {J : Type w} [SmallCategory J]
    (F : J ⥤ CommRingCat.{r}) (c : Cocone F)
    (hinj : ∀ i j x y, c.ι.app i x = c.ι.app j y →
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y)
    (s : Cocone F) (i j : J) (x : F.obj i) (y : F.obj j)
    (h : c.ι.app i x = c.ι.app j y) : s.ι.app i x = s.ι.app j y := by
  obtain ⟨k, f, g, hfg⟩ := hinj i j x y h
  rw [← s.w_apply f x, ← s.w_apply g y, hfg]

/-- Two elements of a set-theoretically filtered cocone point come from a common stage. -/
private theorem exists_common_stage
    {J : Type w} [SmallCategory J] [IsFilteredOrEmpty J]
    (F : J ⥤ CommRingCat.{r}) (c : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ i y, x = c.ι.app i y) (a b : c.pt) :
    ∃ (k : J) (x y : F.obj k), a = c.ι.app k x ∧ b = c.ι.app k y := by
  obtain ⟨i, x, rfl⟩ := hsurj a
  obtain ⟨j, y, rfl⟩ := hsurj b
  obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
  exact ⟨k, F.map f x, F.map g y, (c.w_apply f x).symm, (c.w_apply g y).symm⟩

/-- The ring map out of a cocone point which is set-theoretically a filtered colimit. -/
private noncomputable def commRingCoconeDescOfFactorization
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{r}) (c : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ i y, x = c.ι.app i y)
    (hinj : ∀ i j x y, c.ι.app i x = c.ι.app j y →
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y)
    (s : Cocone F) : c.pt →+* s.pt := by
  let hc := Types.FilteredColimit.isColimitOf (F ⋙ forget CommRingCat.{r})
    ((forget CommRingCat.{r}).mapCocone c) hsurj hinj
  let d : c.pt → s.pt := hc.desc ((forget CommRingCat.{r}).mapCocone s)
  have d_fac (i : J) (x : F.obj i) : d (c.ι.app i x) = s.ι.app i x :=
    ConcreteCategory.congr_hom (hc.fac ((forget CommRingCat.{r}).mapCocone s) i) x
  have d_const (z : c.pt) (z' : s.pt) (w : ∀ i, F.obj i) (hz : ∀ i, c.ι.app i (w i) = z)
      (hz' : ∀ i, s.ι.app i (w i) = z') : d z = z' := by
    obtain ⟨i, x, hx⟩ := hsurj z
    rw [hx, d_fac, cocone_app_eq_of_factorization F c hinj s i i x (w i) (hx ▸ (hz i).symm), hz']
  exact
    { toFun := d
      map_one' := d_const 1 1 (fun _ => 1) (by simp) (by simp)
      map_zero' := d_const 0 0 (fun _ => 0) (by simp) (by simp)
      map_add' a b := by
        obtain ⟨k, x, y, rfl, rfl⟩ := exists_common_stage F c hsurj a b
        rw [← map_add, d_fac, d_fac, d_fac, map_add]
      map_mul' a b := by
        obtain ⟨k, x, y, rfl, rfl⟩ := exists_common_stage F c hsurj a b
        rw [← map_mul, d_fac, d_fac, d_fac, map_mul] }

/-- The ring map out of the cocone point factors each leg of the cocone. -/
private theorem commRingCoconeDescOfFactorization_fac
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{r}) (c : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ i y, x = c.ι.app i y)
    (hinj : ∀ i j x y, c.ι.app i x = c.ι.app j y →
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y)
    (s : Cocone F) (i : J) :
    c.ι.app i ≫ CommRingCat.ofHom
      (commRingCoconeDescOfFactorization F c hsurj hinj s) = s.ι.app i := by
  let hc := Types.FilteredColimit.isColimitOf (F ⋙ forget CommRingCat.{r})
    ((forget CommRingCat.{r}).mapCocone c) hsurj hinj
  ext x
  exact ConcreteCategory.congr_hom
    (hc.fac ((forget CommRingCat.{r}).mapCocone s) i) x

/-- A cocone of commutative rings which is a filtered colimit of the underlying sets is a
colimit. -/
private noncomputable def commRingCocone_isColimit_of_factorization
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{r}) (c : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ i y, x = c.ι.app i y)
    (hinj : ∀ i j x y, c.ι.app i x = c.ι.app j y →
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) : IsColimit c := by
  refine ⟨fun s => CommRingCat.ofHom
    (commRingCoconeDescOfFactorization F c hsurj hinj s),
    commRingCoconeDescOfFactorization_fac F c hsurj hinj, fun s m hm => ?_⟩
  apply CommRingCat.hom_ext
  ext x
  obtain ⟨i, y, rfl⟩ := hsurj x
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.ofHom_hom] using
    (ConcreteCategory.congr_hom (hm i) y).trans
      (ConcreteCategory.congr_hom (commRingCoconeDescOfFactorization_fac F c hsurj hinj s i) y).symm

/-- A locally constant function on a limit of finite discrete spaces is pulled back from one of
the stages. -/
private theorem exists_locallyConstant_factor_through_finite_limit
    {J : Type w} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{v}) (c : Cone F) (hc : IsLimit c)
    (hfinite : ∀ j, Finite (F.obj j) ∧ DiscreteTopology (F.obj j))
    (k : Type u) [CommRing k] (f : LocallyConstant c.pt k) :
    ∃ j g, f = LocallyConstant.comap (c.π.app j).hom g := by
  let FU := F ⋙ TopCat.uliftFunctor.{w, v}
  have hfiniteU : ∀ j, Finite (FU.obj j) ∧ DiscreteTopology (FU.obj j) := by
    intro j
    have : Finite (F.obj j) := (hfinite j).1
    have : DiscreteTopology (F.obj j) := (hfinite j).2
    change Finite (ULift.{w} (F.obj j)) ∧ DiscreteTopology (ULift.{w} (F.obj j))
    exact ⟨inferInstance, inferInstance⟩
  let FP := liftToProfinite J FU hfiniteU
  let L := Profinite.limitCone.{w, v} FP
  let hcU := isLimitOfPreserves TopCat.uliftFunctor.{w, v} hc
  let hL := Profinite.limitConeIsLimit.{w, v} FP
  let eFU := liftToProfiniteNatIso J FU hfiniteU
  let hL' := (IsLimit.postcomposeHomEquiv eFU (Profinite.toTopCat.mapCone L)).symm
    (isLimitOfPreserves Profinite.toTopCat hL)
  let e := IsLimit.conePointUniqueUpToIso hL' hcU
  let fL : LocallyConstant L.pt k := f.comap
    ⟨fun x => (e.hom x).down, continuous_uliftDown.comp e.hom.hom.continuous⟩
  obtain ⟨j, g, hg⟩ := Profinite.exists_locallyConstant L hL fL
  refine ⟨j, g.comap ⟨ULift.up, continuous_uliftUp⟩, ?_⟩
  ext x
  have hp := ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_inv_comp hL' hcU j) (ULift.up x)
  have hp' : (L.π.app j) (e.inv (ULift.up x)) = ULift.up ((c.π.app j) x) := hp
  have he : e.hom (e.inv (ULift.up x)) = ULift.up x :=
    ConcreteCategory.congr_hom e.inv_hom_id (ULift.up x)
  have hx := LocallyConstant.congr_fun hg (e.inv (ULift.up x))
  change f ((e.hom (e.inv (ULift.up x))).down) = g ((L.π.app j) (e.inv (ULift.up x))) at hx
  change f x = g (ULift.up ((c.π.app j) x))
  rwa [he, hp'] at hx

/-- The rings of functions on the stages of a diagram of spaces, with pullback maps. -/
def functionRingDiagram (k : Type u) [CommRing k]
    {J : Type w} [SmallCategory J] (F : J ⥤ TopCat.{v}) : Jᵒᵖ ⥤ CommRingCat.{max u v} where
  obj j := CommRingCat.of (LocallyConstant (F.obj j.unop) k)
  map f := CommRingCat.ofHom
    (LocallyConstant.comapRingHom ((F.map f.unop).hom))
  map_id j := by
    ext x y
    simp
  map_comp f g := by
    ext x y
    simp

/-- Pullback to the cone point gives a cocone of function rings. -/
def functionRingCocone (k : Type u) [CommRing k]
    {J : Type w} [SmallCategory J] {F : J ⥤ TopCat.{v}} (c : Cone F) :
    Cocone (functionRingDiagram k F) where
  pt := CommRingCat.of (LocallyConstant c.pt k)
  ι := {
    app := fun j => CommRingCat.ofHom
      (LocallyConstant.comapRingHom (c.π.app j.unop).hom)
    naturality := by
      intro i j f
      ext x
      rw [← c.w f.unop]
      rfl }

/-- A cocone of algebras whose image under the forgetful functor to rings is a colimit is
itself a colimit. -/
private noncomputable def commAlg_isColimit_of_ring
    (k : Type u) [CommRing k] {J : Type w} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{r} k) (c : Cocone F)
    (hc : IsColimit ((forget₂ (CommAlgCat.{r} k) CommRingCat.{r}).mapCocone c)) :
    IsColimit c := by
  let U := forget₂ (CommAlgCat.{r} k) CommRingCat.{r}
  let d (s : Cocone F) : c.pt →ₐ[k] s.pt :=
    { toRingHom := (hc.desc (U.mapCocone s)).hom
      commutes' a := by
        obtain ⟨i⟩ := IsFiltered.nonempty (C := J)
        have h := ConcreteCategory.congr_hom (hc.fac (U.mapCocone s) i)
          (algebraMap k (F.obj i) a)
        change (hc.desc (U.mapCocone s)).hom
          ((c.ι.app i).hom (algebraMap k (F.obj i) a)) =
          (s.ι.app i).hom (algebraMap k (F.obj i) a) at h
        simpa only [AlgHom.commutes, Functor.const_obj_obj] using! h }
  refine ⟨fun s => CommAlgCat.ofHom (d s), fun s i => ?_, fun s m hm =>
    U.map_injective (hc.uniq (U.mapCocone s) (U.map m) fun i => congrArg U.map (hm i))⟩
  ext x
  exact ConcreteCategory.congr_hom (hc.fac (U.mapCocone s) i) x

/-- A cocone of algebras which is a filtered colimit of the underlying sets is a colimit. -/
private noncomputable def commAlgCocone_isColimit_of_factorization
    (k : Type u) [CommRing k]
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{r} k) (c : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ i y, x = c.ι.app i y)
    (hinj : ∀ i j x y, c.ι.app i x = c.ι.app j y →
      ∃ (l : J) (f : i ⟶ l) (g : j ⟶ l), F.map f x = F.map g y) : IsColimit c :=
  commAlg_isColimit_of_ring k F c
    (commRingCocone_isColimit_of_factorization
      (F ⋙ forget₂ (CommAlgCat.{r} k) CommRingCat.{r})
      ((forget₂ (CommAlgCat.{r} k) CommRingCat.{r}).mapCocone c) hsurj hinj)

/-- The function rings of the stages of a diagram of spaces, as algebras over the base ring. -/
private def functionAlgDiagram (k : Type u) [CommRing k]
    {J : Type w} [SmallCategory J] (F : J ⥤ TopCat.{v}) :
    Jᵒᵖ ⥤ CommAlgCat.{max u v} k where
  obj j := CommAlgCat.of k (LocallyConstant (F.obj j.unop) k)
  map f := CommAlgCat.ofHom (LocallyConstant.comapₐ k (F.map f.unop).hom)
  map_id j := by
    ext x y
    simp
  map_comp f g := by
    ext x y
    simp

/-- Pullback to the cone point gives a cocone of function algebras. -/
private def functionAlgCocone (k : Type u) [CommRing k]
    {J : Type w} [SmallCategory J] {F : J ⥤ TopCat.{v}} (c : Cone F) :
    Cocone (functionAlgDiagram k F) where
  pt := CommAlgCat.of k (LocallyConstant c.pt k)
  ι := {
    app := fun j => CommAlgCat.ofHom (LocallyConstant.comapₐ k (c.π.app j.unop).hom)
    naturality := by
      intro i j f
      ext x
      rw [← c.w f.unop]
      rfl }

/-- On a compact space the function ring is the filtered colimit of the function rings of the
discrete quotients, each of which is a local isomorphism over the base ring. -/
private theorem ind_locallyConstant (k : Type u) [CommRing k]
    (T : Type v) [TopologicalSpace T] [CompactSpace T] :
    ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} k => Algebra.IsLocalIso k C)
      (CommAlgCat.of k (LocallyConstant T k)) := by
  let F : DiscreteQuotient T ⥤ TopCat.{v} :=
    { obj Q := TopCat.of Q
      map f := TopCat.ofHom ⟨DiscreteQuotient.ofLE f.le, DiscreteQuotient.ofLE_continuous f.le⟩
      map_id Q := by ext x; exact DiscreteQuotient.ofLE_refl_apply x
      map_comp f g := by ext x; exact (DiscreteQuotient.ofLE_ofLE f.le g.le x).symm }
  let c : Cone F :=
    { pt := TopCat.of T
      π := { app Q := TopCat.ofHom ⟨Q.proj, Q.proj_continuous⟩ } }
  let D := functionAlgDiagram k F
  let C := functionAlgCocone k c
  have hs : ∀ x : C.pt, ∃ i y, x = C.ι.app i y := fun f =>
    ⟨Opposite.op f.discreteQuotient, f.lift, rfl⟩
  have hi : ∀ i j x y, C.ι.app i x = C.ι.app j y →
      ∃ (l : (DiscreteQuotient T)ᵒᵖ) (f : i ⟶ l) (g : j ⟶ l),
        D.map f x = D.map g y := by
    intro i j x y h
    refine ⟨Opposite.op (i.unop ⊓ j.unop), (homOfLE inf_le_left).op,
      (homOfLE inf_le_right).op, ?_⟩
    refine LocallyConstant.ext fun q => ?_
    obtain ⟨t, rfl⟩ := (i.unop ⊓ j.unop).proj_surjective q
    exact LocallyConstant.congr_fun h t
  let pres : ColimitPresentation (DiscreteQuotient T)ᵒᵖ C.pt :=
    ⟨D, C.ι, commAlgCocone_isColimit_of_factorization k D C hs hi⟩
  exact ObjectProperty.of_essentiallySmall_index pres fun i =>
    locallyConstant_isLocalIso_of_finite_discrete k i.unop

/-- **Stacks Project, Tag 09BJ.** Locally constant functions on a profinite space form an
ind-Zariski algebra over a field. -/
@[stacks 09BJ "ind-Zariski algebra"]
theorem isIndZariski_locallyConstant
    (k : Type u) [Field k] (T : Type v) [TopologicalSpace T]
    (hT : IsProfiniteStacks T) :
    IsIndZariski.{u, max u v, max u v} k (LocallyConstant T k) := by
  obtain ⟨hC, hH, hD⟩ := compact_t2_totallyDisconnected_of_isProfiniteStacks T hT
  exact ObjectProperty.prop_of_iso
    (ObjectProperty.ind.{max u v} (fun C : CommAlgCat.{max u v} k => Algebra.IsLocalIso k C))
    (CommAlgCat.isoMk
      (ULift.algEquiv.symm : LocallyConstant T k ≃ₐ[k] ULift (LocallyConstant T k)))
    (ind_locallyConstant k T)

/-- Two points of a set are equal as soon as the same functions to a field vanish at both. -/
private theorem eq_of_forall_zero_iff (k : Type u) [Field k] {S : Type v}
    (x y : S) (h : ∀ f : S → k, f x = 0 ↔ f y = 0) : x = y := by
  classical
  have := (h (fun z => if z = x then 0 else 1)).mp (by simp)
  exact (by simpa using this : y = x).symm

/-- A prime of a ring receiving the functions on a finite set is the vanishing locus at one of
its points. -/
private theorem exists_eval_of_prime_pi (k : Type u) [Field k]
    (S : Type v) [Finite S] {R : Type r} [CommRing R]
    (φ : (S → k) →+* R) (p : PrimeSpectrum R) :
    ∃ s : S, ∀ f, φ f ∈ p.asIdeal ↔ f s = 0 := by
  obtain ⟨⟨s, q⟩, hq⟩ := (PrimeSpectrum.sigmaToPi_bijective (fun _ : S => k)).2
    (PrimeSpectrum.comap φ p)
  refine ⟨s, fun f => ?_⟩
  have h := congrArg (fun q : PrimeSpectrum (S → k) => f ∈ q.asIdeal) hq
  change (f s ∈ q.asIdeal) = (φ f ∈ p.asIdeal) at h
  rw [Ideal.eq_bot_of_prime q.asIdeal] at h
  exact h.symm ▸ Ideal.mem_bot

/-- The functions on a discrete quotient, viewed inside the locally constant functions. -/
private noncomputable def quotientFunctionHom (k : Type u) [CommRing k]
    {T : Type v} [TopologicalSpace T] (Q : DiscreteQuotient T) :
    (Q → k) →+* LocallyConstant T k :=
  (LocallyConstant.comapRingHom ⟨Q.proj, Q.proj_continuous⟩).comp
    (locallyConstantAlgEquivPi k Q).symm.toRingEquiv.toRingHom

/-- The prime of the function ring consisting of the functions vanishing at a given point. -/
private def evalSpectrum (k : Type u) [Field k]
    (T : Type v) [TopologicalSpace T] (t : T) : PrimeSpectrum (LocallyConstant T k) :=
  PrimeSpectrum.comap (LocallyConstant.evalₐ k t).toRingHom ⟨⊥, inferInstance⟩

private theorem mem_evalSpectrum (k : Type u) [Field k]
    (T : Type v) [TopologicalSpace T] (t : T) (f : LocallyConstant T k) :
    f ∈ (evalSpectrum k T t).asIdeal ↔ f t = 0 := Iff.rfl

/-- On a compact space every prime of the function ring is an evaluation prime. -/
private theorem evalSpectrum_surjective (k : Type u) [Field k]
    (T : Type v) [TopologicalSpace T] [CompactSpace T] :
    Function.Surjective (evalSpectrum k T) := by
  intro p
  choose q hq using fun Q : DiscreteQuotient T =>
    exists_eval_of_prime_pi k Q (quotientFunctionHom k Q) p
  have compat (A B : DiscreteQuotient T) (h : A ≤ B) :
      DiscreteQuotient.ofLE h (q A) = q B := by
    apply eq_of_forall_zero_iff k
    intro f
    change (f ∘ DiscreteQuotient.ofLE h) (q A) = 0 ↔ f (q B) = 0
    rw [← hq B f, ← hq A (f ∘ DiscreteQuotient.ofLE h)]
    rfl
  obtain ⟨t, ht⟩ := DiscreteQuotient.exists_of_compat q compat
  refine ⟨t, PrimeSpectrum.ext ?_⟩
  ext f
  rw [mem_evalSpectrum]
  have h := hq f.discreteQuotient f.lift
  rw [← ht f.discreteQuotient] at h
  exact h.symm

/-- On a profinite space distinct points are separated by a locally constant function. -/
private theorem evalSpectrum_injective (k : Type u) [Field k]
    (T : Type v) [TopologicalSpace T] [CompactSpace T] [T2Space T]
    [TotallyDisconnectedSpace T] : Function.Injective (evalSpectrum k T) := by
  intro x y h
  refine DiscreteQuotient.eq_of_forall_proj_eq fun Q => eq_of_forall_zero_iff k _ _ fun f => ?_
  exact Iff.of_eq (congrArg (fun p : PrimeSpectrum (LocallyConstant T k) =>
    quotientFunctionHom k Q f ∈ p.asIdeal) h)

private theorem evalSpectrum_continuous (k : Type u) [Field k]
    (T : Type v) [TopologicalSpace T] : Continuous (evalSpectrum k T) := by
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff.mpr
  rintro _ ⟨f, rfl⟩
  exact (f.isLocallyConstant.isClopen_fiber 0).1.isOpen_compl

private theorem evalSpectrum_isOpenMap (k : Type u) [Field k]
    (T : Type v) [TopologicalSpace T] [CompactSpace T] [T2Space T]
    [TotallyDisconnectedSpace T] : IsOpenMap (evalSpectrum k T) := by
  apply isTopologicalBasis_isClopen.isOpenMap_iff.mpr
  intro U hU
  have h : evalSpectrum k T '' U =
      (PrimeSpectrum.basicOpen (LocallyConstant.charFn k hU) : Set _) := by
    ext p
    obtain ⟨t, rfl⟩ := evalSpectrum_surjective k T p
    change (∃ x, x ∈ U ∧ evalSpectrum k T x = evalSpectrum k T t) ↔
      LocallyConstant.charFn k hU t ≠ 0
    simp only [(evalSpectrum_injective k T).eq_iff, exists_eq_right]
    exact ((not_congr (LocallyConstant.charFn_eq_zero k t hU)).trans not_not).symm
  rw [h]
  exact PrimeSpectrum.isOpen_basicOpen

/-- **Stacks Project, Tag 09BJ.** The spectrum of the ring of locally constant functions on a
profinite space is homeomorphic to that space. -/
@[stacks 09BJ "spectrum"]
theorem primeSpectrum_locallyConstant_homeomorph
    (k : Type u) [Field k] (T : Type v) [TopologicalSpace T]
    (hT : IsProfiniteStacks T) :
    Nonempty (PrimeSpectrum (LocallyConstant T k) ≃ₜ T) := by
  obtain ⟨hC, hH, hD⟩ := compact_t2_totallyDisconnected_of_isProfiniteStacks T hT
  let e := Equiv.ofBijective (evalSpectrum k T)
    ⟨evalSpectrum_injective k T, evalSpectrum_surjective k T⟩
  exact ⟨(e.toHomeomorphOfContinuousOpen
    (evalSpectrum_continuous k T) (evalSpectrum_isOpenMap k T)).symm⟩

/-- In a cofiltered limit of finite sets, the image of some transition map is already the image
of the projection from the limit. -/
private theorem range_projection_of_finite
    {J : Type w} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ Type v) [∀ j, Finite (F.obj j)] (c : Cone F) (hc : IsLimit c) (i : J) :
    ∃ (j : J) (f : j ⟶ i), Set.range (F.map f) = Set.range (c.π.app i) := by
  have hml : F.IsMittagLeffler := F.isMittagLeffler_of_exists_finite_range
    (fun j => ⟨j, 𝟙 j, Set.toFinite _⟩)
  obtain ⟨j, f, hf⟩ := F.isMittagLeffler_iff_eventualRange.mp hml i
  refine ⟨j, f, hf.symm.trans ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    let E := F.toEventualRanges
    have : ∀ j, Nonempty (E.obj j) := by
      intro j
      obtain ⟨l, a, b, _⟩ := IsCofilteredOrEmpty.cone_objs i j
      obtain ⟨y, hy, _⟩ := hml.subset_image_eventualRange F a hx
      exact ⟨⟨F.map b y, F.eventualRange_mapsTo b hy⟩⟩
    obtain ⟨s, hs⟩ := E.eval_section_surjective_of_surjective
      (F.surjective_toEventualRanges hml) i ⟨x, hx⟩
    let t := F.toEventualRangesSectionsEquiv s
    refine ⟨(Types.isLimitEquivSections hc).symm t, ?_⟩
    rw [Types.isLimitEquivSections_symm_apply]
    exact congrArg Subtype.val hs
  · rintro x ⟨y, rfl⟩
    exact F.mem_eventualRange_iff.mpr fun j f => ⟨c.π.app j y, ConcreteCategory.congr_hom (c.w f) y⟩

/-- Two locally constant functions on stages with the same pullback to the limit of a cofiltered
diagram of finite spaces already agree at some later stage. -/
private theorem functionRingCocone_injective_eventually
    (k : Type u) [CommRing k] {J : Type w} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{v}) (c : Cone F) (hc : IsLimit c)
    (hfinite : ∀ j, Finite (F.obj j)) :
    ∀ i j x y, (functionRingCocone k c).ι.app i x = (functionRingCocone k c).ι.app j y →
      ∃ (l : Jᵒᵖ) (f : i ⟶ l) (g : j ⟶ l),
        (functionRingDiagram k F).map f x = (functionRingDiagram k F).map g y := by
  intro i j x y h
  change LocallyConstant (F.obj i.unop) k at x
  change LocallyConstant (F.obj j.unop) k at y
  obtain ⟨l, a, b, _⟩ := IsCofilteredOrEmpty.cone_objs i.unop j.unop
  have : ∀ j, Finite ((F ⋙ forget TopCat).obj j) := hfinite
  obtain ⟨m, f, hf⟩ := range_projection_of_finite (F ⋙ forget TopCat)
    ((forget TopCat).mapCone c) (isLimitOfPreserves _ hc) l
  refine ⟨Opposite.op m, (f ≫ a).op, (f ≫ b).op, ?_⟩
  apply LocallyConstant.ext
  intro z
  obtain ⟨t, ht⟩ := hf ▸ (Set.mem_range_self (f := (F ⋙ forget TopCat).map f) z)
  have key (n : J) (e : l ⟶ n) : F.map e (F.map f z) = c.π.app n t := by
    rw [← show (c.π.app l) t = (F.map f) z from ht]
    exact ConcreteCategory.congr_hom (c.w e) t
  change x ((F.map (f ≫ a)) z) = y ((F.map (f ≫ b)) z)
  rw [F.map_comp, F.map_comp]
  change x ((F.map a) ((F.map f) z)) = y ((F.map b) ((F.map f) z))
  rw [key _ a, key _ b]
  exact LocallyConstant.congr_fun h t

/-- **Stacks Project, Tag 09BJ.** For any presentation of a space as a limit of finite discrete
spaces, its ring of locally constant functions is the colimit of the finite-stage function
rings. -/
@[stacks 09BJ "filtered colimit of finite-stage function rings"]
theorem isColimit_functionRingCocone
    (k : Type u) [Field k] {J : Type w} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{v}) (c : Cone F)
    (hc : IsLimit c)
    (hfinite : ∀ j, Finite (F.obj j) ∧ DiscreteTopology (F.obj j)) :
    Nonempty (IsColimit (functionRingCocone k c)) := by
  refine ⟨commRingCocone_isColimit_of_factorization _ _ ?_
    (functionRingCocone_injective_eventually k F c hc (fun j => (hfinite j).1))⟩
  intro f
  obtain ⟨j, g, hg⟩ := exists_locallyConstant_factor_through_finite_limit F c hc hfinite k f
  exact ⟨Opposite.op j, g, hg⟩

end AlgebraicGeometry.ProEtale
