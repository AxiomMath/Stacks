module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.RingHom.PurelyInseparable
import StacksFrontier.RingTheory.Etale.ResidueFieldExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.QuasiFiniteFiniteAtPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale localisation of quasi-finite morphisms

For a morphism locally of finite type, finitely many distinct isolated points of one fibre admit,
after a single étale base change, finite open neighbourhoods containing exactly one point over the
distinguished point of the base. Those distinguished points have finite purely inseparable residue
field extensions, they are pairwise distinct, and together they exhaust the points of the base
change lying over the chosen points of the original fibre.

## Main results

* `AlgebraicGeometry.exists_etale_finite_opens_of_isolated_fiber_points`: the étale neighbourhood,
  the finite open subschemes, and their distinguished fibre points.

## Implementation notes

The base change is `X ×_S U`. The open subschemes are represented by opens of this pullback, and
distinctness is asserted for their images in the pullback, since points of different open
subschemes otherwise belong to different types. The final clause says that these points exhaust
every point above the specified points of `X`.

The proof enlarges the residue field first and splits afterwards. By Tag 01TF each chosen point has
a finite residue extension `κ(x i)/κ(s)`; a single finite separable extension `L/κ(s)` splitting
the separable part of every `κ(x i)` is produced by
`Stacks.Etale.ResidueFieldRealization.exists_finite_isSeparable_splits`, and Tag 02LF realizes `L`
as the residue field of an étale neighbourhood `U`. Over `U` the fibre of `X ×_S U` at
the distinguished point is `Spec` of the finite `κ(U.point)`-algebra `κ(U.point) ⊗_{κ(s)} κ(x i)`,
which is artinian, so it has finitely many points; the splitting hypothesis makes each of their
residue extensions purely inseparable. Those finitely many points are still isolated in their
fibre, so Tag 02LL applies to them and produces the required opens over a further elementary étale
neighbourhood, which does not change any residue field.

## References

* [Stacks Project, Tag 02LM](https://stacks.math.columbia.edu/tag/02LM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v

namespace AlgebraicGeometry

/-- **A point isolated in its fibre has a finite residue field extension.** For a morphism locally
of finite type this is Tag 01TF read through the topological characterisation of quasi-finiteness
at a point, Tag 01TH. -/
private lemma finite_residueField_of_isIsolatedPoint {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (hx : IsIsolatedPoint (f.asFiber x)) :
    let := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (S.residueField (f x)) (X.residueField x) := by
  have hprop : IsClosed ({f.asFiber x} : Set (f.fiber (f x))) ∧
      ¬ ∃ x' : f.fiber (f x), x' ≠ f.asFiber x ∧ x' ⤳ f.asFiber x :=
    ((quasiFiniteAt_tfae f x).out 2 3).mp hx
  exact (isClosed_asFiber_iff_finite_residueField f x).mp hprop.1

/-- **An étale neighbourhood splitting the separable parts of finitely many finite residue
extensions.** Combining `Stacks.Etale.ResidueFieldRealization.exists_finite_isSeparable_splits`
with Tag 02LF: the splitting field is realized as the residue field at the distinguished point of
an étale neighbourhood. -/
private lemma exists_etaleNeighborhood_residueField_splits
    {S : Scheme.{u}} (s : S) {n : ℕ} (E : Fin n → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra (S.residueField s) (E i)]
    [∀ i, FiniteDimensional (S.residueField s) (E i)] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra (S.residueField s) L)
      (_ : FiniteDimensional (S.residueField s) L) (_ : Algebra.IsSeparable (S.residueField s) L)
      (U : EtaleNeighborhood S s),
      (let := U.residueFieldMap.hom.toAlgebra
       Nonempty (U.scheme.residueField U.point ≃ₐ[S.residueField s] L)) ∧
      ∀ (i : Fin n) (z : E i), IsSeparable (S.residueField s) z →
        ((minpoly (S.residueField s) z).map (algebraMap (S.residueField s) L)).Splits := by
  obtain ⟨L, hLfield, hLalg, hLfinite, hLsep, hsplit⟩ :=
    Stacks.Etale.ResidueFieldRealization.exists_finite_isSeparable_splits
      (K := S.residueField s) (E := E)
  let : Field L := hLfield
  let : Algebra (S.residueField s) L := hLalg
  have : FiniteDimensional (S.residueField s) L := hLfinite
  have : Algebra.IsSeparable (S.residueField s) L := hLsep
  obtain ⟨U, hU⟩ := exists_etaleNeighborhood_residueField_algEquiv S s L
  exact ⟨L, hLfield, hLalg, hLfinite, hLsep, U, hU, fun i z hz => hsplit i z hz⟩

/-- **A quotient of `L ⊗[K] E` is purely inseparable over `L` when `L` splits the separable part of
`E`.** This is the field-theoretic heart of the argument: the residue fields of the primes of
`L ⊗[K] E` are purely inseparable over `L`. -/
private lemma isPurelyInseparable_comp_algebraMap_of_splits
    {K E L M : Type u} [Field K] [Field E] [Field L] [Field M]
    [Algebra K E] [Algebra K L] [FiniteDimensional K E]
    (hsplit : ∀ z : E, IsSeparable K z →
      ((minpoly K z).map (algebraMap K L)).Splits)
    (θ : L ⊗[K] E →+* M) (hθ : Function.Surjective θ) :
    (θ.comp (algebraMap L (L ⊗[K] E))).IsPurelyInseparable := by
  let T := L ⊗[K] E
  let : Algebra E T := Algebra.TensorProduct.rightAlgebra
  let χ := θ.comp (algebraMap L T)
  let ψ := θ.comp (algebraMap E T)
  let : Algebra L M := χ.toAlgebra
  have hχ : χ.comp (algebraMap K L) = ψ.comp (algebraMap K E) := by
    ext a
    show θ (algebraMap L T (algebraMap K L a)) =
      θ (algebraMap E T (algebraMap K E a))
    rw [← IsScalarTower.algebraMap_apply K L T, ← IsScalarTower.algebraMap_apply K E T]
  let R : IntermediateField L M := IntermediateField.adjoin L (Set.range ψ)
  have hgen : R = ⊤ := by
    apply top_le_iff.mp
    intro z hz
    clear hz
    obtain ⟨t, rfl⟩ := hθ z
    induction t using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using R.zero_mem
    | tmul a b =>
        have hab : (a ⊗ₜ[K] b : T) = algebraMap L T a * algebraMap E T b := by
          show (a ⊗ₜ[K] b : T) = (a ⊗ₜ[K] (1 : E)) * ((1 : L) ⊗ₜ[K] b)
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [hab, map_mul]
        exact R.mul_mem (R.algebraMap_mem a) (IntermediateField.subset_adjoin L _ ⟨b, rfl⟩)
    | add a b ha hb => simpa only [map_add] using R.add_mem ha hb
  let e := ringExpChar K
  have : ExpChar L e := expChar_of_injective_ringHom (algebraMap K L).injective e
  have hpow : ∀ z ∈ Set.range ψ, ∃ n : ℕ,
      z ^ e ^ n ∈ (algebraMap L M).range := by
    rintro _ ⟨a, rfl⟩
    exact Stacks.Etale.ResidueFieldRealization.exists_pow_mem_range_of_splits e ψ χ hχ hsplit a
  have hpure : IsPurelyInseparable L R :=
    (IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem L M e).2 hpow
  have hpureTop : IsPurelyInseparable L (⊤ : IntermediateField L M) := hgen ▸ hpure
  exact (IntermediateField.topEquiv.isPurelyInseparable_iff).mp hpureTop

/-- **Isolation in a fibre is inherited by a base change.** If the first projection of a point of
`X ×_S Y` is isolated in its fibre over `S`, then the point itself is isolated in its fibre over
`Y`. -/
private lemma isIsolatedPoint_asFiber_pullback_snd
    {X S Y : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : Y ⟶ S) (y : ↑(pullback f g))
    (hx : IsIsolatedPoint (f.asFiber (pullback.fst f g y))) :
    IsIsolatedPoint ((pullback.snd f g).asFiber y) := by
  let q := pullback.snd f g
  have hqfx : f.QuasiFiniteAt (pullback.fst f g y) :=
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr hx
  let W := f.quasiFiniteLocus
  have hxW : pullback.fst f g y ∈ W := f.mem_quasiFiniteLocus.mpr hqfx
  let qW := pullback.snd (W.ι ≫ f) g
  let e := pullback.map (W.ι ≫ f) g f g W.ι (𝟙 Y) (𝟙 S) (by simp) (by simp)
  have : LocallyQuasiFinite qW := by
    dsimp [qW]
    infer_instance
  have he : IsOpenImmersion e := by
    show IsOpenImmersion (pullback.map (W.ι ≫ f) g f g W.ι (𝟙 Y) (𝟙 S) _ _)
    infer_instance
  have hrange : Set.range e = pullback.fst f g ⁻¹' Set.range W.ι ∩
      pullback.snd f g ⁻¹' Set.range (𝟙 Y) :=
    Scheme.Pullback.range_map (W.ι ≫ f) g f g W.ι (𝟙 Y) (𝟙 S) (by simp) (by simp)
  have hyRange : y ∈ Set.range e := by
    rw [hrange]
    exact ⟨⟨⟨pullback.fst f g y, hxW⟩, rfl⟩, ⟨pullback.snd f g y, by simp⟩⟩
  obtain ⟨yW, hyW⟩ := hyRange
  have hcomp : e ≫ q = qW := by
    dsimp [e, qW, q]
    rw [pullback.map, pullback.lift_snd]
    simp
  have hqW' : qW.QuasiFiniteAt yW := qW.quasiFiniteAt yW
  have hq : q.QuasiFiniteAt y := by
    have hq' : (e ≫ q).QuasiFiniteAt yW := by simpa [hcomp] using hqW'
    have hq'' :=
      (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion (f := e) (g := q)
        (x := yW)).mp hq'
    simpa [hyW] using hq''
  have : LocallyOfFiniteType q := inferInstance
  show IsOpen ({q.asFiber y} : Set (q.fiber (q y)))
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hq

/-- **A pushout of commutative rings over a module-finite leg is module-finite.** Transporting
`Module.Finite.base_change` along the comparison with the tensor product. -/
private lemma moduleFinite_of_isPushout_tensorProduct {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R B]
    {P : CommRingCat.{u}}
    {inl : CommRingCat.of A ⟶ P} {inr : CommRingCat.of B ⟶ P}
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R B)) inl inr) :
    let := inl.hom.toAlgebra
    Module.Finite A P := by
  let : Algebra A P := inl.hom.toAlgebra
  let ep : P ≅ CommRingCat.of (A ⊗[R] B) :=
    h.isoIsPushout (CommRingCat.of A) (CommRingCat.of B)
      (CommRingCat.isPushout_tensorProduct R A B)
  let e : CommRingCat.of (A ⊗[R] B) ≅ P := ep.symm
  let er : (A ⊗[R] B) ≃+* P := e.commRingCatIsoToRingEquiv
  have he : (algebraMap A P).comp (RingEquiv.refl A) =
      er.toRingHom.comp (algebraMap A (A ⊗[R] B)) := by
    ext a
    have hh := congrArg (fun k => k.hom a)
      (IsPushout.inl_isoIsPushout_hom (CommRingCat.of A) (CommRingCat.of B)
        (CommRingCat.isPushout_tensorProduct R A B) h)
    convert hh.symm using 1 <;> rfl
  have : Module.Finite A (A ⊗[R] B) := Module.Finite.base_change R A B
  exact Module.Finite.of_equiv_equiv (RingEquiv.refl A) er he

/-- **The residue fields of a pushout of fields are purely inseparable over the splitting leg.**
Specializing `isPurelyInseparable_comp_algebraMap_of_splits` to a prime of the pushout, which is
automatically maximal because the pushout is artinian. -/
private lemma isPurelyInseparable_residueField_of_isPushout_of_splits
    {K E L : Type u} [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [FiniteDimensional K E]
    {P : CommRingCat.{u}} {inl : CommRingCat.of L ⟶ P}
    {inr : CommRingCat.of E ⟶ P}
    (h : IsPushout (CommRingCat.ofHom (algebraMap K L))
      (CommRingCat.ofHom (algebraMap K E)) inl inr)
    (hsplit : ∀ z : E, IsSeparable K z →
      ((minpoly K z).map (algebraMap K L)).Splits)
    (p : PrimeSpectrum P) :
    (inl ≫ CommRingCat.ofHom (algebraMap P p.asIdeal.ResidueField)).hom.IsPurelyInseparable := by
  let := inl.hom.toAlgebra
  have : Module.Finite L P := moduleFinite_of_isPushout_tensorProduct h
  have : IsArtinianRing P := IsArtinianRing.of_finite L P
  have : p.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p.asIdeal
  let e := (CommRingCat.isPushout_tensorProduct K L E).isoIsPushout
    (CommRingCat.of L) (CommRingCat.of E) h
  let θ := (algebraMap P p.asIdeal.ResidueField).comp e.hom.hom
  have hθ : Function.Surjective θ :=
    p.asIdeal.algebraMap_residueField_surjective.comp
      e.commRingCatIsoToRingEquiv.surjective
  have hinc : (CommRingCat.ofHom (algebraMap L (L ⊗[K] E))) ≫ e.hom = inl :=
    IsPushout.inl_isoIsPushout_hom _ _ _ _
  have hp := isPurelyInseparable_comp_algebraMap_of_splits hsplit θ hθ
  change ((CommRingCat.ofHom (algebraMap L (L ⊗[K] E))) ≫ e.hom ≫
    CommRingCat.ofHom (algebraMap P p.asIdeal.ResidueField)).hom.IsPurelyInseparable at hp
  simpa only [← Category.assoc, hinc] using hp

/-- **The bottom half of a purely inseparable composite of field maps is purely inseparable.** -/
private lemma isPurelyInseparable_of_comp {K L M : Type*} [Field K] [Field L] [Field M]
    (f : K →+* L) (g : L →+* M) (h : (g.comp f).IsPurelyInseparable) :
    f.IsPurelyInseparable := by
  algebraize [f, g, g.comp f]
  exact IsPurelyInseparable.tower_bot K L M

/-- **The top half of a purely inseparable composite of field maps is purely inseparable.** -/
private lemma isPurelyInseparable_of_comp_top {K L M : Type*} [Field K] [Field L] [Field M]
    (f : K →+* L) (g : L →+* M) (h : (g.comp f).IsPurelyInseparable) :
    g.IsPurelyInseparable := by
  algebraize [f, g, g.comp f]
  exact IsPurelyInseparable.tower_top K L M

/-- A point of the prime spectrum of a commutative ring is a prime ideal. -/
private instance spec_asIdeal_isPrime (R : CommRingCat.{u}) (p : Spec R) :
    p.asIdeal.IsPrime := p.isPrime

/-- **The left leg of the residue field tensor product computes the residue field map of the first
projection.** The square identifying `AlgebraicGeometry.Scheme.Pullback.Triplet.tensorInl` with the
residue field map of `pullback.fst` at the point attached to a prime of the tensor product. -/
private lemma tensorInl_comp_algebraMap_residueField {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    (X.residueFieldCongr (T.fst_SpecTensorTo_apply p)).inv ≫
      (pullback.fst f g).residueFieldMap (T.SpecTensorTo p) ≫
      T.SpecTensorTo.residueFieldMap p ≫ (Scheme.Spec.residueFieldIso T.tensor p).hom =
        T.tensorInl ≫ CommRingCat.ofHom (algebraMap T.tensor p.asIdeal.ResidueField) := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecResidueField T.x)]
  simp only [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_inv,
    Scheme.residueFieldCongr_fromSpecResidueField,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  simp only [Category.assoc, T.specTensorTo_fst, ← Spec.map_comp_assoc,
    Iso.inv_hom_id, Category.comp_id]
  rfl

/-- **Pure inseparability of a residue field of the tensor product descends to the first
projection.** -/
private lemma isPurelyInseparable_residueFieldMap_fst_of_tensorInl
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor)
    (hp : (T.tensorInl ≫ CommRingCat.ofHom
      (algebraMap T.tensor p.asIdeal.ResidueField)).hom.IsPurelyInseparable) :
    ((pullback.fst f g).residueFieldMap (T.SpecTensorTo p)).hom.IsPurelyInseparable := by
  rw [← tensorInl_comp_algebraMap_residueField T p] at hp
  exact isPurelyInseparable_of_comp _ _ (isPurelyInseparable_of_comp_top _ _ hp)

/-- **Over a point with trivial residue extension the fibre of a base change is a single point of
the original fibre.** Hence the first projection is injective on that fibre. -/
private lemma injOn_pullback_fst_fiber_of_isIso_residueFieldMap {X S U : Scheme.{u}} (f : X ⟶ S)
    (g : U ⟶ S) (u : U) [IsIso (g.residueFieldMap u)] :
    Set.InjOn (pullback.fst f g) ((pullback.snd f g) ⁻¹' {u}) := by
  let q := pullback.snd f g
  let l := pullback.map q (U.fromSpecResidueField u) f
    (S.fromSpecResidueField (g u)) (pullback.fst f g)
    (Spec.map (g.residueFieldMap u)) g pullback.condition.symm (by simp)
  have hl : IsIso l :=
    (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f g) u).isIso_fst_of_isIso
  have hfac : q.fiberι u ≫ pullback.fst f g = l ≫ f.fiberι (g u) :=
    (pullback.lift_fst _ _ _).symm
  intro a ha b hb hab
  obtain ⟨a', rfl⟩ := (q.range_fiberι u).ge ha
  obtain ⟨b', rfl⟩ := (q.range_fiberι u).ge hb
  have : l a' = l b' := (f.fiberι (g u)).isEmbedding.injective (by
    show (l ≫ f.fiberι (g u)) a' = (l ≫ f.fiberι (g u)) b'
    rwa [← hfac])
  exact congrArg (q.fiberι u) (l.isEmbedding.injective this)

/-- **Stacks Project, Tag 02LM.** Finitely many distinct isolated points of a fibre of a morphism
locally of finite type have, after a single étale base change, finite open neighbourhoods meeting
the distinguished fibre in exactly one point, with finite purely inseparable residue extension,
and these points exhaust the base change of the chosen points. -/
@[stacks 02LM, ega "IV 18.12.1" "more general"]
theorem exists_etale_finite_opens_of_isolated_fiber_points
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (n : ℕ) (s : S) (x : Fin n → X) (hx : ∀ i, f (x i) = s)
    (hx_injective : Function.Injective x)
    (hx_isolated : ∀ i, IsIsolatedPoint (f.asFiber (x i))) :
    ∃ (U : EtaleNeighborhood S s)
      (m : Fin n → ℕ)
      (V : ∀ i, Fin (m i) → (pullback f U.toBase).Opens)
      (v : ∀ i j, V i j),
      (∀ i j,
        let g := (V i j).ι ≫ pullback.snd f U.toBase
        IsFinite g ∧
          g ⁻¹' {U.point} = {v i j} ∧
          ((V i j).ι ≫ pullback.fst f U.toBase) (v i j) = x i ∧
          ∃ hvu : g (v i j) = U.point,
            RingHom.Finite (((U.scheme.residueFieldCongr hvu).inv ≫
              g.residueFieldMap (v i j)).hom) ∧
            ((U.scheme.residueFieldCongr hvu).inv ≫
              g.residueFieldMap (v i j)).hom.IsPurelyInseparable) ∧
      Function.Injective (fun p : Σ i, Fin (m i) ↦ (V p.1 p.2).ι (v p.1 p.2)) ∧
      (∀ i (y : ↥(pullback f U.toBase)),
        (pullback.snd f U.toBase) y = U.point →
        (pullback.fst f U.toBase) y = x i →
        ∃ j, (V i j).ι (v i j) = y) := by
  classical
  let K := S.residueField s
  let E : Fin n → Type u := fun i => X.residueField (x i)
  let (i : Fin n) : Algebra K (E i) :=
    (((S.residueFieldCongr (hx i)).inv ≫ f.residueFieldMap (x i)).hom).toAlgebra
  have (i : Fin n) : Module.Finite K (E i) := by
    let : Algebra (S.residueField (f (x i))) (E i) := (f.residueFieldMap (x i)).hom.toAlgebra
    have : Module.Finite (S.residueField (f (x i))) (E i) :=
      finite_residueField_of_isIsolatedPoint f (x i) (hx_isolated i)
    let e : K ≃+* S.residueField (f (x i)) :=
      (S.residueFieldCongr (hx i)).symm.commRingCatIsoToRingEquiv
    have hcomp : (algebraMap K (E i)).comp e.symm.toRingHom =
        algebraMap (S.residueField (f (x i))) (E i) := by
      cases hx i
      rfl
    exact Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl (E i)) hcomp
  have (i : Fin n) : FiniteDimensional K (E i) := inferInstance
  obtain ⟨L, hLfield, hLalg, hLfinite, hLsep, U, hUL, hsplit⟩ :=
    exists_etaleNeighborhood_residueField_splits (S := S) s E
  let : Field L := hLfield
  let : Algebra K L := hLalg
  have : FiniteDimensional K L := hLfinite
  have : Algebra.IsSeparable K L := hLsep
  let K' := U.scheme.residueField U.point
  let : Algebra K K' := U.residueFieldMap.hom.toAlgebra
  have hsplit' : ∀ (i : Fin n) (z : E i), IsSeparable K z →
      ((minpoly K z).map (algebraMap K K')).Splits :=
    fun i z hz => (hsplit i z hz).of_algHom (Classical.choice hUL).symm
  let T : Fin n → Scheme.Pullback.Triplet U.toBase f := fun i =>
    { x := U.point
      y := x i
      s := s
      hx := U.map_point
      hy := hx i }
  let (i : Fin n) : Algebra K' ((T i).tensor : Type u) :=
    ((T i).tensorInl).hom.toAlgebra
  have ht (i : Fin n) : IsPushout (CommRingCat.ofHom (algebraMap K K'))
      (CommRingCat.ofHom (algebraMap K (E i))) (T i).tensorInl (T i).tensorInr :=
    IsPushout.of_hasPushout _ _
  have (i : Fin n) : Module.Finite K' ((T i).tensor : Type u) :=
    moduleFinite_of_isPushout_tensorProduct (R := K) (A := K') (B := E i) (ht i)
  have (i : Fin n) : IsArtinianRing ((T i).tensor : Type u) := IsArtinianRing.of_finite K' _
  have (i : Fin n) : Finite (PrimeSpectrum (T i).tensor) := inferInstance
  let α := Σ i : Fin n, PrimeSpectrum (T i).tensor
  let : Fintype α := Fintype.ofFinite α
  let N := Fintype.card α
  let eFin : Fin N ≃ α := (Fintype.equivFin α).symm
  let q := pullback.snd f U.toBase
  let y : Fin N → ↑(pullback f U.toBase) := fun j =>
    (pullbackSymmetry U.toBase f).hom
      ((T (eFin j).1).SpecTensorTo (eFin j).2)
  have hybase : ∀ j, q (y j) = U.point := by
    intro j
    dsimp [y, q]
    rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd]
    exact (T (eFin j).1).fst_SpecTensorTo_apply (eFin j).2
  have hxfst : ∀ j, (pullback.fst f U.toBase) (y j) = x (eFin j).1 := by
    intro j
    dsimp [y]
    rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]
    exact (T (eFin j).1).snd_SpecTensorTo_apply (eFin j).2
  have hyisolated (j : Fin N) : IsIsolatedPoint (q.asFiber (y j)) :=
    isIsolatedPoint_asFiber_pullback_snd f U.toBase (y j) (by rw [hxfst j]; exact hx_isolated _)
  have hypure : ∀ j, (q.residueFieldMap (y j)).hom.IsPurelyInseparable := by
    intro j
    let i := (eFin j).1
    let p := (eFin j).2
    have hp := isPurelyInseparable_residueFieldMap_fst_of_tensorInl (T i) p
      (isPurelyInseparable_residueField_of_isPushout_of_splits (ht i) (hsplit' i) p)
    have he : (pullbackSymmetry U.toBase f).hom ≫ q =
        pullback.fst U.toBase f := pullbackSymmetry_hom_comp_snd _ _
    rw [← he, Scheme.residueFieldMap_comp] at hp
    exact isPurelyInseparable_of_comp _ _ hp
  obtain ⟨U', hU', V', v', hfinite, hsingle, hfst, hres⟩ :=
    exists_elementaryEtaleNeighborhood_finite_opens_of_isolated_fiber_points
      q U.point N y hybase hyisolated
  have : Etale U'.toBase := U'.etale_toBase
  have : Etale U.toBase := U.etale_toBase
  let W : EtaleNeighborhood S s :=
    { scheme := U'.scheme
      point := U'.point
      toBase := U'.toBase ≫ U.toBase
      map_point := by
        show U.toBase (U'.toBase U'.point) = s
        exact congrArg U.toBase U'.map_point |>.trans U.map_point }
  let β := {z : ↥(pullback f U.toBase) // z ∈ Set.range y}
  have : Finite β := (Set.finite_range y).to_subtype
  let : Fintype β := Fintype.ofFinite β
  let pick : β → Fin N := fun z => Classical.choose z.2
  have pick_spec : ∀ z : β, y (pick z) = z.1 := fun z => Classical.choose_spec z.2
  let loc : β → Fin n := fun z => (eFin (pick z)).1
  have loc_image : ∀ z : β, (pullback.fst f U.toBase) z.1 = x (loc z) := by
    intro z
    rw [← pick_spec z]
    exact hxfst (pick z)
  let J : Fin n → Type u := fun i => {z : β // loc z = i}
  let m : Fin n → ℕ := fun i => Fintype.card (J i)
  let eJ : ∀ i, Fin (m i) ≃ J i := fun i => (Fintype.equivFin (J i)).symm
  let beta : ∀ i, Fin (m i) → β := fun i j => (eJ i j).1
  let idx : ∀ i, Fin (m i) → Fin N := fun i j => pick (beta i j)
  have idx_mem : ∀ i j, (eFin (idx i j)).1 = i := fun i j => (eJ i j).2
  let eAssoc := pullbackLeftPullbackSndIso f U.toBase U'.toBase
  let r : ∀ k, (V' k).toScheme ⟶ pullback f W.toBase :=
    fun k => (V' k).ι ≫ eAssoc.hom
  let V : ∀ i, Fin (m i) → (pullback f W.toBase).Opens :=
    fun i j => (r (idx i j)).opensRange
  let eV : ∀ i j, (V' (idx i j)).toScheme ≅ (V i j).toScheme :=
    fun i j => (r (idx i j)).isoOpensRange
  let v : ∀ i j, V i j := fun i j => (eV i j).hom (v' (idx i j))
  have hAssocSnd : eAssoc.hom ≫ pullback.snd f W.toBase =
      pullback.snd q U'.toBase := by
    show eAssoc.hom ≫ pullback.snd f (U'.toBase ≫ U.toBase) = _
    exact pullbackLeftPullbackSndIso_hom_snd f U.toBase U'.toBase
  have hAssocFst : eAssoc.hom ≫ pullback.fst f W.toBase =
      pullback.fst q U'.toBase ≫ pullback.fst f U.toBase := by
    show eAssoc.hom ≫ pullback.fst f (U'.toBase ≫ U.toBase) = _
    exact pullbackLeftPullbackSndIso_hom_fst f U.toBase U'.toBase
  have hyRange : ∀ i (z : ↥(pullback f U.toBase)),
      q z = U.point → (pullback.fst f U.toBase) z = x i → z ∈ Set.range y := by
    intro i z hzu hzx
    let e := Scheme.Pullback.carrierEquiv (f := U.toBase) (g := f)
    let z' := (pullbackSymmetry U.toBase f).inv z
    let t := e z'
    have hz'fst : pullback.fst U.toBase f z' = U.point := by
      show pullback.fst U.toBase f ((pullbackSymmetry U.toBase f).inv z) = _
      rw [← Scheme.Hom.comp_apply, pullbackSymmetry_inv_comp_fst]
      exact hzu
    have hz'snd : pullback.snd U.toBase f z' = x i := by
      show pullback.snd U.toBase f ((pullbackSymmetry U.toBase f).inv z) = _
      rw [← Scheme.Hom.comp_apply, pullbackSymmetry_inv_comp_snd]
      exact hzx
    have hT : t.1 = T i := by
      apply Scheme.Pullback.Triplet.ext
      · have hh := Scheme.Pullback.carrierEquiv_symm_fst t.1 t.2
        change pullback.fst U.toBase f (e.symm t) = t.1.x at hh
        rw [e.symm_apply_apply] at hh
        exact hh.symm.trans hz'fst
      · have hh := Scheme.Pullback.carrierEquiv_symm_snd t.1 t.2
        change pullback.snd U.toBase f (e.symm t) = t.1.y at hh
        rw [e.symm_apply_apply] at hh
        exact hh.symm.trans hz'snd
    let eTensor := Scheme.Pullback.Triplet.tensorCongr hT
    let p : Spec (T i).tensor := Spec.map eTensor.inv t.2
    have hSpec : (T i).SpecTensorTo p = z' := by
      have htc := Scheme.Pullback.tensorCongr_SpecTensorTo hT
      have htc' := congrArg (fun a => a p) htc
      have hmap : (Spec.map eTensor.hom) p = t.2 := by
        show (Spec.map eTensor.inv ≫ Spec.map eTensor.hom) t.2 = t.2
        rw [← Spec.map_comp]
        simp
      calc
        (T i).SpecTensorTo p = t.1.SpecTensorTo ((Spec.map eTensor.hom) p) := htc'.symm
        _ = t.1.SpecTensorTo t.2 := by rw [hmap]
        _ = z' := by
          show e.symm (e z') = z'
          exact e.symm_apply_apply z'
    obtain ⟨k, hk⟩ := eFin.surjective ⟨i, p⟩
    refine ⟨k, ?_⟩
    show (pullbackSymmetry U.toBase f).hom
      ((T (eFin k).1).SpecTensorTo (eFin k).2) = z
    rw [hk]
    have hh := congrArg (pullbackSymmetry U.toBase f).hom hSpec
    simpa [z'] using hh
  have hcenter : ∀ i j,
      eAssoc.hom ((V' (idx i j)).ι (v' (idx i j))) = (V i j).ι (v i j) := by
    intro i j
    have hh := congrArg (fun a => a (v' (idx i j)))
      (Scheme.Hom.isoOpensRange_hom_ι (r (idx i j)))
    exact hh.symm
  refine ⟨W, m, V, v, ?_, ?_, ?_⟩
  · intro i j
    let k := idx i j
    let g := (V i j).ι ≫ pullback.snd f W.toBase
    let g' := (V' k).ι ≫ pullback.snd q U'.toBase
    have hopen {Z : Scheme.{u}} (φ : pullback f W.toBase ⟶ Z) :
        (eV i j).hom ≫ (V i j).ι ≫ φ = (V' k).ι ≫ eAssoc.hom ≫ φ := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ φ) (Scheme.Hom.isoOpensRange_hom_ι (r k))
    have hproj : (eV i j).hom ≫ g = g' := by
      simp only [g, g', hopen, hAssocSnd]
    have hfinite' : IsFinite g := by
      have hmap : g = (eV i j).inv ≫ g' := by rw [← hproj, Iso.inv_hom_id_assoc]
      rw [hmap]
      have : IsFinite g' := hfinite k
      infer_instance
    have hpoint : g (v i j) = W.point := by
      have hh := congrArg (fun a => a (v' (idx i j))) hproj
      change g ((eV i j).hom (v' (idx i j))) = g' (v' (idx i j)) at hh
      rw [hh]
      exact (hsingle k).ge (Set.mem_singleton _)
    have hsing : g ⁻¹' {W.point} = {v i j} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hz
        have hzinv : (eV i j).hom ((eV i j).inv z) = z := by simp
        have hz' : g' ((eV i j).inv z) = U'.point := by
          have hh := congrArg (fun a => a ((eV i j).inv z)) hproj
          change g ((eV i j).hom ((eV i j).inv z)) = g' ((eV i j).inv z) at hh
          rw [hzinv, hz] at hh
          exact hh.symm
        have hv_eq : (eV i j).inv z = v' k := (hsingle k).le hz'
        rw [← hzinv, hv_eq]
        exact Set.mem_singleton _
      · rintro rfl
        exact hpoint
    have himage : ((V i j).ι ≫ pullback.fst f W.toBase) (v i j) = x i := by
      have hproj' : (eV i j).hom ≫
          ((V i j).ι ≫ pullback.fst f W.toBase) =
          (V' k).ι ≫ pullback.fst q U'.toBase ≫ pullback.fst f U.toBase := by
        rw [hopen, hAssocFst]
      calc
        ((V i j).ι ≫ pullback.fst f W.toBase) (v i j) =
            ((V' k).ι ≫ pullback.fst q U'.toBase ≫ pullback.fst f U.toBase)
              (v' k) := by
                show ((V i j).ι ≫ pullback.fst f W.toBase)
                  ((eV i j).hom (v' k)) = _
                exact congrArg (fun a => a (v' k)) hproj'
        _ = (pullback.fst f U.toBase) (y k) := by
          show pullback.fst f U.toBase
            (pullback.fst q U'.toBase ((V' k).ι (v' k))) = _
          exact congrArg (pullback.fst f U.toBase) (hfst k)
        _ = x ((eFin k).1) := hxfst k
        _ = x i := congrArg x (idx_mem i j)
    refine ⟨hfinite', hsing, himage, ?_⟩
    have : IsFinite g := hfinite'
    let : Field ((V' k).toScheme.residueField (v' k)) := by
      dsimp only [Scheme.residueField]
      infer_instance
    have hfg : (g.residueFieldMap (v i j)).hom.Finite :=
      finite_residueField_of_isIsolatedPoint g (v i j)
        (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (g.quasiFiniteAt _))
    have hpg' : (g'.residueFieldMap (v' k)).hom.IsPurelyInseparable := by
      let t := (V' k).ι ≫ pullback.fst q U'.toBase
      have ht : (q.residueFieldMap (t (v' k))).hom.IsPurelyInseparable := by
        show RingHom.IsPurelyInseparable
          (q.residueFieldMap (((V' k).ι ≫ pullback.fst q U'.toBase) (v' k))).hom
        rw [hfst k]
        exact hypure k
      have : IsIso (t.residueFieldMap (v' k)) := hres k
      have hc : ((t ≫ q).residueFieldMap (v' k)).hom.IsPurelyInseparable := by
        rw [Scheme.residueFieldMap_comp t q (v' k)]
        exact ht.comp (RingHom.isPurelyInseparable_of_surjective _
          (asIso (t.residueFieldMap (v' k))).commRingCatIsoToRingEquiv.surjective)
      have hsquare : t ≫ q = g' ≫ U'.toBase := by
        dsimp [t, g']
        rw [Category.assoc, pullback.condition, Category.assoc]
      rw [hsquare, Scheme.residueFieldMap_comp g' U'.toBase (v' k)] at hc
      exact isPurelyInseparable_of_comp_top _ _ hc
    have hpg : (g.residueFieldMap (v i j)).hom.IsPurelyInseparable := by
      have hc : (((eV i j).hom ≫ g).residueFieldMap (v' k)).hom.IsPurelyInseparable := by
        rwa [hproj]
      rw [Scheme.residueFieldMap_comp (eV i j).hom g (v' k)] at hc
      exact isPurelyInseparable_of_comp _ _ hc
    exact ⟨hpoint, hfg.comp (RingHom.Finite.of_surjective _
        (W.scheme.residueFieldCongr hpoint).symm.commRingCatIsoToRingEquiv.surjective),
      (RingHom.isPurelyInseparable_of_surjective _
        (W.scheme.residueFieldCongr hpoint).symm.commRingCatIsoToRingEquiv.surjective).comp hpg⟩
  · intro a b hab
    rcases a with ⟨i, j⟩
    rcases b with ⟨i', j'⟩
    have hcenters : (V i j).ι (v i j) = (V i' j').ι (v i' j') := hab
    have hbeta : beta i j = beta i' j' := by
      apply Subtype.ext
      have hb (i j) : (pullback.fst q U'.toBase) (eAssoc.inv ((V i j).ι (v i j))) =
          y (idx i j) := by
        rw [← hcenter i j]
        simp only [← Scheme.Hom.comp_apply, Iso.hom_inv_id, Category.id_comp]
        exact hfst (idx i j)
      calc
        (beta i j).1 = y (idx i j) := (pick_spec (beta i j)).symm
        _ = y (idx i' j') := by rw [← hb, ← hb, hcenters]
        _ = (beta i' j').1 := pick_spec (beta i' j')
    have hi : i = i' := (eJ i j).2.symm.trans ((congrArg loc hbeta).trans (eJ i' j').2)
    apply Sigma.ext hi
    subst i'
    exact ((eJ i).injective (Subtype.ext hbeta)).heq
  · intro i z hzu hzx
    let z' := eAssoc.inv z
    have hez : eAssoc.hom z' = z := by simp [z']
    have hz'snd : pullback.snd q U'.toBase z' = U'.point := by
      calc
        _ = (eAssoc.hom ≫ pullback.snd f W.toBase) z' :=
          congrArg (fun a => a z') hAssocSnd.symm
        _ = pullback.snd f W.toBase z := congrArg (pullback.snd f W.toBase) hez
        _ = U'.point := hzu
    have hz'fst : pullback.fst f U.toBase (pullback.fst q U'.toBase z') = x i := by
      calc
        _ = (eAssoc.hom ≫ pullback.fst f W.toBase) z' :=
          congrArg (fun a => a z') hAssocFst.symm
        _ = pullback.fst f W.toBase z := congrArg (pullback.fst f W.toBase) hez
        _ = x i := hzx
    have hbase : q (pullback.fst q U'.toBase z') = U.point := by
      show (pullback.fst q U'.toBase ≫ q) z' = U.point
      rw [pullback.condition]
      show U'.toBase (pullback.snd q U'.toBase z') = U.point
      rw [hz'snd, U'.map_point]
    let b : β := ⟨pullback.fst q U'.toBase z', hyRange i _ hbase hz'fst⟩
    have hb : loc b = i := hx_injective ((loc_image b).symm.trans hz'fst)
    let j := (eJ i).symm ⟨b, hb⟩
    have hbj : beta i j = b := congrArg Subtype.val ((eJ i).apply_symm_apply ⟨b, hb⟩)
    have hyj : y (idx i j) = pullback.fst q U'.toBase z' := by
      rw [show idx i j = pick (beta i j) from rfl, pick_spec, hbj]
    have : IsIso (U'.toBase.residueFieldMap U'.point) := (U'.isElementary_iff).mp hU'
    have hzcenter : (V' (idx i j)).ι (v' (idx i j)) = z' := by
      apply injOn_pullback_fst_fiber_of_isIso_residueFieldMap q U'.toBase U'.point
      · exact (hsingle _).ge (Set.mem_singleton _)
      · exact hz'snd
      · exact (hfst (idx i j)).trans hyj
    refine ⟨j, ?_⟩
    rw [← hcenter, hzcenter, hez]

end AlgebraicGeometry

end
