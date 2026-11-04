module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization

/-!
# Algebraizing a quotient of a henselization

Let `C` be a finite type algebra over a Noetherian ring `A` and let `I` be an ideal of `A`.
The adic completion of any quotient of the henselization of the pair `(C, IC)` is again the
adic completion of a finite type `A`-algebra.

The construction writes the henselization as a filtered colimit of etale `C`-algebras, picks
a stage `D` through which a chosen finite generating set of the quotient ideal factors, and
inverts one element `d` of `D` so that `D[1/d]` reduces to `C/IC` modulo `I`.  The quotient of
`D[1/d]` by the lifted generators is then a finite type `A`-algebra whose henselization along
`I` is the given quotient, so the two have the same adic completion.

## Main results

* `Rig.exists_finiteType_adicCompletion_algEquiv_henselization_quotient` — the finite type
  algebra together with an `A`-algebra isomorphism of its completion with the completion of
  the quotient.

## Implementation notes

The henselization is the canonical algebra `henselization C (I.map (algebraMap A C))` of Tag
0A02.  Both completions use the ideals extended from `I`, and the isomorphism is an
`A`-algebra equivalence.  Universe bookkeeping forces the resulting algebra to live in
`Type (max u v)`; it is obtained by `ULift`ing the quotient of the localization.

## References

* [Stacks Project, Tag 0GAS](https://stacks.math.columbia.edu/tag/0GAS)
-/

@[expose] public section

namespace Rig

section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

private abbrev colimitRange {R : Type u} [CommRing R] {J : Type v} [Category.{w} J]
    {F : J ⥤ CommAlgCat.{u} R} (c : Cocone F) (j : J) :
    Subalgebra R ((c.pt : CommAlgCat.{u} R) : Type u) := (c.ι.app j).hom.range

private theorem directed_colimitRange {R : Type u} [CommRing R] {J : Type v}
    [Category.{w} J] [IsFilteredOrEmpty J] {F : J ⥤ CommAlgCat.{u} R}
    (c : Cocone F) : Directed (· ≤ ·) (colimitRange c) := by
  have hle : ∀ {i j : J}, (i ⟶ j) → colimitRange c i ≤ colimitRange c j := by
    rintro i j f y ⟨a, rfl⟩
    exact ⟨(F.map f).hom a, ConcreteCategory.congr_hom (c.w f) a⟩
  exact fun i j => ⟨IsFiltered.max i j, hle (IsFiltered.leftToMax i j),
    hle (IsFiltered.rightToMax i j)⟩

private theorem iSup_colimitRange_eq_top {R : Type u} [CommRing R] {J : Type v}
    [Category.{w} J] {F : J ⥤ CommAlgCat.{u} R} (c : Cocone F) (hc : IsColimit c) :
    ⨆ j, colimitRange c j = ⊤ := by
  let T := ⨆ j, colimitRange c j
  have hmem (j : J) (y : (F.obj j : CommAlgCat.{u} R)) : (c.ι.app j).hom y ∈ T :=
    le_iSup (colimitRange c) j ⟨y, rfl⟩
  let d : Cocone F :=
    { pt := CommAlgCat.of R ↥T
      ι := { app := fun j => CommAlgCat.ofHom ((c.ι.app j).hom.codRestrict T (hmem j))
             naturality := by
              intro i j f
              apply CommAlgCat.hom_ext
              ext x
              exact Subtype.ext (ConcreteCategory.congr_hom (c.w f) x) } }
  have hid : hc.desc d ≫ CommAlgCat.ofHom T.val = 𝟙 _ := by
    refine hc.hom_ext fun j => ?_
    rw [← Category.assoc, hc.fac, Category.comp_id]
    apply CommAlgCat.hom_ext
    ext x
    rfl
  refine eq_top_iff.2 fun x _ => ?_
  have hx : T.val ((hc.desc d).hom x) = x := ConcreteCategory.congr_hom hid x
  exact hx ▸ ((hc.desc d).hom x).property

private theorem exists_colimit_image {R : Type u} [CommRing R] {J : Type v}
    [Category.{w} J] [IsFiltered J] {F : J ⥤ CommAlgCat.{u} R}
    (c : Cocone F) (hc : IsColimit c) (x : (c.pt : CommAlgCat.{u} R)) :
    ∃ (j : J) (y : (F.obj j : CommAlgCat.{u} R)), (c.ι.app j).hom y = x := by
  have : Nonempty J := IsFiltered.nonempty
  have hx : x ∈ (↑(⨆ j, colimitRange c j) : Set ((c.pt : CommAlgCat.{u} R) : Type u)) := by
    rw [iSup_colimitRange_eq_top c hc]
    trivial
  rw [Subalgebra.coe_iSup_of_directed (directed_colimitRange c)] at hx
  obtain ⟨_, ⟨j, rfl⟩, y, hy⟩ := hx
  exact ⟨j, y, hy⟩

private theorem exists_colimit_image_finset {R : Type u} [CommRing R] {J : Type v}
    [Category.{w} J] [IsFiltered J] {F : J ⥤ CommAlgCat.{u} R}
    (c : Cocone F) (hc : IsColimit c) (s : Finset ((c.pt : CommAlgCat.{u} R) : Type u)) :
    ∃ j : J, ∀ x ∈ s, ∃ y : (F.obj j : CommAlgCat.{u} R), (c.ι.app j).hom y = x := by
  classical
  have : Nonempty J := IsFiltered.nonempty
  choose j y hy using fun x => exists_colimit_image c hc x
  obtain ⟨k, hk⟩ := (directed_colimitRange c).finset_le (s.image j)
  exact ⟨k, fun x hx => hk (j x) (Finset.mem_image_of_mem _ hx) ⟨y x, hy x⟩⟩

private theorem unique_etale_map_of_quotient
    {R : Type u} {S : Type u} {B : Type v}
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra.Etale R S]
    [Algebra R B] (K : Ideal B) (hK : K ≤ (⊥ : Ideal B).jacobson)
    (f g : S →ₐ[R] B)
    (hfg : (Ideal.Quotient.mkₐ R K).comp f = (Ideal.Quotient.mkₐ R K).comp g) : f = g := by
  let θ : S ⊗[R] S →ₐ[R] B :=
    Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  let q : B →ₐ[R] B ⧸ K := Ideal.Quotient.mkₐ R K
  have hθ : q.comp θ = (q.comp f).comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [AlgHom.comp_apply, θ, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
    have h := congrArg (fun φ : S →ₐ[R] B ⧸ K => φ y) hfg
    simpa only [AlgHom.comp_apply] using congrArg (q (f x) * ·) h.symm
  let e := Algebra.FormallyUnramified.elem R S
  have hunit : IsUnit (θ e) := by
    have hq : q (θ e) = 1 := by
      rw [← AlgHom.comp_apply, hθ, AlgHom.comp_apply,
        show Algebra.TensorProduct.lmul' R e = 1 from Algebra.FormallyUnramified.lmul_elem,
        map_one]
    have hm : θ e - 1 ∈ K := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      show q (θ e - 1) = 0
      simp [hq]
    exact Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hK hm)
  apply AlgHom.ext
  intro x
  have heq := congrArg θ
    (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) (S := S) x)
  have hmul : f x * θ e = g x * θ e := by
    simpa [θ, e, Algebra.TensorProduct.lift_tmul, mul_comm] using heq.symm
  exact hunit.mul_right_cancel hmul

private theorem henselianPair_quotient_local {R : Type u} [CommRing R] {J K : Ideal R}
    (h : HenselianPair R J) : HenselianPair (R ⧸ K) (J.map (Ideal.Quotient.mk K)) := by
  apply ((henselianPair_tfae.{u,u} (R ⧸ K) (J.map (Ideal.Quotient.mk K))).out 4 1).mp
  intro B _ _ _
  let : Algebra R B := ((algebraMap (R ⧸ K) B).comp (algebraMap R (R ⧸ K))).toAlgebra
  let : IsScalarTower R (R ⧸ K) B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.IsIntegral R B := Algebra.IsIntegral.trans (R ⧸ K)
  have hb : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.IsIntegral R S],
      InducesBijectionOnIdempotents (J.map (algebraMap R S)) :=
    ((henselianPair_tfae.{u,u} R J).out 1 4).mp h
  rw [Ideal.map_map]
  show InducesBijectionOnIdempotents (J.map (algebraMap R B))
  exact hb B

private theorem away_section_quotient_equiv
    {A : Type u} {D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.Etale A D] (I : Ideal A) (α : D →ₐ[A] A ⧸ I)
    (_hα : ∀ a : A, α (algebraMap A D a) = Ideal.Quotient.mk I a) :
    ∃ d : D, α d = 1 ∧
      Nonempty ((Localization.Away d ⧸
        (I.map (algebraMap A (Localization.Away d)))) ≃ₐ[A] A ⧸ I) := by
  let Dmod := D ⧸ I.map (algebraMap A D)
  obtain ⟨X, hXring, hXalg, E, hE⟩ :=
    exists_quotient_algEquiv_prod_of_etale_section A D I α
  let : CommRing X := hXring
  let : Algebra (A ⧸ I) X := hXalg
  let e : Dmod := E.symm (1, (0 : X))
  obtain ⟨d, hd0⟩ := Ideal.Quotient.mk_surjective e
  have hd : α d = 1 := by
    have hh := hE d
    rw [hd0] at hh
    simpa [e] using hh.symm
  have hαunit : IsUnit (α d) := by simp [hd]
  let α' : Localization.Away d →ₐ[A] A ⧸ I :=
    IsLocalization.Away.liftAlgHom (A := A) (f := α) d hαunit
  have hα'comp : α'.toRingHom.comp (algebraMap D (Localization.Away d)) = α.toRingHom :=
    IsLocalization.Away.lift_comp (x := d) (g := α.toRingHom) hαunit
  have hα'comp_apply (a : D) : α' (algebraMap D (Localization.Away d) a) = α a :=
    DFunLike.congr_fun hα'comp a
  have heq_prod {a : D} (ha : α a = 0) : e * Ideal.Quotient.mk _ a = 0 := by
    refine E.injective (Prod.ext ?_ ?_)
    · simp [e, hE, ha]
    · simp [e]
  have hker : RingHom.ker α'.toRingHom = I.map (algebraMap A (Localization.Away d)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, a, hxa⟩ := IsLocalization.Away.surj d x
      have ha0 : α a = 0 := by
        have hx0 : α' x = 0 := RingHom.mem_ker.mp hx
        calc
          α a = α' (algebraMap D (Localization.Away d) a) := (hα'comp_apply a).symm
          _ = α' (x * (algebraMap D (Localization.Away d) d) ^ n) := by rw [hxa]
          _ = α' x * (α' (algebraMap D (Localization.Away d) d)) ^ n := by simp
          _ = 0 := by rw [hx0, hα'comp_apply, hd]; simp
      have hprod := heq_prod ha0
      have hda : d * a ∈ I.map (algebraMap A D) := by
        have hq : Ideal.Quotient.mk (I.map (algebraMap A D)) (d * a) = 0 := by
          rw [map_mul]
          simpa [hd0] using hprod
        exact Ideal.Quotient.eq_zero_iff_mem.mp hq
      have hda' : algebraMap D (Localization.Away d) (d * a) ∈
          I.map (algebraMap A (Localization.Away d)) := by
        simpa only [Ideal.map_map, IsScalarTower.algebraMap_eq A D (Localization.Away d)] using
          Ideal.mem_map_of_mem (algebraMap D (Localization.Away d)) hda
      have ha' : algebraMap D (Localization.Away d) a ∈
          I.map (algebraMap A (Localization.Away d)) := by
        have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away d) d
        apply (Ideal.unit_mul_mem_iff_mem _ (hu.pow 1)).mp
        simpa [map_mul, mul_comm] using hda'
      have hpow : (algebraMap D (Localization.Away d) d) ^ n * x ∈
          I.map (algebraMap A (Localization.Away d)) := by
        rw [mul_comm, hxa]
        exact ha'
      exact (Ideal.unit_mul_mem_iff_mem _
        ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away d) d).pow n)).mp hpow
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      show α' (algebraMap A (Localization.Away d) a) = 0
      rw [AlgHom.commutes]
      exact (Ideal.Quotient.eq_zero_iff_mem).2 ha
  have hsurj : Function.Surjective α' := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨algebraMap A (Localization.Away d) a, by simp [α']⟩
  have hqker : ∀ x ∈ I.map (algebraMap A (Localization.Away d)), α' x = 0 := by
    intro x hx
    rw [← hker] at hx
    exact RingHom.mem_ker.mp hx
  let q : Localization.Away d ⧸ (I.map (algebraMap A (Localization.Away d))) →ₐ[A] A ⧸ I :=
    Ideal.Quotient.liftₐ (I.map (algebraMap A (Localization.Away d))) α' hqker
  have hqcomp : q.comp
      (Ideal.Quotient.mkₐ A (I.map (algebraMap A (Localization.Away d)))) = α' :=
    Ideal.Quotient.liftₐ_comp _ _ _
  have hqbij : Function.Bijective q := by
    constructor
    · intro x y hxy
      induction x using Quotient.inductionOn with
      | _ a =>
        induction y using Quotient.inductionOn with
        | _ b =>
          apply Ideal.Quotient.eq.mpr
          have hab : α' a = α' b := by
            calc
              α' a = q (Ideal.Quotient.mk _ a) := (DFunLike.congr_fun hqcomp a).symm
              _ = q (Ideal.Quotient.mk _ b) := hxy
              _ = α' b := DFunLike.congr_fun hqcomp b
          have hkerab : a - b ∈ RingHom.ker α'.toRingHom :=
            RingHom.mem_ker.mpr ((map_sub _ a b).trans (sub_eq_zero.mpr hab))
          rwa [hker] at hkerab
    · intro y
      obtain ⟨z, hz⟩ := hsurj y
      refine ⟨Ideal.Quotient.mk _ z, ?_⟩
      exact (DFunLike.congr_fun hqcomp z).trans hz
  exact ⟨d, hd, ⟨AlgEquiv.ofBijective q hqbij⟩⟩

private theorem eq_algHom_mod_of_quotient_algEquiv
    {A : Type u} {S : Type v} {T : Type w}
    [CommRing A] [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
    (I : Ideal A) (K : Ideal S)
    (e : (S ⧸ K) ≃ₐ[A] A ⧸ I) (L : Ideal T)
    (f g : S →ₐ[A] T)
    (hf : K.map f.toRingHom ≤ L) (hg : K.map g.toRingHom ≤ L) :
    (Ideal.Quotient.mkₐ A L).comp f = (Ideal.Quotient.mkₐ A L).comp g := by
  apply AlgHom.ext
  intro x
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e (Ideal.Quotient.mk K x))
  have hmk : Ideal.Quotient.mk K x =
      Ideal.Quotient.mk K (algebraMap A S a) := by
    apply e.injective
    calc
      e (Ideal.Quotient.mk K x) = Ideal.Quotient.mk I a := ha.symm
      _ = e (Ideal.Quotient.mk K (algebraMap A S a)) := by simp
  have hxK : x - algebraMap A S a ∈ K := Ideal.Quotient.eq.mp hmk
  have hmem : f x - g x ∈ L := by
    rw [show f x - g x = f (x - algebraMap A S a) - g (x - algebraMap A S a) by simp]
    exact Ideal.sub_mem L (hf (Ideal.mem_map_of_mem f.toRingHom hxK))
      (hg (Ideal.mem_map_of_mem g.toRingHom hxK))
  exact (Ideal.Quotient.eq).2 hmem

/-- A unique-lifting property against henselian pairs in `Type (max u v)` descends to
henselian pairs in `Type v`, by passing through `ULift`. -/
private theorem existsUnique_ringHom_lift_of_ulift {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (IR : Ideal R) (IS : Ideal S)
    (h : ∀ (T : Type (max u v)) [CommRing T] (L : Ideal T), HenselianPair T L →
      ∀ f : R →+* T, IR ≤ L.comap f → ∃! g : S →+* T, g.comp φ = f ∧ IS ≤ L.comap g)
    (T : Type v) [CommRing T] (L : Ideal T) (hT : HenselianPair T L) (f : R →+* T)
    (hf : IR ≤ L.comap f) : ∃! g : S →+* T, g.comp φ = f ∧ IS ≤ L.comap g := by
  let T' := ULift.{max u v} T
  let e : T ≃+* T' := ULift.ringEquiv.symm
  let : Algebra T T' := e.toRingHom.toAlgebra
  let : Module.Finite T T' := Module.Finite.equiv
    (LinearEquiv.ofBijective (Algebra.linearMap T T') e.bijective)
  let : Algebra.IsIntegral T T' := Algebra.IsIntegral.of_finite T T'
  let L' : Ideal T' := L.map e.toRingHom
  have hT' : HenselianPair T' L' := henselianPair_map_of_isIntegral L hT
  let f' : R →+* T' := e.toRingHom.comp f
  have hf' : IR ≤ L'.comap f' := fun x hx => Ideal.mem_map_of_mem e.toRingHom (hf hx)
  obtain ⟨g', hg', hg'unique⟩ := h T' L' hT' f' hf'
  let g : S →+* T := e.symm.toRingHom.comp g'
  have hgcomp : g.comp φ = f := by
    apply RingHom.ext
    intro b
    have hb := congrArg (fun k : R →+* T' => k b) hg'.1
    calc
      g (φ b) = e.symm (g' (φ b)) := by simp [g]
      _ = e.symm (f' b) := congrArg e.symm.toRingHom hb
      _ = f b := by simp [f']
  have hL : L'.map e.symm.toRingHom = L := by
    dsimp [L']
    rw [Ideal.map_map]
    simp
  have hgmap : IS ≤ L.comap g :=
    hg'.2.trans (Ideal.comap_mono (Ideal.le_comap_of_map_le hL.le))
  refine ⟨g, ⟨hgcomp, hgmap⟩, fun g₂ hg₂ => ?_⟩
  let g₂' : S →+* T' := e.toRingHom.comp g₂
  have hg₂'comp : g₂'.comp φ = f' := by
    apply RingHom.ext
    intro b
    calc
      g₂' (φ b) = e (g₂ (φ b)) := by simp [g₂']
      _ = e (f b) := congrArg e.toRingHom (DFunLike.congr_fun hg₂.1 b)
      _ = f' b := by simp [f']
  have hg₂'map : IS ≤ L'.comap g₂' :=
    hg₂.2.trans (Ideal.comap_mono (Ideal.le_comap_of_map_le le_rfl))
  have heq := hg'unique g₂' ⟨hg₂'comp, hg₂'map⟩
  apply RingHom.ext
  intro x
  apply e.injective
  simpa [g, g₂'] using congrArg (fun k : S →+* T' => k x) heq

/-- If `u ∘ v = w` and `w` maps `K` into `L`, then so does `u` on `K.map v`. -/
private theorem map_map_le_of_comp_eq {C X T : Type*} [CommRing C] [CommRing X] [CommRing T]
    {K : Ideal C} {L : Ideal T} (v : C →+* X) (u : X →+* T) (w : C →+* T)
    (h : u.comp v = w) (hw : K.map w ≤ L) : (K.map v).map u ≤ L := by
  rw [Ideal.map_map, h]
  exact hw

/-- `adicCompletionMap` of an `A`-algebra map commutes with the structure maps from `A`. -/
private theorem adicCompletionMap_algebraMap_of_algHom {A S T : Type*} [CommRing A] [CommRing S]
    [CommRing T] [Algebra A S] [Algebra A T] (ψ : S →ₐ[A] T) (IS : Ideal S) (IT : Ideal T)
    (h : IS.map ψ.toRingHom ≤ IT) (a : A) :
    adicCompletionMap ψ.toRingHom IS IT h (algebraMap A (AdicCompletion IS S) a) =
      algebraMap A (AdicCompletion IT T) a := by
  calc
    _ = adicCompletionMap ψ.toRingHom IS IT h
        (algebraMap S (AdicCompletion IS S) (algebraMap A S a)) := by rfl
    _ = algebraMap T (AdicCompletion IT T) (ψ (algebraMap A S a)) :=
      DFunLike.congr_fun (adicCompletionMap_comp_algebraMap ψ.toRingHom IS IT h) _
    _ = algebraMap A (AdicCompletion IT T) a := by
      rw [ψ.commutes]
      exact (IsScalarTower.algebraMap_apply A T _ a).symm

/-- `adicCompletionMap` of a left inverse pair of ring maps composes to the identity. -/
private theorem adicCompletionMap_comp_eq_id {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : S →+* R) (I : Ideal R) (J : Ideal S) (hf : I.map f ≤ J)
    (hg : J.map g ≤ I) (h : g.comp f = RingHom.id R) :
    (adicCompletionMap g J I hg).comp (adicCompletionMap f I J hf) = RingHom.id _ := by
  rw [adicCompletionMap_comp f g I J I hf hg (by rw [h]; simp)]
  simpa only [h] using adicCompletionMap_id I (by simp)

/-- A finite type `A`-algebra in `Type v` has the same `I`-adic completion as a finite type
`A`-algebra in `Type (max u v)`. -/
private theorem exists_ulift_adicCompletion_algEquiv (A : Type u) (S : Type v) [CommRing A]
    [CommRing S] [Algebra A S] [Algebra.FiniteType A S] (I : Ideal A) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.FiniteType A B),
      Nonempty (AdicCompletion (I.map (algebraMap A B)) B ≃ₐ[A]
        AdicCompletion (I.map (algebraMap A S)) S) := by
  let B := ULift.{max u v} S
  let : Algebra A B := Algebra.compHom B
    ((ULift.ringEquiv.symm.toRingHom).comp (algebraMap A S))
  let eB : S ≃ₐ[A] B :=
    { toRingEquiv := ULift.ringEquiv.symm
      commutes' := fun _ => rfl }
  let IS : Ideal S := I.map (algebraMap A S)
  let IB : Ideal B := IS.map eB.toRingHom
  have he : eB.symm.toRingHom.comp eB.toRingHom = RingHom.id _ := by
    ext x
    simp
  have he' : eB.toRingHom.comp eB.symm.toRingHom = RingHom.id _ := by
    ext x
    simp
  let F : AdicCompletion IS S →+* AdicCompletion IB B := adicCompletionMap eB.toRingHom IS IB le_rfl
  let G : AdicCompletion IB B →+* AdicCompletion IS S :=
    adicCompletionMap eB.symm.toRingHom IB IS (by
      show (IS.map eB.toRingHom).map eB.symm.toRingHom ≤ IS
      rw [Ideal.map_map, he]
      simp)
  have hFG : G.comp F = RingHom.id _ :=
    adicCompletionMap_comp_eq_id _ _ IS IB _ _ he
  have hGF : F.comp G = RingHom.id _ :=
    adicCompletionMap_comp_eq_id _ _ IB IS _ _ he'
  have hFbij : Function.Bijective F :=
    Function.bijective_iff_has_inverse.mpr
      ⟨G, fun x => DFunLike.congr_fun hFG x, fun x => DFunLike.congr_fun hGF x⟩
  let Fₐ : AdicCompletion IS S →ₐ[A] AdicCompletion IB B :=
    { toRingHom := F
      commutes' := adicCompletionMap_algebraMap_of_algHom eB.toAlgHom IS IB le_rfl }
  have hsource : I.map (algebraMap A B) = IB := by
    show I.map (algebraMap A B) = (I.map (algebraMap A S)).map eB.toRingHom
    rw [Ideal.map_map]
    congr 1
  refine ⟨B, inferInstance, inferInstance,
    Algebra.FiniteType.of_surjective eB.toAlgHom eB.surjective, ⟨?_⟩⟩
  rw [hsource]
  exact (AlgEquiv.ofBijective Fₐ hFbij).symm

/-- A quotient of the henselization of a finite type `A`-algebra has a completion algebraizable
by a finite type `A`-algebra. -/
@[stacks 0GAS]
public theorem exists_finiteType_adicCompletion_algEquiv_henselization_quotient
    (A : Type u) (C : Type v) [CommRing A] [IsNoetherianRing A]
    [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (I : Ideal A)
    (J : Ideal (henselization C (I.map (algebraMap A C)) : Type v)) :
    let H := (henselization C (I.map (algebraMap A C)) : Type v)
    letI : Algebra A H :=
      ((algebraMap C H).comp (algebraMap A C)).toAlgebra
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra A B)
      (_ : Algebra.FiniteType A B),
      Nonempty (AdicCompletion (I.map (algebraMap A B)) B ≃ₐ[A]
        AdicCompletion (I.map (algebraMap A (H ⧸ J))) (H ⧸ J)) := by
  classical
  dsimp only
  let K : Ideal C := I.map (algebraMap A C)
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  let H := (henselization C K : Type v)
  let : Algebra A H := ((algebraMap C H).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C H := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨H₀, hH₀ring, ι, hH₀pair, hH₀univ⟩ :=
    exists_henselization.{v, max u v} C K
  let : CommRing H₀ := hH₀ring
  let : Algebra C H₀ := ι.toAlgebra
  let : Algebra A H₀ := ((algebraMap C H₀).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C H₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hH₀univSmall : ∀ (B : Type v) [CommRing B] (L : Ideal B),
      HenselianPair B L → ∀ f : C →+* B, K ≤ L.comap f →
        ∃! g : H₀ →+* B, g.comp ι = f ∧ Ideal.map ι K ≤ L.comap g :=
    existsUnique_ringHom_lift_of_ulift ι K (K.map ι) fun T i L => hH₀univ T i L
  have hH₀comp :=
    henselization_isNoetherian_and_completion_equiv C K H₀ hH₀pair hH₀univSmall
  let : IsNoetherianRing H₀ := hH₀comp.2.1
  have eHne : Nonempty (H ≃ₐ[C] H₀) :=
    nonempty_algEquiv_henselization C K H₀ hH₀pair hH₀univSmall
  let eH := Classical.choice eHne
  let : IsNoetherianRing H := isNoetherianRing_of_ringEquiv H₀ eH.symm.toRingEquiv
  have hJfg : J.FG := Ideal.fg_of_isNoetherianRing J
  obtain ⟨n, gen, hgen⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hJfg
  obtain ⟨Kidx, _, hKidx, pres, hStageEtale⟩ := ind_henselization C K
  let F := pres.diag
  let cocone : Cocone F := pres.cocone
  let genSet : Finset H := Finset.univ.image gen
  obtain ⟨j, hrep⟩ := exists_colimit_image_finset cocone pres.isColimit genSet
  let D := (F.obj j : Type v)
  let fD : D →ₐ[C] H := (pres.ι.app j).hom
  let liftGen : Fin n → D := fun i => Classical.choose (hrep (gen i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  have hliftGen (i : Fin n) : fD (liftGen i) = gen i :=
    Classical.choose_spec (hrep (gen i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  have hDétale : Algebra.Etale C D := hStageEtale j
  let KH : Ideal H := K.map (algebraMap C H)
  let qH : H →ₐ[C] H ⧸ KH := Ideal.Quotient.mkₐ C KH
  let qmap : C ⧸ K →ₐ[C] H ⧸ KH :=
    Ideal.quotientMapₐ KH (Algebra.ofId C H) Ideal.le_comap_map
  have hqmap : Function.Bijective qmap := bijective_quotientMap_henselization C K
  let eQ : (C ⧸ K) ≃ₐ[C] (H ⧸ KH) := AlgEquiv.ofBijective qmap hqmap
  let α : D →ₐ[C] C ⧸ K := eQ.symm.toAlgHom.comp (qH.comp fD)
  obtain ⟨d, hdα, eLoc⟩ := away_section_quotient_equiv K α
    (fun a => by simp)
  have hqd : qH (fD d) = qH 1 := by simpa [α] using congrArg eQ.toAlgHom hdα
  have hdmem : fD d - 1 ∈ KH := Ideal.Quotient.eq.mp hqd
  have hpH : HenselianPair H KH := henselianPair_henselization C K
  have hdunit : IsUnit (fD d) :=
    Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hpH.1 hdmem)
  let fD₀ : D →ₐ[C] H₀ := eH.toAlgHom.comp fD
  have hdunit₀ : IsUnit (fD₀ d) := hdunit.map eH.toRingEquiv.toRingHom
  let : Algebra.Etale C (Localization.Away d) := Algebra.Etale.comp C D _
  let σ : Localization.Away d →ₐ[C] H₀ :=
    IsLocalization.Away.liftAlgHom (A := C) (f := fD₀) d hdunit₀
  let gen' : Fin n → Localization.Away d := fun i => algebraMap D (Localization.Away d) (liftGen i)
  let J' : Ideal (Localization.Away d) := Ideal.span (Set.range gen')
  let : CommRing (Localization.Away d ⧸ J') := @CommRing.mk
    (Localization.Away d ⧸ J') (Ideal.Quotient.ring J') (fun x y => by
      induction x using Quotient.inductionOn with
      | _ a =>
        induction y using Quotient.inductionOn with
        | _ b => exact congrArg (Ideal.Quotient.mk J') (mul_comm a b))
  let iD : D →ₐ[C] Localization.Away d := IsScalarTower.toAlgHom C D (Localization.Away d)
  have hσcomp : σ.comp iD = fD₀ := AlgHom.ext fun x => DFunLike.congr_fun
    (IsLocalization.Away.lift_comp (x := d) (g := fD₀.toRingHom) hdunit₀) x
  have hgenmap (i : Fin n) : σ (gen' i) = eH (gen i) :=
    (DFunLike.congr_fun hσcomp (liftGen i)).trans (congrArg eH (hliftGen i))
  let σH : Localization.Away d →ₐ[C] H := eH.symm.toAlgHom.comp σ
  have hgenmapH (i : Fin n) : σH (gen' i) = gen i := by
    simp [σH, hgenmap i]
  have hgensMapH : (Ideal.span (Set.range gen')).map σH.toRingHom = J := by
    rw [Ideal.map_span, ← hgen, ← Set.range_comp]
    exact congrArg (fun g => Ideal.span (Set.range g)) (funext hgenmapH)
  let : Algebra A (Localization.Away d) := Algebra.compHom _ (algebraMap A C)
  let : IsScalarTower A C (Localization.Away d) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra (Localization.Away d) (Localization.Away d ⧸ J') := (Ideal.Quotient.mk J').toAlgebra
  let : Algebra A (Localization.Away d ⧸ J') := Ideal.Quotient.algebra A
  let sigQ : Localization.Away d →ₐ[A] H ⧸ J :=
    (Ideal.Quotient.mkₐ A J).comp (σH.restrictScalars A)
  have hsigQker : ∀ x ∈ J', sigQ x = 0 := by
    intro x hx
    have hm : σH x ∈ (J'.map σH.toRingHom) := Ideal.mem_map_of_mem σH.toRingHom hx
    rw [hgensMapH] at hm
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hm
  let φ : (Localization.Away d ⧸ J') →ₐ[A] H ⧸ J := Ideal.Quotient.liftₐ J' sigQ hsigQker
  let : Algebra (Localization.Away d ⧸ J') (H ⧸ J) := φ.toRingHom.toAlgebra
  let IB : Ideal (Localization.Away d ⧸ J') := I.map (algebraMap A (Localization.Away d ⧸ J'))
  let : Algebra.FiniteType A (Localization.Away d) := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType A C)
    (inferInstance : Algebra.FiniteType C (Localization.Away d))
  let qB : Localization.Away d →ₐ[A] (Localization.Away d ⧸ J') := Ideal.Quotient.mkₐ A J'
  have hqBsurj : Function.Surjective qB := Ideal.Quotient.mk_surjective
  let : Algebra.FiniteType A (Localization.Away d ⧸ J') :=
    Algebra.FiniteType.of_surjective qB hqBsurj
  let : IsNoetherianRing (Localization.Away d ⧸ J') :=
    Algebra.FiniteType.isNoetherianRing A (Localization.Away d ⧸ J')
  let KQ : Ideal (H ⧸ J) := KH.map (Ideal.Quotient.mk J)
  have hQpair : HenselianPair (H ⧸ J) KQ :=
    henselianPair_quotient_local (J := KH) (K := J) hpH
  have hB₀univ : ∀ (T : Type (max u v)) [CommRing T] (L : Ideal T),
      HenselianPair T L → ∀ f : (Localization.Away d ⧸ J') →+* T,
        IB ≤ L.comap f →
        ∃! g : (H ⧸ J) →+* T,
          g.comp (algebraMap (Localization.Away d ⧸ J') (H ⧸ J)) = f ∧
            KQ ≤ L.comap g := by
    intro T _ L hT f hf
    let fC : C →+* T := f.comp ((Ideal.Quotient.mk J').comp
      (algebraMap C (Localization.Away d)))
    have hKf : K.map fC ≤ L := by
      calc
        K.map fC = IB.map f := by
          rw [show K = I.map (algebraMap A C) from rfl, Ideal.map_map,
            show fC.comp (algebraMap A C) = f.comp (algebraMap A (Localization.Away d ⧸ J')) from by
              ext a
              rfl, ← Ideal.map_map]
        _ ≤ L := (Ideal.map_le_iff_le_comap).2 hf
    obtain ⟨g₀, hg₀, hg₀unique⟩ := hH₀univ T inferInstance L hT fC
      ((Ideal.map_le_iff_le_comap).1 hKf)
    let eLoc' := Classical.choice eLoc
    let Kstage : Ideal (Localization.Away d) := K.map (algebraMap C (Localization.Away d))
    have hKstagef : Kstage.map (f.comp (Ideal.Quotient.mk J')) ≤ L :=
      map_map_le_of_comp_eq _ _ fC rfl hKf
    let : Algebra C T := fC.toAlgebra
    let fS : Localization.Away d →ₐ[C] T :=
      { toRingHom := (f.comp (Ideal.Quotient.mk J'))
        commutes' := fun _ => rfl }
    let g₀S : H₀ →ₐ[C] T :=
      { toRingHom := g₀
        commutes' := by
          intro c
          convert congrArg (fun φ : C →+* T => φ c) hg₀.1 using 1 <;> rfl }
    let gS : Localization.Away d →ₐ[C] T := g₀S.comp σ
    have hgSC : gS.toRingHom.comp (algebraMap C (Localization.Away d)) = fC := by
      apply RingHom.ext
      intro c
      calc
        g₀ (σ (algebraMap C (Localization.Away d) c)) =
            g₀ (algebraMap C H₀ c) := by rw [σ.commutes]
        _ = fC c := congrArg (fun φ : C →+* T => φ c) hg₀.1
    have hKstageg : Kstage.map gS.toRingHom ≤ L := map_map_le_of_comp_eq _ _ fC hgSC hKf
    have hred := eq_algHom_mod_of_quotient_algEquiv K Kstage eLoc' L fS gS
      hKstagef hKstageg
    have hmaps : fS = gS :=
      unique_etale_map_of_quotient (R := C) (S := Localization.Away d) (B := T)
        L hT.1 fS gS hred
    let gH : H →+* T := g₀.comp eH.toRingEquiv.toRingHom
    have hJker : J ≤ RingHom.ker gH := by
      rw [← hgen]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply RingHom.mem_ker.mpr
      have hqzero : Ideal.Quotient.mk J' (gen' i) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span ⟨i, rfl⟩)
      show g₀ (eH (gen i)) = 0
      calc
        g₀ (eH (gen i)) = g₀ (σ (gen' i)) := by rw [hgenmap i]
        _ = gS (gen' i) := rfl
        _ = fS (gen' i) := (DFunLike.congr_fun hmaps (gen' i)).symm
        _ = 0 := by simp [fS, hqzero]
    let gQ : (H ⧸ J) →+* T := Ideal.Quotient.lift J gH hJker
    have hgQq : gQ.comp (Ideal.Quotient.mk J) = gH :=
      RingHom.ext fun x => Ideal.Quotient.lift_mk J gH hJker
    have hφq : φ.comp qB = sigQ := Ideal.Quotient.liftₐ_comp J' sigQ hsigQker
    have hgQ : gQ.comp φ.toRingHom = f := by
      apply RingHom.ext
      intro b
      obtain ⟨x, rfl⟩ := hqBsurj b
      calc
        gQ (φ (qB x)) = gH (σH x) :=
          (congrArg gQ (DFunLike.congr_fun hφq x)).trans (DFunLike.congr_fun hgQq (σH x))
        _ = gS x := by simp [gH, gS, g₀S, σH]
        _ = fS x := (DFunLike.congr_fun hmaps x).symm
        _ = f (qB x) := rfl
    have hKQmap : KQ.map gQ ≤ L := by
      refine (Ideal.map_map _ gQ).le.trans (map_map_le_of_comp_eq _ _ fC ?_ hKf)
      apply RingHom.ext
      intro c
      have hc := congrArg (fun k : C →+* T => k c) hg₀.1
      have hec : eH (algebraMap C H c) = ι c := eH.commutes c
      change gQ (Ideal.Quotient.mk J (algebraMap C H c)) = fC c
      simpa [gQ, gH, hec] using hc
    refine ⟨gQ, ⟨hgQ, (Ideal.map_le_iff_le_comap).1 hKQmap⟩, ?_⟩
    intro g hg
    let gH' : H →+* T := g.comp (Ideal.Quotient.mk J)
    let g₀' : H₀ →+* T := gH'.comp eH.symm.toRingEquiv.toRingHom
    have hg₀'comp : g₀'.comp ι = fC := by
      have h := congrArg (fun k : (Localization.Away d ⧸ J') →+* T =>
        k.comp qB.toRingHom) hg.1
      apply RingHom.ext
      intro c
      have hc := congrArg (fun k : Localization.Away d →+* T =>
        k (algebraMap C (Localization.Away d) c)) h
      have hφc := DFunLike.congr_fun hφq (algebraMap C (Localization.Away d) c)
      calc
        g₀' (ι c) = g (Ideal.Quotient.mk J (σH (algebraMap C (Localization.Away d) c))) := by
          have hι : eH.symm (ι c) = algebraMap C H c :=
            eH.symm_apply_eq.mpr (eH.commutes c).symm
          have hσc : eH.symm (σ (algebraMap C (Localization.Away d) c)) = algebraMap C H c :=
            eH.symm_apply_eq.mpr ((σ.commutes c).trans (eH.commutes c).symm)
          show g (Ideal.Quotient.mk J (eH.symm (ι c))) =
            g (Ideal.Quotient.mk J (eH.symm (σ (algebraMap C (Localization.Away d) c))))
          rw [hι, hσc]
        _ = g (φ (qB (algebraMap C (Localization.Away d) c))) := by
          have hh : φ (qB (algebraMap C (Localization.Away d) c)) =
              Ideal.Quotient.mk J (σH (algebraMap C (Localization.Away d) c)) := by
            simpa [sigQ] using hφc
          rw [← hh]
        _ = f (qB (algebraMap C (Localization.Away d) c)) := hc
        _ = fC c := rfl
    have hK0map : (Ideal.map ι K).map g₀' ≤ L := map_map_le_of_comp_eq _ _ fC hg₀'comp hKf
    have heq₀ := hg₀unique g₀' ⟨hg₀'comp, (Ideal.map_le_iff_le_comap).1 hK0map⟩
    have hmapsH : g.comp (Ideal.Quotient.mk J) = gQ.comp (Ideal.Quotient.mk J) := by
      apply RingHom.ext
      intro x
      have hx := congrArg (fun k : H₀ →+* T => k (eH x)) heq₀
      simpa [g₀', gH', gQ, gH] using hx
    exact Ideal.Quotient.ringHom_ext hmapsH
  have hB₀univSmall : ∀ (T : Type v) [CommRing T] (L : Ideal T),
      HenselianPair T L → ∀ f : (Localization.Away d ⧸ J') →+* T,
        IB ≤ L.comap f →
        ∃! g : (H ⧸ J) →+* T,
          g.comp φ.toRingHom = f ∧ KQ ≤ L.comap g :=
    existsUnique_ringHom_lift_of_ulift φ.toRingHom IB KQ hB₀univ
  have hIBtarget : IB.map φ.toRingHom = I.map (algebraMap A (H ⧸ J)) := by
    show (I.map (algebraMap A (Localization.Away d ⧸ J'))).map φ.toRingHom = _
    rw [Ideal.map_map]
    congr 1
    ext a
    exact φ.commutes a
  have hIBφ : IB.map φ.toRingHom = KQ := by
    rw [hIBtarget]
    symm
    show ((I.map (algebraMap A C)).map (algebraMap C H)).map
      (Ideal.Quotient.mk J) = I.map (algebraMap A (H ⧸ J))
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
  have hQpair' : HenselianPair (H ⧸ J) (IB.map φ.toRingHom) := by
    rw [hIBφ]
    exact hQpair
  have hAlg : algebraMap (Localization.Away d ⧸ J') (H ⧸ J) = φ.toRingHom := rfl
  have hB₀univForAGV : ∀ (T : Type v) [CommRing T] (L : Ideal T),
      HenselianPair T L →
        ∀ f : (Localization.Away d ⧸ J') →+* T,
          IB ≤ L.comap f →
            ∃! g : (H ⧸ J) →+* T,
              g.comp (algebraMap (Localization.Away d ⧸ J') (H ⧸ J)) = f ∧
                Ideal.map (algebraMap (Localization.Away d ⧸ J') (H ⧸ J)) IB ≤ L.comap g := by
    simpa only [hAlg, hIBφ] using hB₀univSmall
  have h0AGV := henselization_isNoetherian_and_completion_equiv
    (Localization.Away d ⧸ J') IB (H ⧸ J) hQpair' hB₀univForAGV
  let e0hom : AdicCompletion IB (Localization.Away d ⧸ J') →ₐ[A]
      AdicCompletion (IB.map φ.toRingHom) (H ⧸ J) :=
    { toRingHom := adicCompletionMap (algebraMap (Localization.Away d ⧸ J') (H ⧸ J))
        IB (IB.map φ.toRingHom) le_rfl
      commutes' := adicCompletionMap_algebraMap_of_algHom φ IB _ le_rfl }
  let e0 := AlgEquiv.ofBijective e0hom h0AGV.1
  obtain ⟨B, _, _, hBfinite, ⟨eB⟩⟩ :=
    exists_ulift_adicCompletion_algEquiv A (Localization.Away d ⧸ J') I
  let hFinal : AdicCompletion (I.map (algebraMap A B)) B ≃ₐ[A]
      AdicCompletion (I.map (algebraMap A (H ⧸ J))) (H ⧸ J) := by
    rw [← hIBtarget]
    exact eB.trans e0
  exact ⟨B, inferInstance, inferInstance, hBfinite, ⟨by simpa [H] using hFinal⟩⟩

end

end Rig

end
