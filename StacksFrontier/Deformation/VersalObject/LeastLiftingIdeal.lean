module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts
public import StacksFrontier.Deformation.Schlessinger.Basic

/-!
# The smallest ideal over which an object lifts

Let `p : F ⥤ 𝒞_Λ` be cofibered in groupoids and satisfy Schlessinger's condition (S1), and let
`f : B ⟶ p(x)` be a surjection whose kernel is annihilated by the maximal ideal of `B`. Among
the ideals of that kernel over whose quotients the object `x` lifts there is a smallest one.
This is the algebraic form of "the smallest closed subscheme over which an object extends".

The proof is the one in the source. The set of such ideals is nonempty and `B` is Artinian, so
it has a minimal member `J`; given any other member `K` one enlarges `J` to an ideal `J'` of
the kernel with `J' ⊔ K` the whole kernel and `J' ⊓ K = J ⊓ K`, which is possible because the
maximal ideal annihilates the kernel, and then (S1) applied to the fibre product of the two
quotients produces a lift over `B / (J' ⊓ K)`. Minimality of `J` forces `J' ⊓ K = J`, whence
`J ≤ K`.

## Main results

* `Deformation.exists_least_lifting_ideal`: the smallest ideal over which the object lifts.

## Implementation notes

An ideal `J` is represented by a surjective morphism `q : B ⟶ C` with kernel `J`, rather than
by choosing a particular quotient algebra. The factorization `q ≫ g = f` and the equality
relating the lifting arrow to `g` ensure that the object over `C ≅ B / J` maps to the specified
object over `p(x)`.

## References

* [Stacks Project, Tag 06SZ](https://stacks.math.columbia.edu/tag/06SZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF

namespace Deformation

private theorem exists_extension_with_sup_eq_of_product_bot
    {R : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (I J K : Ideal R) (hJI : J ≤ I) (hKI : K ≤ I)
    (hann : maximalIdeal R * I = ⊥) :
    ∃ J' : Ideal R, J ≤ J' ∧ J' ≤ I ∧ J' ⊔ K = I ∧ J' ⊓ K = J ⊓ K := by
  classical
  let S : Set (Submodule R R) :=
    {L | (J : Submodule R R) ≤ L ∧ L ≤ (I : Submodule R R) ∧
      L ⊓ (K : Submodule R R) = (J : Submodule R R) ⊓ K}
  obtain ⟨L, hL, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := R) (M := R)).mpr inferInstance S ⟨J, le_rfl, hJI, rfl⟩
  refine ⟨L, hL.1, hL.2.1, le_antisymm (sup_le hL.2.1 hKI) fun x hxI => ?_, hL.2.2⟩
  by_contra hxnot
  have hMK : (L ⊔ Ideal.span {x}) ⊓ K = L ⊓ K := by
    refine le_antisymm (fun z hz => ?_) (inf_le_inf le_sup_left le_rfl)
    obtain ⟨a, haL, b, hbspan, hab⟩ := Submodule.mem_sup.mp
      (show (z : R) ∈ (L : Submodule R R) ⊔ (Ideal.span {x} : Submodule R R) from hz.1)
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hbspan
    by_cases hr : IsUnit r
    · have hmul : r * x ∈ L ⊔ K := by
        rw [show r * x = z - a by rw [← hab]; ring]
        exact (L ⊔ K).sub_mem (Ideal.mem_sup_right hz.2) (Ideal.mem_sup_left haL)
      exact (hxnot ((Ideal.unit_mul_mem_iff_mem _ hr).mp hmul)).elim
    · have hzero : r * x = 0 := by
        simpa [hann] using Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal r).2 hr) hxI
      have hzEq : z = a := by rw [← hab, mul_comm x r, hzero, add_zero]
      rw [hzEq] at hz ⊢
      exact ⟨haL, hz.2⟩
  have hMmem : L ⊔ Ideal.span {x} ∈ S :=
    ⟨hL.1.trans le_sup_left, sup_le hL.2.1 (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxI)),
      hMK.trans hL.2.2⟩
  exact hmax _ hMmem (SetLike.lt_iff_le_and_exists.mpr ⟨le_sup_left, x,
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self x), fun h => hxnot (Ideal.mem_sup_left h)⟩)

/-- In a category cofibered in groupoids, a morphism lying over `g` factors through the
pushforward along any factorization `g = c ≫ g'` of its image. -/
private theorem cofibered_pushforward
    {F : Type uF} [Category.{vF} F]
    {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p)
    {x y : F} {D D' : C} (g : D ⟶ p.obj x) (c : D ⟶ D')
    (g' : D' ⟶ p.obj x) (hcomp : c ≫ g' = g)
    (hy : p.obj y = D) (a : y ⟶ x)
    (hmap : p.map a = eqToHom hy ≫ g) :
    ∃ (y' : F) (hy' : p.obj y' = D') (b : y ⟶ y') (a' : y' ⟶ x),
      p.map b = eqToHom hy ≫ c ≫ eqToHom hy'.symm ∧
      b ≫ a' = a ∧ p.map a' = eqToHom hy' ≫ g' := by
  cases hy
  simp only [eqToHom_refl, Category.id_comp] at hmap
  have hm : p.IsHomLift (c ≫ g') a := by
    rw [hcomp, ← hmap]
    exact IsHomLift.map p a
  obtain ⟨y', b, a', hb, ha', hfac⟩ := exists_factor_of_isHomLift_comp hp c g' a hm
  refine ⟨y', IsHomLift.codomain_eq p c b, b, a', ?_, hfac, ?_⟩
  · simpa using IsHomLift.fac' p c b
  · simpa using IsHomLift.fac' p g' a'

/-- A map between two surjective presentations of objects of `𝒞_Λ` by the same ring, with the
kernel of the first inside the kernel of the second. -/
noncomputable def artinianFactorOfKerLe
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : Type*} [CommRing R] [Algebra Λ R]
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : R →ₐ[Λ] A) (g : R →ₐ[Λ] B) (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (hres : ∀ r, B.residueEquiv (residue B (g r)) = A.residueEquiv (residue A (f r)))
    (hker : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom) : A ⟶ B :=
  { hom := f.liftOfSurjective hf g hker
    isLocal := IsLocalHom.of_surjective _
      (AlgHom.liftOfSurjective_surjective f hf g hker hg)
    residue_comm := fun a ↦ by
      obtain ⟨r, rfl⟩ := hf a
      rw [AlgHom.liftOfSurjective_apply]
      exact hres r }

/-- The ideals of the kernel of a surjection `B ⟶ A` over whose quotients
an object over `A` lifts have a least member when (S1) holds. -/
@[stacks 06SZ]
theorem exists_least_lifting_ideal
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    {B : ArtinianLocalAlgCat.{u, v, w} Λ k} (x : F)
    (f : B ⟶ p.obj x) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal B * RingHom.ker f.hom.toRingHom = ⊥) :
    let lifts : Set (Ideal B) :=
      {J | J ≤ RingHom.ker f.hom.toRingHom ∧
        ∃ (C : ArtinianLocalAlgCat.{u, v, w} Λ k)
          (q : B ⟶ C) (g : C ⟶ p.obj x),
          Function.Surjective q.hom ∧
          RingHom.ker q.hom.toRingHom = J ∧
          q ≫ g = f ∧
          ∃ (y : F) (hy : p.obj y = C) (a : y ⟶ x),
            p.map a = eqToHom hy ≫ g};
    ∃ J : Ideal B, J ∈ lifts ∧ (∀ K : Ideal B, K ∈ lifts → J ≤ K) := by
  classical
  intro lifts
  have comp_apply : ∀ {C D : ArtinianLocalAlgCat.{u, v, w} Λ k} (u : B ⟶ C) (v : C ⟶ D)
      (w : B ⟶ D), u ≫ v = w → ∀ b, v.hom (u.hom b) = w.hom b := by
    rintro C D u v w rfl b
    simp [ArtinianLocalAlgCat.comp_hom]
  have liftUp : ∀ {L L' : Ideal B}, L ∈ lifts → L ≤ L' →
      L' ≤ RingHom.ker f.hom.toRingHom → L' ∈ lifts := by
    intro L L' hL hLL' hL'I
    obtain ⟨-, C, q, g, hq, hqker, hqg, y, hy, a, hmap⟩ := hL
    have hL'max : L' ≤ maximalIdeal B := hL'I.trans (ArtinianLocalAlgCat.ker_le_maximalIdeal f)
    let q' := ArtinianLocalAlgCat.idealQuotientProjection B L' hL'max
    let g' := ArtinianLocalAlgCat.idealQuotientFactor f hf L' hL'I hL'max
    have hq'g' : q' ≫ g' = f :=
      ArtinianLocalAlgCat.idealQuotientProjection_comp_idealQuotientFactor f hf L' hL'I hL'max
    have hq' : Function.Surjective q'.hom := fun z => by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨b, rfl⟩
    have hq'ker : RingHom.ker q'.hom.toRingHom = L' := by
      show RingHom.ker (Ideal.Quotient.mk L') = L'
      rw [Ideal.mk_ker]
    have hkerq : RingHom.ker q.hom.toRingHom ≤ RingHom.ker q'.hom.toRingHom :=
      hqker.le.trans (hLL'.trans hq'ker.ge)
    let c : C ⟶ _ := artinianFactorOfKerLe q.hom q'.hom hq hq'
      (fun b ↦ (q'.residue_comm b).trans (q.residue_comm b).symm) hkerq
    have hqc : q ≫ c = q' := ArtinianLocalAlgCat.hom_ext
      (AlgHom.ext fun b => AlgHom.liftOfSurjective_apply q.hom hq q'.hom hkerq b)
    have hccomp : c ≫ g' = g := by
      refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun z => ?_)
      obtain ⟨b, rfl⟩ := hq z
      exact (comp_apply q (c ≫ g') f (by rw [← Category.assoc, hqc, hq'g']) b).trans
        (comp_apply q g f hqg b).symm
    obtain ⟨y', hy', -, a', -, -, hamap⟩ := cofibered_pushforward hp g c g' hccomp hy a hmap
    exact ⟨hL'I, _, q', g', hq', hq'ker, hq'g', y', hy', a', hamap⟩
  have hnonempty : lifts.Nonempty :=
    ⟨RingHom.ker f.hom.toRingHom, le_rfl, p.obj x, f, 𝟙 _, hf, rfl, by simp, x, rfl, 𝟙 x,
      by simp⟩
  obtain ⟨J, hJ, hJmin⟩ :=
    IsArtinian.set_has_minimal (R := B) (M := B) lifts hnonempty
  refine ⟨J, hJ, fun K hK => ?_⟩
  obtain ⟨hKker, CK, qK, gK, hqK, hqKker, hqKg, yK, hyK, aK, hmapK⟩ := hK
  obtain ⟨J', hJJ', hJ'I, hsup, hinf⟩ :=
    exists_extension_with_sup_eq_of_product_bot _ J K hJ.1 hKker hI
  obtain ⟨-, CJ', qJ', gJ', hqJ', hqJ'ker, hqJ'g', yJ', hyJ', aJ', hmapJ'⟩ :=
    liftUp hJ hJJ' hJ'I
  cases hyJ'
  cases hyK
  simp only [eqToHom_refl, Category.id_comp] at hmapJ' hmapK
  have hKf := comp_apply qK gK f hqKg
  have hJf := comp_apply qJ' gJ' f hqJ'g'
  have hgK : Function.Surjective gK.hom := fun a => by
    obtain ⟨b, rfl⟩ := hf a
    exact ⟨qK.hom b, hKf b⟩
  let fst := ArtinianLocalAlgCat.pullbackFst_of_surjective gK gJ' (Or.inl hgK)
  let snd := ArtinianLocalAlgCat.pullbackSnd_of_surjective gK gJ' (Or.inl hgK)
  have hpb : IsPullback fst snd gK gJ' :=
    ArtinianLocalAlgCat.isPullback_of_surjective gK gJ' (Or.inl hgK)
  obtain ⟨pc⟩ := hS1.completion aJ' aK (by simpa [hmapK] using hgK) snd fst
    (by simpa [hmapK, hmapJ'] using hpb)
  obtain ⟨r, hrsurj, hrker, hrfst⟩ :
      ∃ r : B ⟶ ArtinianLocalAlgCat.pullbackObj_of_surjective gK gJ' (Or.inl hgK),
        Function.Surjective r.hom ∧ RingHom.ker r.hom.toRingHom = J' ⊓ K ∧
        r ≫ fst = qK := by
    let P := ArtinianLocalAlgCat.pullbackObj_of_surjective gK gJ' (Or.inl hgK)
    let rHom : B →ₐ[Λ] P := by
      show B →ₐ[Λ] AlgHom.pullback gK.hom gJ'.hom
      exact AlgHom.codRestrict (AlgHom.prod qK.hom qJ'.hom)
        (AlgHom.pullback gK.hom gJ'.hom) (fun b => by
          show gK.hom (qK.hom b) = gJ'.hom (qJ'.hom b)
          exact (hKf b).trans (hJf b).symm)
    have hfst (b : B) :
        (ArtinianLocalAlgCat.pullbackFst_of_surjective gK gJ' (Or.inl hgK)).hom (rHom b) =
          qK.hom b := by
      rw [ArtinianLocalAlgCat.pullbackFst_of_surjective_hom]
      rfl
    have hsurj : Function.Surjective rHom := by
      rintro ⟨⟨zK, zJ⟩, hz⟩
      obtain ⟨bK, rfl⟩ := hqK zK
      obtain ⟨bJ, rfl⟩ := hqJ' zJ
      have hd : bK - bJ ∈ (J' : Submodule B B) ⊔ K := by
        rw [hsup]
        show f.hom (bK - bJ) = 0
        rw [map_sub, ← hKf, ← hJf, sub_eq_zero]
        exact hz
      obtain ⟨j, hj, k₀, hk₀, hdiff⟩ := Submodule.mem_sup.mp hd
      have hkzero : qK.hom k₀ = 0 := RingHom.mem_ker.mp (hqKker.ge hk₀)
      have hjzero : qJ'.hom j = 0 := RingHom.mem_ker.mp (hqJ'ker.ge hj)
      refine ⟨bK - k₀, Subtype.ext (Prod.ext ?_ ?_)⟩
      · show qK.hom (bK - k₀) = qK.hom bK
        rw [map_sub, hkzero, sub_zero]
      · show qJ'.hom (bK - k₀) = qJ'.hom bJ
        rw [show bK - k₀ = bJ + j by linear_combination -hdiff, map_add, hjzero, add_zero]
    have hker : RingHom.ker rHom.toRingHom = J' ⊓ K := by
      ext b
      refine ⟨fun hb => Ideal.mem_inf.mpr ⟨?_, ?_⟩, fun hb => RingHom.mem_ker.mpr (Subtype.ext ?_)⟩
      · rw [← hqJ'ker, RingHom.mem_ker]
        have h := congrArg (AlgHom.pullbackSnd gK.hom gJ'.hom) (RingHom.mem_ker.mp hb)
        have hz0 : AlgHom.pullbackSnd gK.hom gJ'.hom (0 : P) = 0 := rfl
        exact h.trans hz0
      · rw [← hqKker, RingHom.mem_ker]
        have h := congrArg (AlgHom.pullbackFst gK.hom gJ'.hom) (RingHom.mem_ker.mp hb)
        have hz0 : AlgHom.pullbackFst gK.hom gJ'.hom (0 : P) = 0 := rfl
        exact h.trans hz0
      · show (qK.hom b, qJ'.hom b) = (0, 0)
        exact Prod.ext (RingHom.mem_ker.mp (hqKker.ge hb.2)) (RingHom.mem_ker.mp (hqJ'ker.ge hb.1))
    refine ⟨{ hom := rHom
              isLocal := IsLocalHom.of_surjective rHom.toRingHom hsurj
              residue_comm := fun b => ?_ }, hsurj, hker,
      ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun b => hfst b)⟩
    calc
      P.residueEquiv (residue P (rHom b)) =
          (p.obj yK).residueEquiv (residue (p.obj yK)
            ((ArtinianLocalAlgCat.pullbackFst_of_surjective gK gJ' (Or.inl hgK)).hom (rHom b))) :=
        ((ArtinianLocalAlgCat.pullbackFst_of_surjective gK gJ' (Or.inl hgK)).residue_comm _).symm
      _ = B.residueEquiv (residue B b) := by rw [hfst]; exact qK.residue_comm b
  have hJmeet : J' ⊓ K ∈ lifts :=
    ⟨inf_le_right.trans hKker, _, r, fst ≫ gK, hrsurj, hrker,
      by rw [← Category.assoc, hrfst, hqKg], pc.apex, pc.apex_eq, pc.toSecond ≫ aK,
      by rw [Functor.map_comp, pc.map_toSecond, hmapK]; simp [fst]⟩
  exact (eq_of_le_of_not_lt (hinf.le.trans inf_le_left) (hJmin _ hJmeet)).symm.le.trans
    inf_le_right

end Deformation

end
