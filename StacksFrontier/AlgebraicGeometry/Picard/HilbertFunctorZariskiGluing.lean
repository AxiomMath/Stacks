module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.IdealSheafZariskiGluing
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf

/-!
# Zariski gluing of Hilbert families

Let `X` be a scheme over `S` and `d` a natural number. This file proves the Zariski half of the
gluing clause of Stacks 0B95: degree-`d` Hilbert families in `X` over the members of an open
covering of an `S`-scheme `T` which agree on overlaps glue uniquely to a family over `T`. It then
packages the Hilbert functor as a presheaf on the category of *all* schemes, the form in which
Mathlib's representability criterion `AlgebraicGeometry.Scheme.LocalRepresentability` (Stacks
01JJ) applies, and proves that this presheaf is a Zariski sheaf.

## Main definitions

* `Stacks.Hilbert.TotalFamily X d T`: pairs of a morphism `t : T ⟶ S` and a degree-`d` Hilbert
  family over `T` viewed as an `S`-scheme through `t`.
* `Stacks.Hilbert.hilbertTotalPresheaf X d`: the presheaf `T ↦ TotalFamily X d T` on all schemes.

## Main results

* `Stacks.Hilbert.HilbertFamily.exists_baseChange_eq_of_isOpenImmersion`: **Zariski gluing** of
  Hilbert families.
* `Stacks.Hilbert.HilbertFamily.eq_of_baseChange_eq_of_isOpenImmersion`: uniqueness of the glued
  family.
* `Stacks.Hilbert.isSheaf_hilbertTotalPresheaf`: `hilbertTotalPresheaf X d` is a sheaf for the
  Zariski topology on schemes.

## Implementation notes

The ideal sheaves glue by
`AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_isOpenImmersion`, along the open
immersions `X ×_S U i ⟶ X ×_S T`; the overlap condition there is on the fibre products of these
open immersions, and `exists_fac_pullback` converts it into the overlap condition on `U i ×_T U j`.
Finite local freeness of rank `d` of the glued family is Zariski local on `T`
(`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_isZariskiLocalAtTarget`), checked on the
cartesian squares `Stacks.Hilbert.isPullback_familyBaseChangeMap_subschemeι`.

The elements of `hilbertTotalPresheaf X d` are dependent pairs, and two such pairs with
propositionally equal structure morphisms are compared through base change along an identity
morphism (`Stacks.Hilbert.totalFamily_mk_eq_iff`), which keeps every comparison inside the
`Stacks.Hilbert.baseChange` calculus rather than in `HEq`.

## References

* [Stacks Project, Tag 0B95](https://stacks.math.columbia.edu/tag/0B95)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- A property of morphisms which is local at the target holds for `f` as soon as it holds for
some base change of `f` along each member of a jointly surjective family of open immersions. -/
theorem AlgebraicGeometry.IsZariskiLocalAtTarget.of_forall_isPullback
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P] {X Y : Scheme.{u}}
    (f : X ⟶ Y) {ι : Type*} {U X' : ι → Scheme.{u}} (g : ∀ i, U i ⟶ Y)
    [∀ i, IsOpenImmersion (g i)] (hg : ∀ y : Y, ∃ i, ∃ u : U i, g i u = y)
    (fst : ∀ i, X' i ⟶ X) (f' : ∀ i, X' i ⟶ U i) (h : ∀ i, IsPullback (fst i) (f' i) f (g i))
    (H : ∀ i, P (f' i)) : P f := by
  refine of_forall_exists_morphismRestrict fun y ↦ ?_
  obtain ⟨i, u, rfl⟩ := hg y
  refine ⟨(g i).opensRange, ⟨u, rfl⟩, ?_⟩
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange f (g i))).mpr ?_
  rw [← (h i).isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso _ _).mpr (H i)

namespace Stacks.Hilbert

variable {S : Scheme.{u}} (X : Over S) {d : ℕ}

/-- The base change `X ×_S T' ⟶ X ×_S T` of an open immersion `T' ⟶ T` is an open immersion. -/
instance isOpenImmersion_familyBaseChangeMap {T' T : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] : IsOpenImmersion (familyBaseChangeMap X g) :=
  MorphismProperty.of_isPullback (isPullback_familyBaseChangeMap X g).flip inferInstance

/-- The first component of `familyBaseChangeMap`: it is compatible with the projections to
`X`. -/
@[reassoc (attr := simp)]
theorem familyBaseChangeMap_fst {T' T : Over S} (g : T' ⟶ T) :
    familyBaseChangeMap X g ≫ pullback.fst X.hom T.hom = pullback.fst X.hom T'.hom :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The second component of `familyBaseChangeMap`: it lies over `g`. -/
@[reassoc (attr := simp)]
theorem familyBaseChangeMap_snd {T' T : Over S} (g : T' ⟶ T) :
    familyBaseChangeMap X g ≫ pullback.snd X.hom T.hom = pullback.snd X.hom T'.hom ≫ g.left :=
  pullback.lift_snd _ _ _

/-- The base changes of `X ×_S T` along a jointly surjective family of morphisms to `T` are
jointly surjective onto `X ×_S T`. -/
theorem familyBaseChangeMap_jointlySurjective {T : Over S} {ι : Type*} {U : ι → Over S}
    (g : ∀ i, U i ⟶ T) (hg : ∀ t : T.left, ∃ i, ∃ u : (U i).left, (g i).left u = t)
    (w : ((Over.pullback T.hom).obj X).left) :
    ∃ i, ∃ v : ((Over.pullback (U i).hom).obj X).left, familyBaseChangeMap X (g i) v = w := by
  obtain ⟨i, y, hy⟩ := hg (((Over.pullback T.hom).obj X).hom w)
  exact ⟨i, exists_preimage_of_isPullback (isPullback_familyBaseChangeMap X (g i)) w y hy.symm⟩

/-- **Uniqueness in the Zariski sheaf property of the Hilbert functor.** Two Hilbert families
over `T` with the same base changes to the members of a Zariski covering of `T` are equal. -/
theorem HilbertFamily.eq_of_baseChange_eq_of_isOpenImmersion {T : Over S} {ι : Type*}
    {U : ι → Over S} (g : ∀ i, U i ⟶ T) [∀ i, IsOpenImmersion (g i).left]
    (hg : ∀ t : T.left, ∃ i, ∃ u : (U i).left, (g i).left u = t)
    {Z W : HilbertFamily X T d} (h : ∀ i, baseChange X (g i) Z = baseChange X (g i) W) :
    Z = W :=
  hilbertFamily_ext_of_baseChange_eq X g (fun _ ↦ inferInstance) hg h

/-- The base changes of `X ×_S U` along `a : W ⟶ U i` and `b : W ⟶ U j` factor the two
projections of the fibre product `(X ×_S U i) ×_{X ×_S T} (X ×_S U j)`, where `W` is the fibre
product `U i ×_T U j`. -/
private theorem exists_fac_pullback {T : Over S} {U₁ U₂ : Over S} (g₁ : U₁ ⟶ T)
    (g₂ : U₂ ⟶ T) :
    ∃ (W : Over S) (a : W ⟶ U₁) (b : W ⟶ U₂)
      (φ : pullback (familyBaseChangeMap X g₁) (familyBaseChangeMap X g₂) ⟶
        ((Over.pullback W.hom).obj X).left),
      a ≫ g₁ = b ≫ g₂ ∧ φ ≫ familyBaseChangeMap X a = pullback.fst _ _ ∧
        φ ≫ familyBaseChangeMap X b = pullback.snd _ _ := by
  have hc := pullback.condition (f := familyBaseChangeMap X g₁) (g := familyBaseChangeMap X g₂)
  have hfst := congrArg (· ≫ pullback.fst X.hom T.hom) hc
  have hsnd := congrArg (· ≫ pullback.snd X.hom T.hom) hc
  simp only [Category.assoc, familyBaseChangeMap_fst, familyBaseChangeMap_snd] at hfst hsnd
  set a' := pullback.fst (familyBaseChangeMap X g₁) (familyBaseChangeMap X g₂) ≫
    pullback.snd X.hom U₁.hom with ha'
  set b' := pullback.snd (familyBaseChangeMap X g₁) (familyBaseChangeMap X g₂) ≫
    pullback.snd X.hom U₂.hom with hb'
  have hab : a' ≫ g₁.left = b' ≫ g₂.left := by simpa only [ha', hb', Category.assoc] using hsnd
  have hw : b' ≫ U₂.hom = a' ≫ U₁.hom := by
    simpa only [Category.assoc, Over.w] using (congrArg (· ≫ T.hom) hab).symm
  refine ⟨Over.mk (a' ≫ U₁.hom), Over.homMk a' rfl, Over.homMk b' hw,
    pullback.lift (pullback.fst _ _ ≫ pullback.fst X.hom U₁.hom) (𝟙 _)
      (by simp only [Category.assoc, pullback.condition, Category.id_comp, Over.mk_hom, ha']),
    ?_, ?_, ?_⟩
  · ext
    simpa using hab
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, familyBaseChangeMap_fst, pullback.lift_fst]
    · simp only [Category.assoc, familyBaseChangeMap_snd, pullback.lift_snd_assoc,
        Category.id_comp, Over.homMk_left, ha']
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, familyBaseChangeMap_fst, pullback.lift_fst, hfst]
    · simp only [Category.assoc, familyBaseChangeMap_snd, pullback.lift_snd_assoc,
        Category.id_comp, Over.homMk_left, hb']

/-- **Stacks Project, Tag 0B95, Zariski gluing.** Degree-`d` Hilbert families over the members
of a Zariski covering `{U i ⟶ T}` which agree on overlaps glue to a family over `T`. -/
theorem HilbertFamily.exists_baseChange_eq_of_isOpenImmersion {T : Over S} {ι : Type*}
    {U : ι → Over S} (g : ∀ i, U i ⟶ T) [∀ i, IsOpenImmersion (g i).left]
    (hg : ∀ t : T.left, ∃ i, ∃ u : (U i).left, (g i).left u = t)
    (Z : ∀ i, HilbertFamily X (U i) d)
    (hZ : ∀ (W : Over S) (i j : ι) (a : W ⟶ U i) (b : W ⟶ U j), a ≫ g i = b ≫ g j →
      baseChange X a (Z i) = baseChange X b (Z j)) :
    ∃ Z' : HilbertFamily X T d, ∀ i, baseChange X (g i) Z' = Z i := by
  obtain ⟨I, hI⟩ := Scheme.IdealSheafData.exists_comap_eq_of_isOpenImmersion
    (fun i ↦ familyBaseChangeMap X (g i)) (familyBaseChangeMap_jointlySurjective X g hg)
    (fun i ↦ (Z i).ideal) fun i j ↦ by
      obtain ⟨W, a, b, φ, hab, ha, hb⟩ := exists_fac_pullback X (g i) (g j)
      rw [← ha, ← hb, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
        ← baseChange_ideal, ← baseChange_ideal, hZ W i j a b hab]
  refine ⟨⟨I, ?_⟩, fun i ↦ HilbertFamily.ext (hI i)⟩
  refine IsZariskiLocalAtTarget.of_forall_isPullback
    (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d) _ (fun i ↦ (g i).left) hg _ _
    (fun i ↦ isPullback_familyBaseChangeMap_subschemeι X (g i) I) fun i ↦ ?_
  have := (Z i).isFiniteLocallyFreeOfRank
  simp only [Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff]
  rw [hI i]
  infer_instance

/-! ### The Hilbert functor as a presheaf on all schemes -/

/-- Base change of a Hilbert family along a morphism of `S`-schemes only depends on the
underlying morphism of schemes. -/
theorem baseChange_congr {T' T : Over S} {f f' : T' ⟶ T} (h : f.left = f'.left)
    (Z : HilbertFamily X T d) : baseChange X f Z = baseChange X f' Z := by
  rw [Over.OverMorphism.ext h]

/-- The type of degree-`d` Hilbert families over a scheme `T` together with a structure morphism
`T ⟶ S`: the value at `T` of `Stacks.Hilbert.hilbertTotalPresheaf`. -/
abbrev TotalFamily (X : Over S) (d : ℕ) (T : Scheme.{u}) : Type u :=
  Σ t : T ⟶ S, HilbertFamily X (Over.mk t) d

/-- Two base changes of one family, along morphisms with the same underlying morphism of schemes,
define the same element of `TotalFamily`. -/
theorem totalFamily_mk_baseChange_eq {T : Scheme.{u}} {t t' : T ⟶ S} {T₀ : Over S}
    (f : Over.mk t ⟶ T₀) (f' : Over.mk t' ⟶ T₀) (hf : f.left = f'.left)
    (Z : HilbertFamily X T₀ d) :
    (⟨t, baseChange X f Z⟩ : TotalFamily X d T) = ⟨t', baseChange X f' Z⟩ := by
  obtain rfl : t = t' := by
    have h₁ := Over.w f
    have h₂ := Over.w f'
    simp only [Over.mk_hom] at h₁ h₂
    rw [← h₁, ← h₂, hf]
  rw [baseChange_congr X hf]

/-- Equality in `TotalFamily`: two elements are equal when their structure morphisms agree and
the families agree after the identification of the two `S`-schemes. -/
theorem totalFamily_mk_eq_iff {T : Scheme.{u}} {t t' : T ⟶ S} (h : t = t')
    (Z : HilbertFamily X (Over.mk t) d) (Z' : HilbertFamily X (Over.mk t') d) :
    (⟨t, Z⟩ : TotalFamily X d T) = ⟨t', Z'⟩ ↔
      baseChange X (Over.homMk (𝟙 T) (by simp [h]) : Over.mk t' ⟶ Over.mk t) Z = Z' := by
  subst h
  have e : (Over.homMk (𝟙 T) (by simp) : Over.mk t ⟶ Over.mk t) = 𝟙 _ := by ext; simp
  rw [e, baseChange_id]
  exact ⟨fun e ↦ eq_of_heq (Sigma.mk.inj e).2, fun e ↦ e ▸ rfl⟩

/-- Two families whose pullbacks along `a.left` and `b.left` define the same element of
`TotalFamily` have equal base changes along `a` and `b`. -/
private theorem baseChange_eq_of_totalFamily_mk_eq {W : Over S} {T₁ T₂ : Scheme.{u}} {t₁ : T₁ ⟶ S}
    {t₂ : T₂ ⟶ S} {Z₁ : HilbertFamily X (Over.mk t₁) d} {Z₂ : HilbertFamily X (Over.mk t₂) d}
    (a : W ⟶ Over.mk t₁) (b : W ⟶ Over.mk t₂)
    (e : (⟨a.left ≫ t₁, baseChange X (Over.homMk a.left rfl : Over.mk (a.left ≫ t₁) ⟶ _) Z₁⟩ :
        TotalFamily X d W.left) =
      ⟨b.left ≫ t₂, baseChange X (Over.homMk b.left rfl : Over.mk (b.left ≫ t₂) ⟶ _) Z₂⟩) :
    baseChange X a Z₁ = baseChange X b Z₂ := by
  have e₀ : ∀ {T₃ : Scheme.{u}} {t₃ : T₃ ⟶ S} (c : W ⟶ Over.mk t₃)
      (Z : HilbertFamily X (Over.mk t₃) d), baseChange X c Z =
      baseChange X (Over.homMk (𝟙 W.left) (by simp [← Over.w c]) : W ⟶ Over.mk (c.left ≫ t₃))
        (baseChange X (Over.homMk c.left rfl : Over.mk (c.left ≫ t₃) ⟶ _) Z) := by
    intro _ _ c Z
    rw [← baseChange_comp]
    exact baseChange_congr X (by simp) _
  rw [e₀ a, e₀ b, ← (totalFamily_mk_eq_iff X (congrArg Sigma.fst e) _ _).mp e]
  simp only [← baseChange_comp]
  exact baseChange_congr X (by simp) _

/-- **The degree-`d` Hilbert functor as a presheaf on all schemes.** It sends a scheme `T` to the
pairs of a morphism `t : T ⟶ S` and a degree-`d` Hilbert family in `X` over `T`, viewed as an
`S`-scheme through `t`; a morphism acts by composition and base change. -/
def hilbertTotalPresheaf (X : Over S) (d : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := TotalFamily X d T.unop
  map g := ↾fun x ↦ ⟨g.unop ≫ x.1,
    baseChange X (Over.homMk g.unop rfl : Over.mk (g.unop ≫ x.1) ⟶ Over.mk x.1) x.2⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    rintro ⟨t, Z⟩
    conv_rhs => rw [← baseChange_id X Z]
    exact totalFamily_mk_baseChange_eq X _ _ (by simp) Z
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    rintro ⟨t, Z⟩
    change _ = (⟨_, baseChange X _ (baseChange X _ Z)⟩ : TotalFamily X d _)
    rw [← baseChange_comp]
    exact totalFamily_mk_baseChange_eq X _ _ (by simp) Z

/-- The action of `hilbertTotalPresheaf` on morphisms. -/
theorem hilbertTotalPresheaf_map_apply {T' T : Scheme.{u}} (g : T' ⟶ T) (t : T ⟶ S)
    (Z : HilbertFamily X (Over.mk t) d) :
    (hilbertTotalPresheaf X d).map g.op ⟨t, Z⟩ =
      ⟨g ≫ t, baseChange X (Over.homMk g rfl : Over.mk (g ≫ t) ⟶ Over.mk t) Z⟩ :=
  rfl

/-- Two elements of `TotalFamily X d Y` with the same restrictions to the members of an open cover
of `Y` are equal. -/
private theorem totalFamily_ext_of_openCover {Y : Scheme.{u}} (𝒰 : Y.OpenCover)
    {p q : TotalFamily X d Y}
    (h : ∀ i, (hilbertTotalPresheaf X d).map (𝒰.f i).op p =
      (hilbertTotalPresheaf X d).map (𝒰.f i).op q) : p = q := by
  obtain ⟨t, Z⟩ := p
  obtain ⟨t', W⟩ := q
  obtain rfl : t = t' := 𝒰.hom_ext _ _ fun i ↦ congrArg Sigma.fst (h i)
  have : ∀ i, IsOpenImmersion
      (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ t) ⟶ Over.mk t).left := fun i ↦ 𝒰.map_prop i
  exact congrArg (Sigma.mk t) <| HilbertFamily.eq_of_baseChange_eq_of_isOpenImmersion X
    (fun i ↦ (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ t) ⟶ Over.mk t)) 𝒰.exists_eq
    fun i ↦ eq_of_heq (Sigma.mk.inj (h i)).2

/-- **Stacks Project, Tag 0B95, the Zariski sheaf property.** The degree-`d` Hilbert functor,
viewed as a presheaf on all schemes through `Stacks.Hilbert.hilbertTotalPresheaf`, is a sheaf
for the Zariski topology. -/
theorem isSheaf_hilbertTotalPresheaf (X : Over S) (d : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (hilbertTotalPresheaf X d) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y R hR
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hR
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let t : Y ⟶ S := 𝒰.glueMorphisms (fun i ↦ (x i).1) fun i j ↦
    congrArg Sigma.fst (hx i j _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition)
  have ht (i : 𝒰.I₀) : 𝒰.f i ≫ t = (x i).1 := 𝒰.ι_glueMorphisms _ _ i
  let g (i : 𝒰.I₀) : Over.mk (𝒰.f i ≫ t) ⟶ Over.mk t := Over.homMk (𝒰.f i) rfl
  have : ∀ i, IsOpenImmersion (g i).left := fun i ↦ 𝒰.map_prop i
  let ψ (i : 𝒰.I₀) : Over.mk (𝒰.f i ≫ t) ⟶ Over.mk (x i).1 :=
    Over.homMk (𝟙 _) (by simp [ht])
  let Z (i : 𝒰.I₀) : HilbertFamily X (Over.mk (𝒰.f i ≫ t)) d := baseChange X (ψ i) (x i).2
  have hZ (W : Over S) (i j : 𝒰.I₀) (a : W ⟶ Over.mk (𝒰.f i ≫ t))
      (b : W ⟶ Over.mk (𝒰.f j ≫ t)) (hab : a ≫ g i = b ≫ g j) :
      baseChange X a (Z i) = baseChange X b (Z j) := by
    simp only [Z, ← baseChange_comp]
    exact baseChange_eq_of_totalFamily_mk_eq X _ _ <|
      hx i j W.left _ _ (by simpa [ψ, g] using congrArg CommaMorphism.left hab)
  obtain ⟨Z', hZ'⟩ :=
    HilbertFamily.exists_baseChange_eq_of_isOpenImmersion X g 𝒰.exists_eq Z hZ
  have key (i : 𝒰.I₀) : (hilbertTotalPresheaf X d).map (𝒰.f i).op ⟨t, Z'⟩ = x i := by
    rw [hilbertTotalPresheaf_map_apply]
    change (⟨𝒰.f i ≫ t, baseChange X (g i) Z'⟩ : TotalFamily X d _) = ⟨(x i).1, (x i).2⟩
    rw [hZ' i]
    conv_rhs => rw [← baseChange_id X (x i).2]
    exact totalFamily_mk_baseChange_eq X (ψ i) (𝟙 _) (by simp [ψ]) _
  exact ⟨⟨t, Z'⟩, key, fun y hy ↦ totalFamily_ext_of_openCover X 𝒰 fun i ↦
    (hy i).trans (key i).symm⟩

end Stacks.Hilbert

end
