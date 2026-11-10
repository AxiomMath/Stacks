module

public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive

/-!
# The kernel pair of a morphism out of a coproduct of sheaves of sets

Let `V = ∐ᵢ Aᵢ` be a coproduct of sheaves of sets, let `φ : V ⟶ Z` be a morphism, and let
`Cᵢⱼ = Aᵢ ×_Z Aⱼ`. Since coproducts of sheaves of sets are universal and disjoint, the kernel
pair `V ×_Z V` is the coproduct `∐ᵢⱼ Cᵢⱼ`. This file records that statement in the form used to
glue spaces along a covering: given any coproduct `R = ∐ᵢⱼ Cᵢⱼ` and maps `t, s : R ⟶ V`
restricting to the two projections of `Cᵢⱼ`, the square `(t, s, φ, φ)` is cartesian.

## Main results

* `CategoryTheory.Limits.isColimitCofanProd`: a coproduct over `i` of coproducts over `j` is a
  coproduct over the pairs `(i, j)`.
* `CategoryTheory.Sheaf.isPullback_of_isColimit_cofan`: the kernel pair statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe w v' v u

namespace Limits

variable {A : Type u} [Category.{v} A]

/-- **A coproduct over `i` of coproducts over `j` is a coproduct over the pairs `(i, j)`.**
Its injection at `(i, j)` is the `j`-th injection into the `i`-th summand followed by the
`i`-th injection. -/
noncomputable def isColimitCofanProd {ι κ : Type*} {F : ι × κ → A} {P : ι → A}
    {c : ∀ i j, F (i, j) ⟶ P i} (hP : ∀ i, IsColimit (Cofan.mk (P i) (c i)))
    {Z : A} {a : ∀ i, P i ⟶ Z} (hZ : IsColimit (Cofan.mk Z a)) :
    IsColimit (Cofan.mk Z (fun p : ι × κ ↦ c p.1 p.2 ≫ a p.1)) := by
  refine Cofan.IsColimit.mk _
    (fun s ↦ Cofan.IsColimit.desc hZ
      (fun i ↦ Cofan.IsColimit.desc (hP i) (fun j ↦ s.inj (i, j))))
    (fun s p ↦ ?_) (fun s n hn ↦ Cofan.IsColimit.hom_ext hZ _ _ fun i ↦ ?_)
  · obtain ⟨i, j⟩ := p
    have h1 : a i ≫ Cofan.IsColimit.desc hZ
        (fun i ↦ Cofan.IsColimit.desc (hP i) (fun j ↦ s.inj (i, j))) =
          Cofan.IsColimit.desc (hP i) (fun j ↦ s.inj (i, j)) := Cofan.IsColimit.fac hZ _ i
    change (c i j ≫ a i) ≫ _ = _
    rw [Category.assoc, h1]
    exact Cofan.IsColimit.fac (hP i) (fun j ↦ s.inj (i, j)) j
  · have h1 : a i ≫ Cofan.IsColimit.desc hZ
        (fun i ↦ Cofan.IsColimit.desc (hP i) (fun j ↦ s.inj (i, j))) =
          Cofan.IsColimit.desc (hP i) (fun j ↦ s.inj (i, j)) := Cofan.IsColimit.fac hZ _ i
    change a i ≫ _ = a i ≫ _
    rw [h1]
    refine Cofan.IsColimit.hom_ext (hP i) _ _ fun j ↦ ?_
    have h2 : c i j ≫ Cofan.IsColimit.desc (hP i) (fun j ↦ s.inj (i, j)) = s.inj (i, j) :=
      Cofan.IsColimit.fac (hP i) (fun j ↦ s.inj (i, j)) j
    change c i j ≫ _ = c i j ≫ _
    rw [h2, ← Category.assoc]
    exact hn (i, j)

end Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasSheafify J (Type w)]

/-- **The kernel pair of a morphism out of a coproduct of sheaves of sets.** Let
`V = ∐ᵢ Aᵢ` and `R = ∐ᵢⱼ Cᵢⱼ` be coproducts of sheaves of sets, let `φ : V ⟶ Z`, and let each
`Cᵢⱼ` be the fibre product `Aᵢ ×_Z Aⱼ` with projections `fst`, `snd`. If `t, s : R ⟶ V`
restrict on `Cᵢⱼ` to `fst` and `snd` followed by the injections, then `R` is the kernel pair of
`φ` with projections `t` and `s`.

Universality of coproducts of sheaves
(`CategoryTheory.Sheaf.nonempty_isColimit_cofanMk_of_isPullback`) decomposes `V ×_Z V` as the
coproduct of the `Aᵢ ×_Z V`, and each of these as the coproduct of the `Cᵢⱼ`; the comparison map
`R ⟶ V ×_Z V` is then a morphism between two coproducts of the same family, matching the
injections, hence an isomorphism. -/
theorem Sheaf.isPullback_of_isColimit_cofan {ι : Type v'} [Small.{w} ι]
    {A : ι → Sheaf J (Type w)} {V : Sheaf J (Type w)} (ιV : ∀ i, A i ⟶ V)
    (hV : IsColimit (Cofan.mk V ιV)) {Cij : ι × ι → Sheaf J (Type w)} {R : Sheaf J (Type w)}
    (κ : ∀ p, Cij p ⟶ R) (hR : IsColimit (Cofan.mk R κ)) {Z : Sheaf J (Type w)} (φ : V ⟶ Z)
    (fst : ∀ p, Cij p ⟶ A p.1) (snd : ∀ p, Cij p ⟶ A p.2)
    (hsq : ∀ p, IsPullback (fst p) (snd p) (ιV p.1 ≫ φ) (ιV p.2 ≫ φ))
    (t s : R ⟶ V) (ht : ∀ p, κ p ≫ t = fst p ≫ ιV p.1) (hs : ∀ p, κ p ≫ s = snd p ≫ ιV p.2) :
    IsPullback t s φ φ := by
  -- the pieces `Aᵢ ×_Z V` of `V ×_Z V`
  let a : ∀ i, pullback (ιV i ≫ φ) φ ⟶ pullback φ φ := fun i ↦
    pullback.lift (pullback.fst _ _ ≫ ιV i) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition])
  have ha : ∀ i, IsPullback (a i) (pullback.fst (ιV i ≫ φ) φ) (pullback.fst φ φ) (ιV i) := by
    intro i
    refine IsPullback.of_right (h₁₂ := pullback.snd φ φ) (v₁₃ := φ) (h₂₂ := φ) ?_
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback φ φ).flip
    rw [show a i ≫ pullback.snd φ φ = pullback.snd (ιV i ≫ φ) φ from pullback.lift_snd _ _ _]
    exact (IsPullback.of_hasPullback (ιV i ≫ φ) φ).flip
  have hPcolim : IsColimit (Cofan.mk (pullback φ φ) a) :=
    (Sheaf.nonempty_isColimit_cofanMk_of_isPullback J ιV hV (pullback.fst φ φ) a _ ha).some
  -- the pieces `Cᵢⱼ` of `Aᵢ ×_Z V`
  let c : ∀ i j, Cij (i, j) ⟶ pullback (ιV i ≫ φ) φ := fun i j ↦
    pullback.lift (fst (i, j)) (snd (i, j) ≫ ιV j) (by simpa using (hsq (i, j)).w)
  have hc : ∀ i j, IsPullback (c i j) (snd (i, j)) (pullback.snd (ιV i ≫ φ) φ) (ιV j) := by
    intro i j
    refine IsPullback.of_right (h₁₂ := pullback.fst (ιV i ≫ φ) φ) (v₁₃ := ιV i ≫ φ)
      (h₂₂ := φ) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [show c i j ≫ pullback.fst (ιV i ≫ φ) φ = fst (i, j) from pullback.lift_fst _ _ _]
    exact hsq (i, j)
  have hPi : ∀ i, IsColimit (Cofan.mk (pullback (ιV i ≫ φ) φ) (c i)) := fun i ↦
    (Sheaf.nonempty_isColimit_cofanMk_of_isPullback J ιV hV (pullback.snd (ιV i ≫ φ) φ)
      (c i) (fun j ↦ snd (i, j)) (hc i)).some
  have hP := Limits.isColimitCofanProd (F := Cij) hPi hPcolim
  -- the comparison map `R ⟶ V ×_Z V`
  have hw : t ≫ φ = s ≫ φ := Cofan.IsColimit.hom_ext hR _ _ fun p ↦ by
    change κ p ≫ t ≫ φ = κ p ≫ s ≫ φ
    rw [reassoc_of% ht, reassoc_of% hs]
    exact (hsq p).w
  let k : R ⟶ pullback φ φ := pullback.lift t s hw
  have hk : ∀ p, κ p ≫ k = c p.1 p.2 ≫ a p.1 := by
    rintro ⟨i, j⟩
    have ha₁ : a i ≫ pullback.fst φ φ = pullback.fst (ιV i ≫ φ) φ ≫ ιV i :=
      pullback.lift_fst _ _ _
    have hc₁ : c i j ≫ pullback.fst (ιV i ≫ φ) φ = fst (i, j) := pullback.lift_fst _ _ _
    have ha₂ : a i ≫ pullback.snd φ φ = pullback.snd (ιV i ≫ φ) φ := pullback.lift_snd _ _ _
    have hc₂ : c i j ≫ pullback.snd (ιV i ≫ φ) φ = snd (i, j) ≫ ιV j := pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ht, Category.assoc, ha₁, ← Category.assoc, hc₁]
    · rw [Category.assoc, pullback.lift_snd, hs, Category.assoc, ha₂, hc₂]
  have he : k = (hR.coconePointUniqueUpToIso hP).hom :=
    Cofan.IsColimit.hom_ext hR _ _ fun p ↦
      (hk p).trans (hR.comp_coconePointUniqueUpToIso_hom hP ⟨p⟩).symm
  have : IsIso k := he ▸ inferInstance
  exact .of_iso_pullback ⟨hw⟩ (asIso k) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end CategoryTheory

end
