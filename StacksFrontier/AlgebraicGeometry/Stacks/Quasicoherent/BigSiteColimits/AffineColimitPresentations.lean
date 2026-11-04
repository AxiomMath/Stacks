module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCechSheafCondition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.ColimitsClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits

/-!
# Global presentations are closed under colimits on an affine slice

A sheaf of modules has a global presentation, in the sense of [Stacks, Tag 03DE] (6), when it is
the cokernel of a map between coproducts of copies of the structure sheaf. This file proves that on
the slice site at an affine object of the fppf site associated with a category fibred in groupoids
over a big fppf category of schemes, global presentations are closed under colimits of small shape:
the condition `AlgebraicGeometry.FibredSite.HasAffineColimitPresentations`.

## Main results

* `CategoryTheory.Limits.isColimitCofanSigma`: a coproduct of coproducts of copies of one object
  is a coproduct of copies of that object, indexed by the total space of the family of index
  types.
* `CategoryTheory.Limits.isColimitCokernelCoforkCofan`: a coproduct of cokernels is a cokernel,
  for the coproduct of the maps.
* `CategoryTheory.Limits.isColimitCokernelCoforkOfIsColimitCocone`: a colimit is a cokernel of a
  map between two coproducts, the one indexed by the arrows of the shape and the one indexed by
  its objects.
* `SheafOfModules.HasGlobalPresentation.of_isColimit_cofan`: a coproduct of globally presented
  sheaves of modules is globally presented.
* `SheafOfModules.HasGlobalPresentation.of_isColimit`: a colimit of globally presented sheaves of
  modules is globally presented, on a site with a terminal object over which the presenting
  morphism of every presentation is surjective on sections.
* `AlgebraicGeometry.FibredSite.hasAffineColimitPresentations`: global presentations on the
  slice site at an affine object are closed under colimits of small shape.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v r m t

namespace CategoryTheory.Limits

variable {A : Type u} [Category.{v} A]

/-- A map out of a coproduct whose components are epimorphisms into the summands of another
coproduct is an epimorphism. -/
theorem epi_of_isColimit_cofan {Jdx : Type w} {Pj Nj : Jdx → A} {bj : ∀ j, Pj j ⟶ Nj j}
    {P N : A} {pinj : ∀ j, Pj j ⟶ P} {ninj : ∀ j, Nj j ⟶ N}
    (hN : IsColimit (Cofan.mk N ninj))
    {b : P ⟶ N} (hb : ∀ j, pinj j ≫ b = bj j ≫ ninj j) (hbj : ∀ j, Epi (bj j)) : Epi b where
  left_cancellation {_} g g' h := by
    refine Cofan.IsColimit.hom_ext hN _ _ fun j ↦ ?_
    have hj : bj j ≫ ninj j ≫ g = bj j ≫ ninj j ≫ g' := by
      rw [← Category.assoc, ← hb j, ← Category.assoc, ← hb j, Category.assoc, Category.assoc, h]
    change ninj j ≫ g = ninj j ≫ g'
    exact (hbj j).left_cancellation _ _ hj

/-- A coproduct of coproducts of copies of one object `O` is a coproduct of copies of `O`,
indexed by the total space of the family of index types: its injection at `⟨j, i⟩` is the `i`-th
injection into the `j`-th summand followed by the `j`-th injection. -/
noncomputable def isColimitCofanSigma {Jdx : Type w} {Idx : Jdx → Type t} {O : A}
    {Pj : Jdx → A} {ιj : ∀ j, Idx j → (O ⟶ Pj j)} (hj : ∀ j, IsColimit (Cofan.mk (Pj j) (ιj j)))
    {Z : A} {inj : ∀ j, Pj j ⟶ Z} (hZ : IsColimit (Cofan.mk Z inj)) :
    IsColimit (Cofan.mk (f := fun _ : Σ j, Idx j ↦ O) Z (fun q ↦ ιj q.1 q.2 ≫ inj q.1)) := by
  refine Cofan.IsColimit.mk _
    (fun s ↦ Cofan.IsColimit.desc hZ
      (fun j ↦ Cofan.IsColimit.desc (hj j) (fun i ↦ s.inj ⟨j, i⟩)))
    (fun s q ↦ ?_) (fun s n hn ↦ Cofan.IsColimit.hom_ext hZ _ _ fun j ↦ ?_)
  · obtain ⟨j, i⟩ := q
    have h1 : inj j ≫ Cofan.IsColimit.desc hZ
        (fun j ↦ Cofan.IsColimit.desc (hj j) (fun i ↦ s.inj ⟨j, i⟩)) =
          Cofan.IsColimit.desc (hj j) (fun i ↦ s.inj ⟨j, i⟩) := Cofan.IsColimit.fac hZ _ j
    change (ιj j i ≫ inj j) ≫ _ = _
    rw [Category.assoc, h1]
    exact Cofan.IsColimit.fac (hj j) (fun i ↦ s.inj ⟨j, i⟩) i
  · have h1 : inj j ≫ Cofan.IsColimit.desc hZ
        (fun j ↦ Cofan.IsColimit.desc (hj j) (fun i ↦ s.inj ⟨j, i⟩)) =
          Cofan.IsColimit.desc (hj j) (fun i ↦ s.inj ⟨j, i⟩) := Cofan.IsColimit.fac hZ _ j
    change inj j ≫ _ = inj j ≫ _
    rw [h1]
    refine Cofan.IsColimit.hom_ext (hj j) _ _ fun i ↦ ?_
    have h2 : ιj j i ≫ Cofan.IsColimit.desc (hj j) (fun i ↦ s.inj ⟨j, i⟩) = s.inj ⟨j, i⟩ :=
      Cofan.IsColimit.fac (hj j) _ i
    change ιj j i ≫ inj j ≫ n = ιj j i ≫ _
    rw [h2, ← Category.assoc]
    exact hn ⟨j, i⟩

section ZeroMorphisms

variable [HasZeroMorphisms A]

/-- The coproduct of a family of maps composes to zero with the coproduct of a family of maps it
is killed by, componentwise. -/
theorem cofan_comp_eq_zero {Jdx : Type w} {Qj Pj Nj : Jdx → A} {aj : ∀ j, Qj j ⟶ Pj j}
    {bj : ∀ j, Pj j ⟶ Nj j} {Q P N : A} {qinj : ∀ j, Qj j ⟶ Q} {pinj : ∀ j, Pj j ⟶ P}
    {ninj : ∀ j, Nj j ⟶ N} (hQ : IsColimit (Cofan.mk Q qinj))
    {a : Q ⟶ P} {b : P ⟶ N} (ha : ∀ j, qinj j ≫ a = aj j ≫ pinj j)
    (hb : ∀ j, pinj j ≫ b = bj j ≫ ninj j) (habj : ∀ j, aj j ≫ bj j = 0) : a ≫ b = 0 := by
  refine Cofan.IsColimit.hom_ext hQ _ _ fun j ↦ ?_
  change qinj j ≫ a ≫ b = qinj j ≫ 0
  rw [← Category.assoc, ha j, Category.assoc, hb j, ← Category.assoc, habj j, zero_comp,
    comp_zero]

/-- If `bj j` is a cokernel of `aj j` for every `j`, and `a` and `b` are maps between coproducts
whose components are the `aj` and the `bj`, then `b` is a cokernel of `a`. -/
noncomputable def isColimitCokernelCoforkCofan {Jdx : Type w} {Qj Pj Nj : Jdx → A}
    {aj : ∀ j, Qj j ⟶ Pj j} {bj : ∀ j, Pj j ⟶ Nj j} {Q P N : A} {qinj : ∀ j, Qj j ⟶ Q}
    {pinj : ∀ j, Pj j ⟶ P} {ninj : ∀ j, Nj j ⟶ N}
    (hP : IsColimit (Cofan.mk P pinj)) (hN : IsColimit (Cofan.mk N ninj))
    {a : Q ⟶ P} {b : P ⟶ N} (ha : ∀ j, qinj j ≫ a = aj j ≫ pinj j)
    (hb : ∀ j, pinj j ≫ b = bj j ≫ ninj j) {habj : ∀ j, aj j ≫ bj j = 0}
    (hbj : ∀ j, IsColimit (CokernelCofork.ofπ (bj j) (habj j))) (hab : a ≫ b = 0) :
    IsColimit (CokernelCofork.ofπ b hab) :=
  haveI : Epi b := epi_of_isColimit_cofan hN hb fun j ↦ Cofork.IsColimit.epi (hbj j)
  CokernelCofork.IsColimit.ofπ' _ _ fun {_} k hk ↦ by
    refine ⟨Cofan.IsColimit.desc hN fun j ↦ (CokernelCofork.IsColimit.desc' (hbj j)
      (pinj j ≫ k) ?_).1, ?_⟩
    · rw [← Category.assoc, ← ha j, Category.assoc, hk, comp_zero]
    · refine Cofan.IsColimit.hom_ext hP _ _ fun j ↦ ?_
      have hd : ninj j ≫ Cofan.IsColimit.desc hN (fun j ↦ (CokernelCofork.IsColimit.desc'
            (hbj j) (pinj j ≫ k) (by rw [← Category.assoc, ← ha j, Category.assoc, hk,
              comp_zero])).1) =
          (CokernelCofork.IsColimit.desc' (hbj j) (pinj j ≫ k)
            (by rw [← Category.assoc, ← ha j, Category.assoc, hk, comp_zero])).1 :=
        Cofan.IsColimit.fac hN _ j
      change pinj j ≫ b ≫ _ = pinj j ≫ k
      rw [← Category.assoc, hb j, Category.assoc, hd]
      exact (CokernelCofork.IsColimit.desc' (hbj j) (pinj j ≫ k) _).2

end ZeroMorphisms

section Preadditive

variable [Preadditive A]

/-- The map out of the coproduct over the arrows of the shape whose component at `g : k₁ ⟶ k₂` is
the difference of the injection at `k₁` and `D g` followed by the injection at `k₂` composes to
zero with the map to the point of a cocone. -/
theorem cofanDifference_comp_eq_zero {K : Type w} [Category.{t} K] {D : K ⥤ A} (c : Cocone D)
    {N M : A} {ninj : ∀ k, D.obj k ⟶ N} {minj : ∀ q : Σ k₁ k₂ : K, k₁ ⟶ k₂, D.obj q.1 ⟶ M}
    (hM : IsColimit (Cofan.mk (f := fun q : Σ k₁ k₂ : K, k₁ ⟶ k₂ ↦ D.obj q.1) M minj))
    {f : M ⟶ N} (hf : ∀ q, minj q ≫ f = ninj q.1 - D.map q.2.2 ≫ ninj q.2.1)
    {π : N ⟶ c.pt} (hπ : ∀ k, ninj k ≫ π = c.ι.app k) : f ≫ π = 0 := by
  refine Cofan.IsColimit.hom_ext hM _ _ fun ⟨k₁, k₂, g⟩ ↦ ?_
  change minj ⟨k₁, k₂, g⟩ ≫ f ≫ π = minj ⟨k₁, k₂, g⟩ ≫ 0
  rw [← Category.assoc, hf ⟨k₁, k₂, g⟩, comp_zero, Preadditive.sub_comp, Category.assoc,
    hπ k₁, hπ k₂, c.w g, sub_self]

/-- A colimit is a cokernel of a map between two coproducts: of the coproduct over the arrows of
the shape, of the sources of the arrows, into the coproduct over its objects, the component at
`g : k₁ ⟶ k₂` being the difference of the injection at `k₁` and `D g` followed by the injection
at `k₂`. -/
noncomputable def isColimitCokernelCoforkOfIsColimitCocone {K : Type w} [Category.{t} K]
    {D : K ⥤ A} {c : Cocone D} (hc : IsColimit c) {N M : A} {ninj : ∀ k, D.obj k ⟶ N}
    {minj : ∀ q : Σ k₁ k₂ : K, k₁ ⟶ k₂, D.obj q.1 ⟶ M}
    (hN : IsColimit (Cofan.mk N ninj))
    {f : M ⟶ N} (hf : ∀ q, minj q ≫ f = ninj q.1 - D.map q.2.2 ≫ ninj q.2.1)
    {π : N ⟶ c.pt} (hπ : ∀ k, ninj k ≫ π = c.ι.app k) (hfπ : f ≫ π = 0) :
    IsColimit (CokernelCofork.ofπ π hfπ) :=
  haveI : Epi π := ⟨fun {_} g g' h ↦ hc.hom_ext fun k ↦ by
    rw [← hπ k, Category.assoc, Category.assoc, h]⟩
  CokernelCofork.IsColimit.ofπ' _ _ fun {A'} k hk ↦ by
    have hw : ∀ {k₁ k₂ : K} (g : k₁ ⟶ k₂), D.map g ≫ ninj k₂ ≫ k = ninj k₁ ≫ k := by
      intro k₁ k₂ g
      have h0 : minj ⟨k₁, k₂, g⟩ ≫ f ≫ k = 0 := by rw [hk, comp_zero]
      rw [← Category.assoc, hf ⟨k₁, k₂, g⟩, Preadditive.sub_comp, sub_eq_zero,
        Category.assoc] at h0
      exact h0.symm
    refine ⟨hc.desc ⟨A', { app := fun k' ↦ ninj k' ≫ k, naturality := fun {k₁ k₂} g ↦ ?_ }⟩, ?_⟩
    · simpa using hw g
    · refine Cofan.IsColimit.hom_ext hN _ _ fun k' ↦ ?_
      change ninj k' ≫ π ≫ _ = ninj k' ≫ k
      rw [← Category.assoc, hπ k']
      exact hc.fac _ k'

end Preadditive

end CategoryTheory.Limits

namespace SheafOfModules

/-- Presheaves of abelian groups in the universe `max u' v' t'` on a site admit sheafification,
and `W` equals locally bijective morphisms there. -/
private theorem hasSheafify_and_wEqualsLocallyBijective.{t', v', u'} {C : Type u'}
    [Category.{v'} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{max u' v' t'} ∧
      J.WEqualsLocallyBijective AddCommGrpCat.{max u' v' t'} :=
  ⟨GrothendieckTopology.hasSheafify_addCommGrpCat.{max u' v' t', v', u'} J,
    _root_.AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u' v' t',
      u', v'} J⟩

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- A coproduct of globally presented sheaves of modules is globally presented. -/
theorem HasGlobalPresentation.of_isColimit_cofan
    [HasWeakSheafify J AddCommGrpCat.{max r m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
    {Jdx : Type (max r m)} {Mj : Jdx → SheafOfModules.{max r m} R}
    {N : SheafOfModules.{max r m} R} {inj : ∀ j, Mj j ⟶ N}
    (hN : IsColimit (Cofan.mk N inj)) (hMj : ∀ j, (Mj j).HasGlobalPresentation) :
    N.HasGlobalPresentation := by
  obtain ⟨_, _⟩ := hasSheafify_and_wEqualsLocallyBijective.{max r m} J
  have hpc : PreservesColimitsOfSize.{max r m, max r m}
      (uliftForPresentationFunctor.{u, v, r, max r m, max u v r} (R := R)) :=
    preservesColimitsOfSize_uliftForPresentationFunctor.{u, v, r, m, max u v r}
  choose I Kk Pj Qj ιj κj hPj hQj aj bj habj hbj using hMj
  have hΦN : IsColimit (Cofan.mk
      ((uliftForPresentationFunctor.{u, v, r, max r m, max u v r} (R := R)).obj N)
      fun j ↦ (uliftForPresentationFunctor.{u, v, r, max r m, max u v r} (R := R)).map (inj j)) :=
    isColimitCofanMkObjOfIsColimit _ Mj inj hN
  have ha : ∀ j, Sigma.ι Qj j ≫ Sigma.desc (fun j ↦ aj j ≫ Sigma.ι Pj j) =
      aj j ≫ Sigma.ι Pj j := fun j ↦ by simp
  have hb : ∀ j, Sigma.ι Pj j ≫ Sigma.desc (fun j ↦ bj j ≫
      (uliftForPresentationFunctor.{u, v, r, max r m, max u v r} (R := R)).map (inj j)) =
        bj j ≫ (uliftForPresentationFunctor.{u, v, r, max r m,
          max u v r} (R := R)).map (inj j) := fun j ↦ by simp
  have hab := cofan_comp_eq_zero (coproductIsCoproduct Qj) ha hb habj
  exact ⟨Σ j, I j, Σ j, Kk j, ∐ Pj, ∐ Qj,
    fun q ↦ ιj q.1 q.2 ≫ Sigma.ι Pj q.1, fun q ↦ κj q.1 q.2 ≫ Sigma.ι Qj q.1,
    ⟨isColimitCofanSigma (fun j ↦ (hPj j).some) (coproductIsCoproduct Pj)⟩,
    ⟨isColimitCofanSigma (fun j ↦ (hQj j).some) (coproductIsCoproduct Qj)⟩,
    _, _, hab,
    ⟨isColimitCokernelCoforkCofan (coproductIsCoproduct Pj) hΦN ha hb
      (fun j ↦ (hbj j).some) hab⟩⟩

/-- A colimit of globally presented sheaves of modules is globally presented, on a site with a
terminal object `Z` over which the presenting morphism of every global presentation is surjective
on sections. -/
theorem HasGlobalPresentation.of_isColimit
    [HasWeakSheafify J AddCommGrpCat.{max r m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
    {Z : C} (hZ : IsTerminal Z)
    (hsurj : ∀ (N' : SheafOfModules.{max r m} R) (I' K' : Type (max u v r m))
      (P' Q' : SheafOfModules.{max u v r m} R)
      (ι' : ∀ _ : I', uliftForPresentation.{u, v, r, r, max u v r m} (unit R) ⟶ P')
      (κ' : ∀ _ : K', uliftForPresentation.{u, v, r, r, max u v r m} (unit R) ⟶ Q'),
      IsColimit (Cofan.mk P' ι') → IsColimit (Cofan.mk Q' κ') →
      ∀ (a' : Q' ⟶ P') (b' : P' ⟶ uliftForPresentation.{u, v, r, max r m, max u v r} N')
        (hab' : a' ≫ b' = 0), IsColimit (CokernelCofork.ofπ b' hab') →
          Function.Surjective (b'.val.app (op Z)))
    {K : Type (max r m)} [Category.{max r m} K] {D : K ⥤ SheafOfModules.{max r m} R}
    {c : Cocone D} (hc : IsColimit c) (hD : ∀ k, (D.obj k).HasGlobalPresentation) :
    c.pt.HasGlobalPresentation := by
  have hf : ∀ q : Σ k₁ k₂ : K, k₁ ⟶ k₂,
      Sigma.ι (fun q : Σ k₁ k₂ : K, k₁ ⟶ k₂ ↦ D.obj q.1) q ≫
          Sigma.desc (fun q : Σ k₁ k₂ : K, k₁ ⟶ k₂ ↦
            Sigma.ι D.obj q.1 - D.map q.2.2 ≫ Sigma.ι D.obj q.2.1) =
        Sigma.ι D.obj q.1 - D.map q.2.2 ≫ Sigma.ι D.obj q.2.1 := fun q ↦ by simp
  have hπ : ∀ k, Sigma.ι D.obj k ≫ Sigma.desc c.ι.app = c.ι.app k := fun k ↦ by simp
  have hfπ := cofanDifference_comp_eq_zero c (coproductIsCoproduct _) hf hπ
  have hπcok := isColimitCokernelCoforkOfIsColimitCocone hc (coproductIsCoproduct D.obj) hf hπ hfπ
  obtain ⟨I, K', P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ :=
    HasGlobalPresentation.of_isColimit_cofan (coproductIsCoproduct D.obj) hD
  obtain ⟨I', F, ν, ⟨hF⟩, p, hpepi⟩ :=
    (HasGlobalPresentation.of_isColimit_cofan
      (coproductIsCoproduct (fun q : Σ k₁ k₂ : K, k₁ ⟶ k₂ ↦ D.obj q.1))
      (fun q ↦ hD q.1)).exists_epi_of_isColimit_cofan
  obtain ⟨_, _⟩ := hasSheafify_and_wEqualsLocallyBijective.{max r m} J
  have hfin : PreservesFiniteColimits
      (uliftForPresentationFunctor.{u, v, r, max r m, max u v r} (R := R)) :=
    preservesFiniteColimits_uliftForPresentationFunctor.{u, v, r, m, max u v r}
  have := hpepi
  exact HasGlobalPresentation.of_isColimit_cokernelCofork_of_surjective_val_app
    hP hQ hF hab hb hZ (hsurj _ I K' P Q ι κ hP hQ a b hab hb) (p := p)
    (by rw [← uliftForPresentationMap_comp, hfπ]
        exact (uliftForPresentationFunctor.{u, v, r, max r m, max u v r} (R := R)).map_zero _ _)
    (isColimitCoforkMapOfIsColimit' (uliftForPresentationFunctor.{u, v, r, max r m, max u v r})
      hfπ hπcok)

end SheafOfModules

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- Global presentations on the slice site at an affine object are closed under colimits of
small shape. -/
theorem hasAffineColimitPresentations : HasAffineColimitPresentations B S hS p hp := by
  intro K _ i D c hc hD
  have _ := hasWeakSheafify_over B S hS p hp .fppf (affineObj B S hS p i)
  have _ := wEqualsLocallyBijective_over B S hS p hp .fppf (affineObj B S hS p i)
  refine SheafOfModules.HasGlobalPresentation.of_isColimit
    (Over.mkIdTerminal (X := affineObj B S hS p i))
    (fun N' I' K' P' Q' ι' κ' hP' hQ' a' b' hab' hb' ↦ ?_) hc hD
  obtain ⟨_, _⟩ := SheafOfModules.hasSheafify_and_wEqualsLocallyBijective.{u}
    ((BigFppfOver.associatedTopology B S hS p .fppf).over (affineObj B S hS p i))
  have _ : Epi b' := Cofork.IsColimit.epi hb'
  exact surjective_val_app_of_isColimit_of_isAffineOver B S hS p hp κ' ι' hQ' hP' a' b'
    (by rw [← SheafOfModules.comp_val, hab']; rfl) hab' hb' _ i.property

end AlgebraicGeometry.FibredSite

end
