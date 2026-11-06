module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreePullbackChartFactor
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.PullbackFreeIsoComp
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPullbackComp
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueChartShrink

/-!
# Shrinking the trivialisation of the inverse image `b^*N` over the preimage of an open

`AlgebraicGeometry.pullbackFreeChartCompIso_eq` cuts the chart comparison of the essential
surjectivity half of [Stacks, Tag 0EXD] into two halves that shrink for completely different
reasons:  the trivialisation of `𝒢` given by `α`, which shrinks by
`AlgebraicGeometry.restrictChartIso_freeChartTargetIso`, and the trivialisation
`AlgebraicGeometry.pullbackFreeTrivIso` of `b^*N` over the preimage of an open `W` on which `N` is
trivialised.  This file shrinks the second half, which closes the shrink of the chart comparison.

## The route

`AlgebraicGeometry.restrictChartIso_pullback_trans` shrinks a comparison presented on the
*inverse images*, provided the two presentations satisfy a cocycle condition there.  The
trivialisation of `b^*N` is such a comparison:  dropping its two passages between restriction and
inverse image leaves `AlgebraicGeometry.pullbackFreeTrivPullbackIso`, a composite of the square
comparison cut out by `W`, the inverse image of a trivialisation of `N`, and the free comparison
of an inverse image.  Its cocycle condition splits into

* the **paste law** of the two square comparisons, over `W` and over the smaller `W'`, whose
  shrinking square is Mathlib's `AlgebraicGeometry.morphismRestrict_homOfLE`;
* the **pseudo-functoriality of the free comparison**, in the form with the composite kept as a
  variable, since the two routes present the one morphism `b ⁻¹ᵁ W' ⟶ W` as two different
  composites;
* the **compatibility of the two trivialisations of `N`**, which is the hypothesis.

## Implementation notes

Two obstructions shape the file, and both are met by moving the argument to a level where they do
not arise.

The first is transparency.  `AlgebraicGeometry.Scheme.ringCatSheaf` unfolds to what
`CategoryTheory.SheafOfModules` asks for only at default transparency, so in a goal whose objects
are free modules on a scheme **no rewrite fires at all** -- not `Iso.trans_hom`, not
`CategoryTheory.Category.assoc`.  Every statement here whose type mentions a free module is
therefore proved in term mode, by `congrArg` and `Eq.trans`; and the one place where real rewriting
is needed, the assembly of the cocycle condition out of its six inputs, is stated over abstract
categories as `Stacks.AlgebraicGeometry.ModuleLimits.trivShrink_of_paste` and instantiated by a
single `exact`.

The second is the kernel budget recorded in
`StacksFrontier/AlgebraicGeometry/ModuleLimits/RestrictPullbackShrinkTail.lean`:  an equation between
composites of six morphisms through four-fold nested inverse images does not finish checking.  The
paste law is accordingly stated as
`AlgebraicGeometry.modulesPullbackTriangleIso_square_paste`, with all ten morphisms and all four
composites variables subject to equations, so that no `AlgebraicGeometry.Scheme.Hom.resLE` and no
concrete open ever appears inside it; keeping the composites variable is also what makes
`AlgebraicGeometry.modulesPullbackTriangleIso_pentagon_app` applicable, which is the whole proof.

## Main definitions

* `AlgebraicGeometry.pullbackPreimageSquareIso`: the square comparison cut out by `W`, with both
  passages between restriction and inverse image left off.
* `AlgebraicGeometry.pullbackFreeTrivPullbackIso`: the trivialisation of `b^*N` over the preimage
  of `W`, entirely in the inverse-image world.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.trivShrink_of_paste`: the categorical assembly of the
  cocycle condition out of the paste law, the two naturalities and the two
  pseudo-functorialities.
* `AlgebraicGeometry.modulesPullbackTriangleIso_square_paste`: **the paste law of the
  inverse-image pseudofunctor**, over variables.
* `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso_comp_of_eq`: pseudo-functoriality of the free
  comparison with the composite kept as a variable.
* `AlgebraicGeometry.pullbackFreeTrivIso_eq`: the trivialisation of `b^*N` read in the
  inverse-image world.
* `AlgebraicGeometry.pullbackPreimageSquareIso_shrink`, and
  `AlgebraicGeometry.pullbackFreeTrivPullbackIso_shrink`: the paste law and the cocycle condition
  at the squares of the blow-up descent.
* `AlgebraicGeometry.restrictChartIso_pullbackFreeTrivIso`: **the trivialisation of `b^*N` over
  the preimage of an open is compatible with shrinking the open.**

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- **A trivialisation assembled from a square comparison, a trivialisation of the base and a
free comparison is compatible with shrinking, given the paste law of the squares.**

The data is the one a chart comparison of the blow-up descent is built from, with every functor
and every morphism a variable:  `s` and `s'` are the square comparisons over the larger and the
smaller open, `t` and `t'` the trivialisations of the base, `fr`, `fr'`, `fbb`, `fcc`, `fm` the
free comparisons, `dk`, `dm1`, `dm2`, `dcc` the contractions of iterated inverse images.  The
hypotheses are the paste law, the two naturalities of the contraction, the two
pseudo-functorialities of the free comparison, and the compatibility of `t` with `t'`.

**It is stated over abstract categories on purpose.**  At the inverse images of sheaves of
modules on schemes the two sides are composites between four-fold nested applications of
`AlgebraicGeometry.Scheme.Modules.pullback` whose targets are free modules, and at those types
`Scheme.ringCatSheaf` does not unfold at the transparency `rw` and `simp` build their motives at:
no rewrite fires at all.  Here nothing of the kind occurs and the proof is five rewrites; the
geometric statement is then one `exact`. -/
theorem trivShrink_of_paste {𝒜 : Type w₁} {ℬ : Type w₂} {𝒞 : Type w₃} {𝒟 : Type w₄}
    [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞] [Category.{v₄} 𝒟]
    (Pr : 𝒜 ⥤ 𝒞) (Pcc : 𝒜 ⥤ ℬ) (Pbb : 𝒞 ⥤ 𝒟) (Pr' : ℬ ⥤ 𝒟) (Pm : 𝒜 ⥤ 𝒟)
    {N₀ FW : 𝒜} {N₁ FW' : ℬ} {X₀ FQ : 𝒞} {Y FQ' : 𝒟}
    (s : X₀ ⟶ Pr.obj N₀) (t : N₀ ⟶ FW) (fr : Pr.obj FW ⟶ FQ) (fbb : Pbb.obj FQ ⟶ FQ')
    (dk : Pbb.obj X₀ ⟶ Y) (s' : Y ⟶ Pr'.obj N₁) (t' : N₁ ⟶ FW')
    (fr' : Pr'.obj FW' ⟶ FQ') (fcc : Pcc.obj FW ⟶ FW') (fm : Pm.obj FW ⟶ FQ')
    (dm1 : Pbb.obj (Pr.obj N₀) ⟶ Pm.obj N₀) (dm1F : Pbb.obj (Pr.obj FW) ⟶ Pm.obj FW)
    (dm2 : Pr'.obj (Pcc.obj N₀) ⟶ Pm.obj N₀) (dm2F : Pr'.obj (Pcc.obj FW) ⟶ Pm.obj FW)
    (dcc : Pcc.obj N₀ ⟶ N₁) (dccInv : N₁ ⟶ Pcc.obj N₀)
    (hpaste : Pbb.map s ≫ dm1 = dk ≫ s' ≫ Pr'.map dccInv ≫ dm2)
    (hnat1 : Pbb.map (Pr.map t) ≫ dm1F = dm1 ≫ Pm.map t)
    (hfree1 : Pbb.map fr ≫ fbb = dm1F ≫ fm)
    (hnat2 : Pr'.map (Pcc.map t) ≫ dm2F = dm2 ≫ Pm.map t)
    (hfree2 : Pr'.map fcc ≫ fr' = dm2F ≫ fm)
    (ht : dcc ≫ t' = Pcc.map t ≫ fcc) (hinv : dccInv ≫ dcc = 𝟙 N₁) :
    dk ≫ s' ≫ Pr'.map t' ≫ fr' = Pbb.map (s ≫ Pr.map t ≫ fr) ≫ fbb := by
  have key : Pr'.map dccInv ≫ dm2 ≫ Pm.map t ≫ fm = Pr'.map t' ≫ fr' := by
    rw [← reassoc_of% hnat2, ← hfree2, ← CategoryTheory.Functor.map_comp_assoc,
      ← CategoryTheory.Functor.map_comp_assoc, Category.assoc, ← ht, ← Category.assoc, hinv,
      Category.id_comp]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [hfree1, reassoc_of% hnat1, ← Category.assoc (Pbb.map s) dm1, hpaste]
  simp only [Category.assoc, key]

end Stacks.AlgebraicGeometry.ModuleLimits

namespace AlgebraicGeometry

/-- `AlgebraicGeometry.pullbackCompIsoOfEq` is the comparison of
`AlgebraicGeometry.modulesPullbackTriangleIso` at a module:  both are
`AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`, one at a module and one as an isomorphism of
functors. -/
theorem pullbackCompIsoOfEq_eq {A B C : Scheme.{u}} (c : A ⟶ B) (p : B ⟶ C) {k : A ⟶ C}
    (hk : c ≫ p = k) (M : C.Modules) :
    pullbackCompIsoOfEq c p hk M = (modulesPullbackTriangleIso c p k hk).app M :=
  rfl

/-- **The free comparison of an inverse image is pseudo-functorial, with the composite kept as a
variable.**  This is
`AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_free_comp_pullbackFreeIso_hom` stated for a
morphism `m` presented as the composite rather than for the literal composite, which is what lets
two such identities for *different* presentations of one composite be compared. -/
theorem Scheme.Modules.pullbackFreeIso_comp_of_eq {A B C : Scheme.{u}} (c : A ⟶ B) (p : B ⟶ C)
    {m : A ⟶ C} (hm : c ≫ p = m) (I : Type u) :
    (Scheme.Modules.pullback c).map (Scheme.Modules.pullbackFreeIso p I).hom ≫
        (Scheme.Modules.pullbackFreeIso c I).hom =
      (pullbackCompIsoOfEq c p hm (_root_.SheafOfModules.free (R := C.ringCatSheaf) I)).hom ≫
        (Scheme.Modules.pullbackFreeIso m I).hom := by
  subst hm
  refine Eq.trans
    (Scheme.Modules.pullbackComp_hom_app_free_comp_pullbackFreeIso_hom c p I).symm ?_
  exact congrArg (· ≫ (Scheme.Modules.pullbackFreeIso (c ≫ p) I).hom)
    (Category.comp_id ((Scheme.Modules.pullbackComp c p).hom.app
      (_root_.SheafOfModules.free (R := C.ringCatSheaf) I))).symm

/-- **The pasting coherence of the inverse-image pseudofunctor, with every composite kept as a
variable.**

Two commuting squares of schemes are stacked:  the inner one `q ≫ v = r ≫ w` over `W`, and the
one `bb ≫ r = r' ≫ cc` shrinking it, whose paste is the square `q' ≫ v = r' ≫ w'` over the
smaller `W'`.  The statement says that the comparison attached to the pasted square, preceded by
the contraction of the two inverse images along `bb` and `q`, is the comparison attached to the
inner square pulled back along `bb`, both read into the inverse image along the common morphism
`m`.

Everything is a variable:  no open immersion, no restriction functor and no free module occurs,
which is what keeps the equation -- between morphisms of three-fold iterated inverse images --
inside the kernel's budget.  The proof is
`AlgebraicGeometry.modulesPullbackTriangleIso_pentagon_app` three times, for the three triangles
cut out by `n` and `n'`. -/
theorem modulesPullbackTriangleIso_square_paste {T S WW WW' QQ QQ' : Scheme.{u}} (v : S ⟶ T)
    (q : QQ ⟶ S) {q' : QQ' ⟶ S} (bb : QQ' ⟶ QQ) (r : QQ ⟶ WW) (r' : QQ' ⟶ WW') (w : WW ⟶ T)
    {w' : WW' ⟶ T} (cc : WW' ⟶ WW) {m : QQ' ⟶ WW} {n : QQ ⟶ T} {n' : QQ' ⟶ T}
    (e3 : bb ≫ q = q') (e4 : cc ≫ w = w') (e5 : bb ≫ r = m) (e6 : r' ≫ cc = m)
    (en1 : q ≫ v = n) (en2 : r ≫ w = n) (en1' : q' ≫ v = n') (en2' : r' ≫ w' = n')
    (N : T.Modules) :
    (modulesPullbackTriangleIso bb q q' e3).hom.app
          ((Scheme.Modules.pullback v).obj N) ≫
        (modulesPullbackTriangleIso q' v n' en1').hom.app N ≫
        (modulesPullbackTriangleIso r' w' n' en2').inv.app N ≫
        (Scheme.Modules.pullback r').map
          ((modulesPullbackTriangleIso cc w w' e4).inv.app N) ≫
        (modulesPullbackTriangleIso r' cc m e6).hom.app
          ((Scheme.Modules.pullback w).obj N) =
      (Scheme.Modules.pullback bb).map
          ((modulesPullbackTriangleIso q v n en1).hom.app N ≫
            (modulesPullbackTriangleIso r w n en2).inv.app N) ≫
        (modulesPullbackTriangleIso bb r m e5).hom.app
          ((Scheme.Modules.pullback w).obj N) := by
  have hn' : bb ≫ n = n' := by rw [← en1, ← Category.assoc, e3, en1']
  have hmw : m ≫ w = n' := by rw [← e5, Category.assoc, en2, hn']
  have P1 := modulesPullbackTriangleIso_pentagon_app bb q v q' n n' e3 en1 hn' en1' N
  have P2 := modulesPullbackTriangleIso_pentagon_app bb r w m n n' e5 en2 hn' hmw N
  have P3 := modulesPullbackTriangleIso_pentagon_app r' cc w m w' n' e6 e4 en2' hmw N
  rw [← Iso.cancel_iso_hom_right _ _ ((modulesPullbackTriangleIso m w n' hmw).app N)]
  simp only [Iso.app_hom, Functor.map_comp, Category.assoc, P2, P3, reassoc_of% P1]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

variable {X X' : Scheme.{u}} (b : X' ⟶ X) {I : Type u}

/-- Associativity bookkeeping: a composite of six, cut after the fourth factor, is the same
composite cut after the first, with the second and third and the fourth and fifth paired. -/
theorem comp_reassoc₆ {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : D}
    (u₁ : X₀ ⟶ X₁) (u₂ : X₁ ⟶ X₂) (u₃ : X₂ ⟶ X₃) (u₄ : X₃ ⟶ X₄) (u₅ : X₄ ⟶ X₅)
    (u₆ : X₅ ⟶ X₆) :
    (u₁ ≫ u₂ ≫ u₃ ≫ u₄) ≫ u₅ ≫ u₆ = u₁ ≫ (u₂ ≫ u₃) ≫ (u₄ ≫ u₅) ≫ u₆ := by
  simp

/-- **The comparison of the two inverse images of `N` attached to the square cut out by an open
`W` of `X`**: the inverse image along the inclusion of `b ⁻¹ᵁ W` of `b^*N` is the inverse image
along `b ∣_ W` of the inverse image of `N` along the inclusion of `W`.

This is `AlgebraicGeometry.restrictPullbackPreimageIso` with both of its passages between
restriction and inverse image left off, so that nothing but the inverse-image pseudofunctor
occurs. -/
def pullbackPreimageSquareIso (W : X.Opens) (N : X.Modules) :
    (Scheme.Modules.pullback (b ⁻¹ᵁ W).ι).obj ((Scheme.Modules.pullback b).obj N) ≅
      (Scheme.Modules.pullback (b ∣_ W)).obj ((Scheme.Modules.pullback W.ι).obj N) :=
  pullbackCompIsoOfEq (b ⁻¹ᵁ W).ι b (morphismRestrict_ι b W).symm N ≪≫
    (pullbackCompIsoOfEq (b ∣_ W) W.ι rfl N).symm

/-- **The trivialisation of `b^*N` over the preimage of `W`, in the inverse-image world.**
This is `AlgebraicGeometry.pullbackFreeTrivIso` with its source read as an inverse image rather
than a restriction, and with the trivialisation of `N` over `W` given on the inverse image too.

Keeping the trivialisation on the inverse image is what makes the whole composite a statement
about the inverse-image pseudofunctor and the free comparison alone:  that is what
`AlgebraicGeometry.pullbackFreeTrivPullbackIso_shrink` needs. -/
def pullbackFreeTrivPullbackIso (W : X.Opens) (N : X.Modules)
    (τ : (Scheme.Modules.pullback W.ι).obj N ≅
      _root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) I) :
    (Scheme.Modules.pullback (b ⁻¹ᵁ W).ι).obj ((Scheme.Modules.pullback b).obj N) ≅
      _root_.SheafOfModules.free (R := (b ⁻¹ᵁ W).toScheme.ringCatSheaf) I :=
  pullbackPreimageSquareIso b W N ≪≫
    (Scheme.Modules.pullback (b ∣_ W)).mapIso τ ≪≫
    Scheme.Modules.pullbackFreeIso (b ∣_ W) I

/-- **The trivialisation of `b^*N` over the preimage of `W` is the identification of the
restriction with the inverse image followed by the inverse-image trivialisation.**

Both sides are the same six comparisons in the same order; they are bracketed differently, and
the trivialisation of `N` is carried to the inverse image by the one factor
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` that the two bracketings put on
opposite sides of the cut.  Nothing is unfolded:  the transparency obstruction recorded in
`StacksFrontier/AlgebraicGeometry/FiniteLocallyFree/RestrictFreeIsoComp.lean` makes a goal about a
free module on a scheme unrewritable, so the reassociation is applied by hand in term mode. -/
theorem pullbackFreeTrivIso_eq (W : X.Opens) (N : X.Modules)
    (τ : Scheme.Modules.restrict N W.ι ≅
      _root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) I) :
    pullbackFreeTrivIso b W N τ =
      (Scheme.Modules.restrictFunctorIsoPullback (b ⁻¹ᵁ W).ι).app
          ((Scheme.Modules.pullback b).obj N) ≪≫
        pullbackFreeTrivPullbackIso b W N
          (((Scheme.Modules.restrictFunctorIsoPullback W.ι).app N).symm ≪≫ τ) :=
  Iso.ext ((comp_reassoc₆ _ _ _ _ _ _).trans
    (congrArg (fun z =>
      (Scheme.Modules.restrictFunctorIsoPullback (b ⁻¹ᵁ W).ι).hom.app
          ((Scheme.Modules.pullback b).obj N) ≫
        ((pullbackCompIsoOfEq (b ⁻¹ᵁ W).ι b (morphismRestrict_ι b W).symm N).hom ≫
            (pullbackCompIsoOfEq (b ∣_ W) W.ι rfl N).inv) ≫
          z ≫ (Scheme.Modules.pullbackFreeIso (b ∣_ W) I).hom)
      ((Scheme.Modules.pullback (b ∣_ W)).map_comp
        ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app N).inv τ.hom).symm))

/-- **The square comparison over the preimage of a smaller open is the square comparison over the
larger one, shrunk.**  This is
`AlgebraicGeometry.modulesPullbackTriangleIso_square_paste` at the two squares cut out by `W` and
by `W'`, whose shrinking square is `AlgebraicGeometry.morphismRestrict_homOfLE`. -/
theorem pullbackPreimageSquareIso_shrink {W W' : X.Opens} (hW : W' ≤ W) (N : X.Modules) :
    (pullbackCompIsoOfEq (X'.homOfLE (b.preimage_mono hW)) (b ⁻¹ᵁ W).ι
          (Scheme.homOfLE_ι X' (b.preimage_mono hW))
          ((Scheme.Modules.pullback b).obj N)).hom ≫
        (pullbackPreimageSquareIso b W' N).hom ≫
        (Scheme.Modules.pullback (b ∣_ W')).map
          (pullbackCompIsoOfEq (X.homOfLE hW) W.ι (Scheme.homOfLE_ι X hW) N).inv ≫
        (pullbackCompIsoOfEq (b ∣_ W') (X.homOfLE hW)
            (morphismRestrict_homOfLE b W' W hW)
            ((Scheme.Modules.pullback W.ι).obj N)).hom =
      (Scheme.Modules.pullback (X'.homOfLE (b.preimage_mono hW))).map
          (pullbackPreimageSquareIso b W N).hom ≫
        (pullbackCompIsoOfEq (X'.homOfLE (b.preimage_mono hW)) (b ∣_ W) rfl
          ((Scheme.Modules.pullback W.ι).obj N)).hom :=
  modulesPullbackTriangleIso_square_paste b (b ⁻¹ᵁ W).ι
    (X'.homOfLE (b.preimage_mono hW)) (b ∣_ W) (b ∣_ W') W.ι (X.homOfLE hW)
    (Scheme.homOfLE_ι X' (b.preimage_mono hW)) (Scheme.homOfLE_ι X hW) rfl
    (morphismRestrict_homOfLE b W' W hW) (morphismRestrict_ι b W).symm rfl
    (morphismRestrict_ι b W').symm rfl N

/-- **The inverse-image trivialisation of `b^*N` over the preimage of `W` shrinks to the one over
the preimage of a smaller `W'`**, provided the two trivialisations of `N` are compatible.

This is the cocycle condition on inverse images that
`AlgebraicGeometry.restrictChartIso_pullback_trans` asks for, and it is
`Stacks.AlgebraicGeometry.ModuleLimits.trivShrink_of_paste` at the square comparisons of the two
opens:  the paste law is `AlgebraicGeometry.pullbackPreimageSquareIso_shrink`, the two
pseudo-functorialities of the free comparison are
`AlgebraicGeometry.Scheme.Modules.pullbackFreeIso_comp_of_eq`, and the two naturalities are those
of `AlgebraicGeometry.modulesPullbackTriangleIso`. -/
theorem pullbackFreeTrivPullbackIso_shrink {W W' : X.Opens} (hW : W' ≤ W) (N : X.Modules)
    (τ : (Scheme.Modules.pullback W.ι).obj N ≅
      _root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) I)
    (τ' : (Scheme.Modules.pullback W'.ι).obj N ≅
      _root_.SheafOfModules.free (R := W'.toScheme.ringCatSheaf) I)
    (hτ : (pullbackCompIsoOfEq (X.homOfLE hW) W.ι (Scheme.homOfLE_ι X hW) N).hom ≫ τ'.hom =
      (Scheme.Modules.pullback (X.homOfLE hW)).map τ.hom ≫
        (Scheme.Modules.pullbackFreeIso (X.homOfLE hW) I).hom) :
    (pullbackCompIsoOfEq (X'.homOfLE (b.preimage_mono hW)) (b ⁻¹ᵁ W).ι
          (Scheme.homOfLE_ι X' (b.preimage_mono hW))
          ((Scheme.Modules.pullback b).obj N)).hom ≫
        (pullbackFreeTrivPullbackIso b W' N τ').hom =
      (Scheme.Modules.pullback (X'.homOfLE (b.preimage_mono hW))).map
          (pullbackFreeTrivPullbackIso b W N τ).hom ≫
        (Scheme.Modules.pullbackFreeIso (X'.homOfLE (b.preimage_mono hW)) I).hom :=
  Stacks.AlgebraicGeometry.ModuleLimits.trivShrink_of_paste
    (Scheme.Modules.pullback (b ∣_ W)) (Scheme.Modules.pullback (X.homOfLE hW))
    (Scheme.Modules.pullback (X'.homOfLE (b.preimage_mono hW)))
    (Scheme.Modules.pullback (b ∣_ W'))
    (Scheme.Modules.pullback (X'.homOfLE (b.preimage_mono hW) ≫ (b ∣_ W)))
    (pullbackPreimageSquareIso b W N).hom τ.hom
    (Scheme.Modules.pullbackFreeIso (b ∣_ W) I).hom
    (Scheme.Modules.pullbackFreeIso (X'.homOfLE (b.preimage_mono hW)) I).hom
    (pullbackCompIsoOfEq (X'.homOfLE (b.preimage_mono hW)) (b ⁻¹ᵁ W).ι
      (Scheme.homOfLE_ι X' (b.preimage_mono hW)) ((Scheme.Modules.pullback b).obj N)).hom
    (pullbackPreimageSquareIso b W' N).hom τ'.hom
    (Scheme.Modules.pullbackFreeIso (b ∣_ W') I).hom
    (Scheme.Modules.pullbackFreeIso (X.homOfLE hW) I).hom
    (Scheme.Modules.pullbackFreeIso (X'.homOfLE (b.preimage_mono hW) ≫ (b ∣_ W)) I).hom
    (pullbackCompIsoOfEq (X'.homOfLE (b.preimage_mono hW)) (b ∣_ W) rfl
      ((Scheme.Modules.pullback W.ι).obj N)).hom
    (pullbackCompIsoOfEq (X'.homOfLE (b.preimage_mono hW)) (b ∣_ W) rfl
      (_root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) I)).hom
    (pullbackCompIsoOfEq (b ∣_ W') (X.homOfLE hW) (morphismRestrict_homOfLE b W' W hW)
      ((Scheme.Modules.pullback W.ι).obj N)).hom
    (pullbackCompIsoOfEq (b ∣_ W') (X.homOfLE hW) (morphismRestrict_homOfLE b W' W hW)
      (_root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) I)).hom
    (pullbackCompIsoOfEq (X.homOfLE hW) W.ι (Scheme.homOfLE_ι X hW) N).hom
    (pullbackCompIsoOfEq (X.homOfLE hW) W.ι (Scheme.homOfLE_ι X hW) N).inv
    (pullbackPreimageSquareIso_shrink b hW N).symm
    ((modulesPullbackTriangleIso (X'.homOfLE (b.preimage_mono hW)) (b ∣_ W)
      (X'.homOfLE (b.preimage_mono hW) ≫ (b ∣_ W)) rfl).hom.naturality τ.hom)
    (Scheme.Modules.pullbackFreeIso_comp_of_eq (X'.homOfLE (b.preimage_mono hW)) (b ∣_ W) rfl I)
    ((modulesPullbackTriangleIso (b ∣_ W') (X.homOfLE hW)
      (X'.homOfLE (b.preimage_mono hW) ≫ (b ∣_ W))
      (morphismRestrict_homOfLE b W' W hW)).hom.naturality τ.hom)
    (Scheme.Modules.pullbackFreeIso_comp_of_eq (b ∣_ W') (X.homOfLE hW)
      (morphismRestrict_homOfLE b W' W hW) I)
    hτ (pullbackCompIsoOfEq (X.homOfLE hW) W.ι (Scheme.homOfLE_ι X hW) N).inv_hom_id

/-- Moving the last factor of a composite of isomorphisms to the other side. -/
theorem iso_trans_eq_iff {D : Type*} [Category D] {A B C : D} (e : A ≅ B) (f : B ≅ C)
    (g : A ≅ C) : e ≪≫ f = g ↔ e = g ≪≫ f.symm := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

/-- A chart comparison ending in the free comparison of a restriction is the same as one ending in
the inverse-image form of that comparison. -/
private theorem restrictChartIso_comp_free_iff {P' P T : Scheme.{u}} {p : P' ⟶ P} {c : T ⟶ P'}
    {k : T ⟶ P} (hk : c ≫ p = k) [IsOpenImmersion p] [IsOpenImmersion c] [IsOpenImmersion k]
    {M : P.Modules} {σ₀ σ : Scheme.Modules.restrict M p ≅
      _root_.SheafOfModules.free (R := P'.ringCatSheaf) I}
    {g₀ g : Scheme.Modules.restrict M k ≅ _root_.SheafOfModules.free (R := T.ringCatSheaf) I}
    (hσ : σ₀ = σ) (hg : g₀ = g) :
    restrictChartIso p σ c hk = g ≪≫ (Stacks.Modules.restrictFreeIso c I).symm ↔
      restrictChartIso p σ₀ c hk ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback c).app
            (_root_.SheafOfModules.free (R := P'.ringCatSheaf) I) ≪≫
          Scheme.Modules.pullbackFreeIso c I) = g₀ := by
  subst hσ hg
  rw [← Stacks.Modules.restrictFreeIso_eq c I]
  exact (iso_trans_eq_iff _ _ _).symm

/-- **The trivialisation of `b^*N` over the preimage of `W` is compatible with shrinking the
open.**  For `W' ≤ W` and trivialisations `τ`, `τ'` of `N` over `W` and `W'` that agree over the
smaller open, the chart comparison of `AlgebraicGeometry.pullbackFreeTrivIso` at `W` along the
inclusion of the preimage of `W'` is the trivialisation at `W'`, read through the comparison of
the restriction of the free module on `b ⁻¹ᵁ W` with the free module on `b ⁻¹ᵁ W'`.

This is the half of the shrink of the chart comparison
`AlgebraicGeometry.pullbackFreeChartCompIso` that does not mention `𝒢` or `α`; the other half is
`AlgebraicGeometry.restrictChartIso_freeChartTargetIso`, and
`AlgebraicGeometry.pullbackFreeChartCompIso_eq` is what splits the comparison into the two.

The route is `AlgebraicGeometry.restrictChartIso_pullback_trans`, whose cocycle condition on the
inverse images is `AlgebraicGeometry.pullbackFreeTrivPullbackIso_shrink`; the hypothesis `hτ` is
carried to the inverse images by
`AlgebraicGeometry.pullbackCompIsoOfEq_hom_comp_of_restrictChartIso`, and the three comparison
factors the conclusion comes with are recognised by
`AlgebraicGeometry.pullbackFreeTrivIso_eq` and `Stacks.Modules.restrictFreeIso_eq`. -/
theorem restrictChartIso_pullbackFreeTrivIso {W W' : X.Opens} (hW : W' ≤ W) (N : X.Modules)
    (τ : Scheme.Modules.restrict N W.ι ≅
      _root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) I)
    (τ' : Scheme.Modules.restrict N W'.ι ≅
      _root_.SheafOfModules.free (R := W'.toScheme.ringCatSheaf) I)
    (hτ : restrictChartIso W.ι τ (X.homOfLE hW) (Scheme.homOfLE_ι X hW) =
      τ' ≪≫ (Stacks.Modules.restrictFreeIso (X.homOfLE hW) I).symm) :
    restrictChartIso (b ⁻¹ᵁ W).ι (pullbackFreeTrivIso b W N τ)
          (X'.homOfLE (b.preimage_mono hW))
          (Scheme.homOfLE_ι X' (b.preimage_mono hW)) =
      pullbackFreeTrivIso b W' N τ' ≪≫
        (Stacks.Modules.restrictFreeIso (X'.homOfLE (b.preimage_mono hW)) I).symm := by
  have hmain := restrictChartIso_pullback_trans (b ⁻¹ᵁ W).ι
    (X'.homOfLE (b.preimage_mono hW)) (Scheme.homOfLE_ι X' (b.preimage_mono hW))
    (pullbackFreeTrivPullbackIso b W N
      (((Scheme.Modules.restrictFunctorIsoPullback W.ι).app N).symm ≪≫ τ))
    (Scheme.Modules.pullbackFreeIso (X'.homOfLE (b.preimage_mono hW)) I)
    (pullbackFreeTrivPullbackIso b W' N
      (((Scheme.Modules.restrictFunctorIsoPullback W'.ι).app N).symm ≪≫ τ'))
    (pullbackFreeTrivPullbackIso_shrink b hW N
      (((Scheme.Modules.restrictFunctorIsoPullback W.ι).app N).symm ≪≫ τ)
      (((Scheme.Modules.restrictFunctorIsoPullback W'.ι).app N).symm ≪≫ τ')
      (pullbackCompIsoOfEq_hom_comp_of_restrictChartIso W.ι (X.homOfLE hW)
        (Scheme.homOfLE_ι X hW)
        (((Scheme.Modules.restrictFunctorIsoPullback W.ι).app N).symm ≪≫ τ)
        (Scheme.Modules.pullbackFreeIso (X.homOfLE hW) I)
        (((Scheme.Modules.restrictFunctorIsoPullback W'.ι).app N).symm ≪≫ τ')
        ((restrictChartIso_comp_free_iff _ (Iso.self_symm_id_assoc _ τ)
          (Iso.self_symm_id_assoc _ τ')).1 hτ)))
  exact (restrictChartIso_comp_free_iff _ (pullbackFreeTrivIso_eq b W N τ).symm
    (pullbackFreeTrivIso_eq b W' N τ').symm).2 hmain

end AlgebraicGeometry

end
