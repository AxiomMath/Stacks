module

public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.AffineCase
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocalQuasiCompact

/-!
# Dense test valuative criterion: reduction to an affine Noetherian base

Let `f : 𝒳 ⟶ 𝒴` be a separated morphism of finite type of algebraic stacks with `𝒴` locally
Noetherian, and `h : 𝒰 ⟶ 𝒳` of finite type with dense image, such that `h` and `f` satisfy the
existence part of the valuative criterion for dense test morphisms. If over every smooth chart
`Spec A ⟶ 𝒴` with `A` Noetherian the base change of `f` admits a surjective universally closed
scheme cover satisfying the existence part of the valuative criterion, whose composite to
`Spec A` is separated, quasi-compact and locally of finite type, then `f` is proper.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_denseTestExistence_of_forall_affine`: `f` is
  proper if the base change of `f` to every smooth affine Noetherian chart of `𝒴` has such a cover.

## References

* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- Over a smooth chart `g : Spec A ⟶ 𝒴` with `A` Noetherian, the base change `P.fst` of a
dense-test-existence morphism `f` is universally closed once `P.pt` has a suitable scheme cover. -/
private theorem universallyClosed_fst_of_denseTestExistence_of_cover
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (h : 𝒰 ⟶ 𝒳)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : letI := Stack.pointTopology B S hS 𝒳.val
      Dense (Set.range (AlgebraicStacks.pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DenseTestExistence B S hS h f)
    {A : CommRingCat.{u}} (hA : B.Contains (Spec A)) (a : Spec A ⟶ S) [IsNoetherianRing A]
    (g : schemeStack.{u, w} B S hS (siteObject B S hS hA a) ⟶ 𝒴) (hg : IsSmooth B S hS g)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hcover : ∃ (X' : BigFppfOver B S hS) (p : schemeStack.{u, w} B S hS X' ⟶ P.pt)
        (φ : X' ⟶ siteObject B S hS hA a),
        UniversallyClosed B S hS p ∧ ValuativeCriterion.Existence B S hS p ∧
        Stack.IsSurjective B S hS p ∧
        _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map φ) ∧
        LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map φ) ∧
        QuasiCompact ((BigFppfOver.toScheme B S hS).map φ) ∧
        Nonempty (p ≫ P.fst ≅ schemeStackMap.{u, w} B S hS φ)) :
    UniversallyClosed B S hS P.fst := by
  obtain ⟨X', p, φ, hpuc, hpex, hps, hφsep, hφlft, hφqc, ⟨eφ⟩⟩ := hcover
  let Q := twoFibreProductSquareAlgebraicStacks B S hS P.snd h
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS P.snd h
  have hsep' : IsSeparated B S hS P.fst :=
    isSeparated_baseChange_of_isTwoFibreProduct B S hS f g P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hsep
  have hlift' : ValuativeCriterion.DenseTestExistence B S hS Q.fst P.fst :=
    ValuativeCriterion.denseTestExistence_baseChange B S hS f g P hP h Q.fst Q.snd Q.iso hlift
  have hdense' : letI := Stack.pointTopology B S hS P.pt.val
      Dense (Set.range (AlgebraicStacks.pointsMap B S hS Q.fst)) := by
    let := Stack.pointTopology B S hS P.pt.val
    let := Stack.pointTopology B S hS 𝒳.val
    refine (hdense.preimage (isOpenMap_pointsMap_of_isSmooth B S hS P.snd
      (isSmooth_baseChange B S hS g f P.swap (Bicategory.isTwoFibreProduct_swap hP) hg))).mono ?_
    rintro x ⟨u₀, hu₀⟩
    obtain ⟨pt, hpt, -⟩ :=
      exists_point_of_isTwoFibreProduct_algebraicStacks B S hS Q hQ x u₀ hu₀.symm
    exact ⟨pt, hpt⟩
  exact (isProper_of_denseTestExistence_of_schemeCover B S hS
    (inferInstanceAs (IsAffine (Spec A))) (inferInstanceAs (IsLocallyNoetherian (Spec A)))
    P.fst Q.fst (isFiniteType_baseChange B S hS f g P hP hf)
    (isFiniteType_baseChange B S hS h P.snd Q hQ hh) hsep' hdense' hlift' p hpuc hpex hps φ hφsep
    hφlft hφqc eφ).2.2

/-- Let `f : 𝒳 ⟶ 𝒴` be a separated morphism of finite type of algebraic stacks with `𝒴` locally
Noetherian, and `h : 𝒰 ⟶ 𝒳` a morphism of finite type with dense image such that `h` and `f`
satisfy the existence part of the valuative criterion for dense test morphisms. Suppose that for
every smooth 1-morphism `g : Spec A ⟶ 𝒴` with `A` Noetherian and every 2-fibre product `P` of `g`
and `f`, the base change `P.pt` has a surjective universally closed scheme cover satisfying the
existence part of the valuative criterion, whose composite to `Spec A` is induced by a separated
quasi-compact morphism of schemes locally of finite type. Then `f` is proper. -/
theorem isProper_of_denseTestExistence_of_forall_affine
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (h : 𝒰 ⟶ 𝒳)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : letI := Stack.pointTopology B S hS 𝒳.val
      Dense (Set.range (AlgebraicStacks.pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DenseTestExistence B S hS h f)
    (hcover : ∀ (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S),
      IsNoetherianRing A →
      ∀ (g : schemeStack.{u, w} B S hS (siteObject B S hS hA a) ⟶ 𝒴), IsSmooth B S hS g →
      ∀ (P : Bicategory.TwoCommSq g f), Bicategory.IsTwoFibreProduct P →
      ∃ (X' : BigFppfOver B S hS) (p : schemeStack.{u, w} B S hS X' ⟶ P.pt)
        (φ : X' ⟶ siteObject B S hS hA a),
        UniversallyClosed B S hS p ∧ ValuativeCriterion.Existence B S hS p ∧
        Stack.IsSurjective B S hS p ∧
        _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map φ) ∧
        LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map φ) ∧
        QuasiCompact ((BigFppfOver.toScheme B S hS).map φ) ∧
        Nonempty (p ≫ P.fst ≅ schemeStackMap.{u, w} B S hS φ)) :
    IsProper B S hS f := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U, bStack, hbsurj, hbsm, hU⟩ := h𝒴
  let A : (T.obj U).affineOpens → CommRingCat.{u} := fun O => Γ(T.obj U, O.1)
  have hA : ∀ O, B.Contains (Spec (A O)) := fun O => by
    show (Spec (A O)).size < B.cutoff
    rw [← Scheme.size_congr O.2.isoSpec]
    exact (Scheme.size_coe_opens_le (T.obj U) O.1).trans_lt U.left.property
  let ιO : ∀ O, Spec (A O) ⟶ T.obj U := fun O => O.2.isoSpec.inv ≫ O.1.ι
  let aO : ∀ O, Spec (A O) ⟶ S := fun O => ιO O ≫ B.inclusion.map U.hom
  let V : (T.obj U).affineOpens → BigFppfOver B S hS := fun O => siteObject B S hS (hA O) (aO O)
  let jO : ∀ O, V O ⟶ U := fun O => Over.homMk (⟨ιO O⟩ : (V O).left ⟶ U.left) rfl
  let gO : ∀ O, schemeStack.{u, w} B S hS (V O) ⟶ 𝒴 := fun O =>
    schemeStackMap.{u, w} B S hS (jO O) ≫ bStack
  have hgO : ∀ O, IsSmooth B S hS (gO O) := fun O =>
    isSmooth_comp B S hS _ _ (isSmooth_schemeStackMap.{u, w} B S hS (jO O)
      (inferInstanceAs (Smooth (O.2.isoSpec.inv ≫ O.1.ι)))) hbsm
  have hAN : ∀ O, IsNoetherianRing (A O) := fun O =>
    IsLocallyNoetherian.component_noetherian (X := T.obj U) O
  refine ⟨hsep, hf, ?_⟩
  refine universallyClosed_of_universallyClosed_smooth_cover B S hS f
    (fun O => schemeStack.{u, w} B S hS (V O)) gO hgO ?_ ?_
  · intro y
    obtain ⟨v, hv⟩ := hbsurj y
    let z : T.obj U := schemePoint B S hS U v
    obtain ⟨O, hO, hzO, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) (by simp)
    let O' : (T.obj U).affineOpens := ⟨O, hO⟩
    obtain ⟨z', hz'⟩ : ∃ z' : Spec (A O'), ιO O' z' = z :=
      ⟨O'.2.isoSpec.hom ⟨z, hzO⟩, congrArg O.ι (Scheme.hom_inv_apply _ _)⟩
    obtain ⟨t, ht⟩ := schemePoint_surjective B S hS (V O') z'
    refine ⟨O', t, ?_⟩
    rw [pointsMap_comp, Function.comp_apply, ← hv]
    refine congrArg (AlgebraicStacks.pointsMap B S hS bStack) ?_
    apply schemePoint_injective B S hS U
    rw [schemePoint_naturality]
    exact (congrArg (fun m => T.map m (schemePoint B S hS (V O') t))
      (siteMap_schemeStackMap.{u, w} B S hS (jO O'))).trans (ht ▸ hz')
  · intro O
    have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (gO O) f
    exact universallyClosed_fst_of_denseTestExistence_of_cover B S hS f h hf hh hsep
      hdense hlift (hA O) (aO O) (gO O) (hgO O) _ hP
      (hcover (A O) (hA O) (aO O) (hAN O) (gO O) (hgO O) _ hP)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
