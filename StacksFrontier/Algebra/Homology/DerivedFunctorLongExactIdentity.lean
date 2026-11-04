module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections

/-!
# Right derived functors of a kernel of a left exact endofunctor

Let `A` be an abelian category with injective resolutions and let `F ⟶ 𝟭 ⟶ H` be a short complex of
additive endofunctors of `A` which is short exact at every injective object, with `H` left exact.
Typical examples are the functor `F = i_*ℋ_Z` of sections supported on a closed subset and
`H = j_*(-|_U)` the direct image of the restriction to the open complement, on sheaves on a
topological space or on a site.

The long exact sequence of right derived functors of `F ⟶ 𝟭 ⟶ H` collapses, the higher right
derived functors of the identity vanishing, and gives, for every object `X`,

* `R⁰F(X) = ker(X ⟶ H(X))`,
* `R¹F(X) = coker(X ⟶ H(X))`,
* `R^{n+1}F(X) = RⁿH(X)` for `n ≥ 1`.

## Main definitions

* `CategoryTheory.rightDerivedZeroIsoKernelOfShortExactOnInjectives`: `R⁰F(X) ≅ ker(X ⟶ H(X))`.
* `CategoryTheory.rightDerivedOneIsoCokernelOfShortExactOnInjectives`:
  `R¹F(X) ≅ coker(X ⟶ H(X))`.
* `CategoryTheory.rightDerivedSuccIsoOfShortExactOnInjectives`: `R^{n+1}F(X) ≅ RⁿH(X)` for
  `n ≥ 1`.
* `CategoryTheory.mapRightDerivedIsoOfShortExactOnInjectives`: transfer of all three
  identifications along an exact functor `Φ` which carries `X ⟶ H(X)` to `Φ X ⟶ H'(Φ X)` and
  commutes with the higher right derived functors of `H` at `X`, so that `Φ(RⁿF(X)) ≅ RⁿF'(Φ X)`.

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
* [Stacks Project, Tag 0G72](https://stacks.math.columbia.edu/tag/0G72)
-/

@[expose] public noncomputable section

universe v u v' u'

namespace CategoryTheory

open Category Limits

variable {A : Type u} [Category.{v} A] [Abelian A] [HasInjectiveResolutions A]
  {F H : A ⥤ A} [F.Additive] [H.Additive] [PreservesFiniteLimits H]
  (i : F ⟶ 𝟭 A) (q : 𝟭 A ⟶ H) (hiq : i ≫ q = 0)
  (hinj : ∀ X : A, Injective X → (NatTrans.appShortComplex i q hiq X).ShortExact)

/-- The degree-zero part of `q` on right derived functors is `q` itself, up to the canonical
identifications `X ≅ R⁰𝟭(X)` and `H(X) ≅ R⁰H(X)`. -/
def rightDerivedZeroArrowIso (X : A) :
    Arrow.mk ((NatTrans.rightDerived q 0).app X) ≅ Arrow.mk (q.app X) :=
  Arrow.isoMk (asIso ((𝟭 A).toRightDerivedZero.app X)).symm
    (asIso (H.toRightDerivedZero.app X)).symm (by
      dsimp
      rw [IsIso.inv_comp_eq, ← Category.assoc, Functor.toRightDerivedZero_naturality_app,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id])

include hinj in
/-- **`R⁰F(X) = ker(X ⟶ H(X))`** for a short complex `F ⟶ 𝟭 ⟶ H` short exact on injectives
with `H` left exact. -/
def rightDerivedZeroIsoKernelOfShortExactOnInjectives (X : A) :
    (F.rightDerived 0).obj X ≅ kernel (q.app X) := by
  have h := exact_rightDerived_composableArrows₅ i q hiq hinj (injectiveResolution X) 0
  have hS : (ShortComplex.mk ((NatTrans.rightDerived i 0).app X)
      ((NatTrans.rightDerived q 0).app X) (h.toIsComplex.zero' 0 1 2)).Exact := h.exact 0
  haveI : Mono ((NatTrans.rightDerived i 0).app X) := mono_rightDerived_zero_app i q hiq hinj X
  exact IsLimit.conePointUniqueUpToIso hS.fIsKernel (kernelIsKernel _) ≪≫
    kernel.mapIso _ _ (Arrow.leftFunc.mapIso (rightDerivedZeroArrowIso q X))
      (Arrow.rightFunc.mapIso (rightDerivedZeroArrowIso q X))
      (rightDerivedZeroArrowIso q X).hom.w.symm

include hinj in
/-- **`R¹F(X) = coker(X ⟶ H(X))`** for a short complex `F ⟶ 𝟭 ⟶ H` short exact on injectives
with `H` left exact. -/
def rightDerivedOneIsoCokernelOfShortExactOnInjectives (X : A) :
    (F.rightDerived 1).obj X ≅ cokernel (q.app X) := by
  have h := exact_rightDerived_composableArrows₅ i q hiq hinj (injectiveResolution X) 0
  have hS : (ShortComplex.mk ((NatTrans.rightDerived q 0).app X)
      (InjectiveResolution.rightDerivedDelta i q hiq hinj (injectiveResolution X) 0)
      (h.toIsComplex.zero' 1 2 3)).Exact := h.exact 1
  have hd : (ShortComplex.mk
      (InjectiveResolution.rightDerivedDelta i q hiq hinj (injectiveResolution X) 0)
      ((NatTrans.rightDerived i 1).app X) (h.toIsComplex.zero' 2 3 4)).Exact := h.exact 2
  haveI : Epi (InjectiveResolution.rightDerivedDelta i q hiq hinj (injectiveResolution X) 0) :=
    (ShortComplex.exact_iff_epi _
      ((Functor.isZero_rightDerived_of_exact (𝟭 A) X 1 Nat.one_pos).eq_of_tgt _ 0)).1 hd
  exact (IsColimit.coconePointUniqueUpToIso hS.gIsCokernel (cokernelIsCokernel _) ≪≫
    cokernel.mapIso _ _ (Arrow.leftFunc.mapIso (rightDerivedZeroArrowIso q X))
      (Arrow.rightFunc.mapIso (rightDerivedZeroArrowIso q X))
      (rightDerivedZeroArrowIso q X).hom.w.symm)

include hinj in
/-- **`R^{n+1}F(X) = RⁿH(X)` for `n ≥ 1`**, the isomorphism being the connecting morphism of the
long exact sequence of right derived functors. -/
def rightDerivedSuccIsoOfShortExactOnInjectives (X : A) (n : ℕ) (hn : 0 < n) :
    (H.rightDerived n).obj X ≅ (F.rightDerived (n + 1)).obj X := by
  have h := exact_rightDerived_composableArrows₅ i q hiq hinj (injectiveResolution X) n
  have hb : (ShortComplex.mk ((NatTrans.rightDerived q n).app X)
      (InjectiveResolution.rightDerivedDelta i q hiq hinj (injectiveResolution X) n)
      (h.toIsComplex.zero' 1 2 3)).Exact := h.exact 1
  have hd : (ShortComplex.mk
      (InjectiveResolution.rightDerivedDelta i q hiq hinj (injectiveResolution X) n)
      ((NatTrans.rightDerived i (n + 1)).app X) (h.toIsComplex.zero' 2 3 4)).Exact := h.exact 2
  haveI : Mono (InjectiveResolution.rightDerivedDelta i q hiq hinj (injectiveResolution X) n) :=
    (ShortComplex.exact_iff_mono _
      ((Functor.isZero_rightDerived_of_exact (𝟭 A) X n hn).eq_of_src _ 0)).1 hb
  haveI : Epi (InjectiveResolution.rightDerivedDelta i q hiq hinj (injectiveResolution X) n) :=
    (ShortComplex.exact_iff_epi _
      ((Functor.isZero_rightDerived_of_exact (𝟭 A) X (n + 1) (by omega)).eq_of_tgt _ 0)).1 hd
  haveI := isIso_of_mono_of_epi
    (InjectiveResolution.rightDerivedDelta i q hiq hinj (injectiveResolution X) n)
  exact asIso (InjectiveResolution.rightDerivedDelta i q hiq hinj (injectiveResolution X) n)

section Transfer

/-! ### Transfer along an exact functor -/

variable {A' : Type u'} [Category.{v'} A'] [Abelian A'] [HasInjectiveResolutions A']
  {F' H' : A' ⥤ A'} [F'.Additive] [H'.Additive] [PreservesFiniteLimits H']
  (i' : F' ⟶ 𝟭 A') (q' : 𝟭 A' ⟶ H') (hiq' : i' ≫ q' = 0)
  (hinj' : ∀ X : A', Injective X → (NatTrans.appShortComplex i' q' hiq' X).ShortExact)
  (Φ : A ⥤ A') [Φ.PreservesZeroMorphisms]

include hinj hinj' in
/-- **Transfer of `R⁰F` along a left exact functor.**  If `Φ` preserves finite limits and carries
`q_X : X ⟶ H(X)` to `q'_{Φ X}` up to an isomorphism `Φ(H(X)) ≅ H'(Φ(X))`, then
`Φ(R⁰F(X)) ≅ R⁰F'(Φ(X))`: both are the kernels of the two arrows. -/
def mapRightDerivedZeroIsoOfShortExactOnInjectives [PreservesFiniteLimits Φ] (X : A)
    (e₀ : Φ.obj (H.obj X) ≅ H'.obj (Φ.obj X)) (hw : Φ.map (q.app X) ≫ e₀.hom = q'.app (Φ.obj X)) :
    Φ.obj ((F.rightDerived 0).obj X) ≅ (F'.rightDerived 0).obj (Φ.obj X) :=
  Φ.mapIso (rightDerivedZeroIsoKernelOfShortExactOnInjectives i q hiq hinj X) ≪≫
    PreservesKernel.iso Φ (q.app X) ≪≫
    kernel.mapIso _ _ (Iso.refl _) e₀ (by simp [hw]) ≪≫
    (rightDerivedZeroIsoKernelOfShortExactOnInjectives i' q' hiq' hinj' (Φ.obj X)).symm

include hinj hinj' in
/-- **Transfer of `R¹F` along a right exact functor.**  If `Φ` preserves finite colimits and
carries `q_X : X ⟶ H(X)` to `q'_{Φ X}` up to an isomorphism `Φ(H(X)) ≅ H'(Φ(X))`, then
`Φ(R¹F(X)) ≅ R¹F'(Φ(X))`: both are the cokernels of the two arrows. -/
def mapRightDerivedOneIsoOfShortExactOnInjectives [PreservesFiniteColimits Φ] (X : A)
    (e₀ : Φ.obj (H.obj X) ≅ H'.obj (Φ.obj X)) (hw : Φ.map (q.app X) ≫ e₀.hom = q'.app (Φ.obj X)) :
    Φ.obj ((F.rightDerived 1).obj X) ≅ (F'.rightDerived 1).obj (Φ.obj X) :=
  Φ.mapIso (rightDerivedOneIsoCokernelOfShortExactOnInjectives i q hiq hinj X) ≪≫
    PreservesCokernel.iso Φ (q.app X) ≪≫
    cokernel.mapIso _ _ (Iso.refl _) e₀ (by simp [hw]) ≪≫
    (rightDerivedOneIsoCokernelOfShortExactOnInjectives i' q' hiq' hinj' (Φ.obj X)).symm

include hinj hinj' in
/-- **Transfer of `RⁿF` along an exact functor, in every degree.**  Let `F ⟶ 𝟭 ⟶ H` and
`F' ⟶ 𝟭 ⟶ H'` be short complexes of endofunctors, short exact on injectives with `H` and `H'`
left exact, and let `Φ` be an exact functor.  Suppose that, at an object `X`, `Φ` carries
`q_X : X ⟶ H(X)` to `q'_{Φ X}` up to an isomorphism `Φ(H(X)) ≅ H'(Φ(X))`, and that
`Φ(RᵖH(X)) ≅ RᵖH'(Φ(X))` for every `p ≥ 1`.  Then `Φ(RⁿF(X)) ≅ RⁿF'(Φ(X))` for every `n`.

In degrees `0` and `1` this is `mapRightDerivedZeroIsoOfShortExactOnInjectives` and
`mapRightDerivedOneIsoOfShortExactOnInjectives`; in degree `p + 1 ≥ 2` it is the given
isomorphism in degree `p`, read through `R^{p+1}F = RᵖH` on both sides. -/
def mapRightDerivedIsoOfShortExactOnInjectives [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] (X : A)
    (e₀ : Φ.obj (H.obj X) ≅ H'.obj (Φ.obj X)) (hw : Φ.map (q.app X) ≫ e₀.hom = q'.app (Φ.obj X))
    (e : ∀ p : ℕ, 0 < p → (Φ.obj ((H.rightDerived p).obj X) ≅ (H'.rightDerived p).obj (Φ.obj X)))
    : ∀ n : ℕ, Φ.obj ((F.rightDerived n).obj X) ≅ (F'.rightDerived n).obj (Φ.obj X)
  | 0 => mapRightDerivedZeroIsoOfShortExactOnInjectives i q hiq hinj i' q' hiq' hinj' Φ X e₀ hw
  | 1 => mapRightDerivedOneIsoOfShortExactOnInjectives i q hiq hinj i' q' hiq' hinj' Φ X e₀ hw
  | p + 2 =>
    Φ.mapIso (rightDerivedSuccIsoOfShortExactOnInjectives i q hiq hinj X (p + 1) p.succ_pos).symm ≪≫
      e (p + 1) p.succ_pos ≪≫
      rightDerivedSuccIsoOfShortExactOnInjectives i' q' hiq' hinj' (Φ.obj X) (p + 1) p.succ_pos

end Transfer

end CategoryTheory
