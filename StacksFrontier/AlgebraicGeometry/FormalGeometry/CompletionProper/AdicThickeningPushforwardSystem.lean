module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicThickeningUnwinding
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicPictureBridges
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicThickeningTransitionDescent
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist

/-!
# The direct image of a system on the adic thickenings

Work in the situation of [Stacks, Tag 088F]: `A` is Noetherian, `I ⊆ A` an ideal,
`f : X ⟶ Spec A` locally of finite type, `Xₙ = X ×_{Spec A} Sₙ` with projections
`vₙ : Xₙ ⟶ X` and transitions `iₙ : Xₙ ⟶ Xₙ₊₁`. A system `(ℱₙ, φₙ)` of
`AlgebraicGeometry.AdicCoherentModuleSystem` lives on the thickenings; the category
[Stacks, Tag 088E] is stated against in this library,
`Stacks.Algebraization.CoherentAdicSystemsProperOver`, is made of inverse systems of coherent
`𝒪_X`-modules on `X` with quotient transitions. This file carries a system of the first kind to
one of the second, by termwise direct image:

  `𝓝ₙ = (vₙ)_* ℱₙ`,  with transition `(vₙ₊₁)_* ℱₙ₊₁ ⟶ (vₙ)_* ℱₙ` built from `φₙ`.

It is the direction opposite to
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicThickeningUnwinding.lean`, which reads the
terms of a completion on `X` as direct images; here nothing is assumed to be a completion.

## Main definitions

* `AlgebraicGeometry.closedImmersionCounitIso` — the counit `i^* i_* 𝒢 ≅ 𝒢` of a closed
  immersion, an isomorphism because direct image along a closed immersion is fully faithful
  ([Stacks, Tag 08KS]).
* `AlgebraicGeometry.adicPushforwardObj`, `adicPushforwardTransition` and
  `adicPushforwardSystemFunctor` — the terms, the transitions and the resulting inverse system
  on `X`.
* `AlgebraicGeometry.adicPushforwardPullbackIso` — the restriction `vₙ^*((vₙ₊₁)_* ℱₙ₊₁) ≅ ℱₙ`,
  the counit of `iₙ` read through the factorisation `iₙ ≫ vₙ₊₁ = vₙ` and then through `φₙ`.
* `AlgebraicGeometry.adicPushforwardSystem` — the object of
  `Stacks.Algebraization.CoherentAdicSystemsProperOver f (baseIdealSheaf A I f)`.

## Main results

* `AlgebraicGeometry.unit_comp_map_eq_pushUnit_comp_map` — **the normalization**, over variable
  schemes: for a factorisation `c ≫ h = k`, the unit of `k^* ⊣ k_*` at `h_* G` followed by the
  direct image of a map `k^*(h_* G) ⟶ G'` compatible with the counit of `h` is
  `Stacks.Descent.pushUnit` followed by the direct image of that map. The proof is the unit
  cocycle `AlgebraicGeometry.unit_comp_pushUnit_comp_map_pullbackCompHom`, the naturality of
  `pushUnit`, and the right triangle of the adjunction.
* `AlgebraicGeometry.pullback_map_comp_eq_of_unit_comp` — **the transition square, reflected to
  the thickening**, over variable schemes: a square between units on the base, tested against
  the epimorphism `unit^h ≫ pushUnit`, descends through faithfulness of `k_*` to the square
  between the restrictions. This is what turns an isomorphism of systems on `X` into a morphism
  of systems on the thickenings.
* `AlgebraicGeometry.isCoherentAdicSystem_adicPushforwardSystemFunctor` — the three clauses of
  `Stacks.Coherent.IsCoherentAdicSystem`. Coherence is [Stacks, Tag 087T]; the annihilation is
  `Stacks.Algebraization.idealPower_smul_pushforward_eq_bot_of_ker` at
  `AlgebraicGeometry.AdicFiniteAlgebra.ker_adicBaseChange_fst`; the quotient-transition clause is
  [Stacks, Tag 0EL1] at the module `(vₙ₊₁)_* ℱₙ₊₁`
  (`Stacks.Algebraization.idealQuotientPushforwardIso`) composed with
  `adicPushforwardPullbackIso`, and that the composite intertwines the cokernel projection with
  the transition is the normalization above.
* `AlgebraicGeometry.hasProperSupport_adicPushforwardObj_zero` — **clause (3) crosses from `S₁`
  to `Spec A`.** The support of `(v₀)_* ℱ₀` is the image of the support of `ℱ₀`
  (`AlgebraicGeometry.supp_pushforward_of_isClosedImmersion`), and the image of a closed subset
  proper over the base is proper over the base ([Stacks, Tag 0CYQ],
  `AlgebraicGeometry.isProperOver_closedImage`), the base change `X₀ ⟶ S₁ ⟶ Spec A` being a
  composite of proper morphisms.

## Implementation notes

The two squares are stated over variable schemes with every comparison map a binder named by an
equation, for the reason recorded in the module docstring of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicThickeningTransitionDescent`:
at the adic morphisms `k = vₙ` is a projection out of a fibre product, the equation
`iₙ ≫ vₙ₊₁ = vₙ` cannot be substituted, and transporting a conclusion along it exhausts the
kernel.

`AlgebraicGeometry.adicPushforwardPullbackIso_hom` spells the isomorphism out as a composite and
is proved by `rfl`; it is what lets the normalization be applied with its two comparison binders
given explicitly, so that no `def` has to be unfolded by unification. Without it the
normalization times out at `whnf`.

## References

* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0CYQ](https://stacks.math.columbia.edu/tag/0CYQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace AlgebraicGeometry

open Stacks.Algebraization
open Stacks.Descent (pushUnit pullbackCompHom)

/-! ### Two squares over variable schemes -/

section Generic

variable {Z Z' Z'' : Scheme.{u}}

/-- **The normalization of the quotient transition of a direct image.** -/
public theorem unit_comp_map_eq_pushUnit_comp_map (h : Z' ⟶ Z) (c : Z'' ⟶ Z')
    {k : Z'' ⟶ Z} (hk : c ≫ h = k) (G : Z'.Modules) (G' : Z''.Modules)
    (φ : (Scheme.Modules.pullback c).obj G ⟶ G')
    {Θ : (Scheme.Modules.pullback c).obj
        ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pushforward h).obj G)) ⟶
      (Scheme.Modules.pullback k).obj ((Scheme.Modules.pushforward h).obj G)}
    (hΘ : Θ = pullbackCompHom c h k hk ((Scheme.Modules.pushforward h).obj G))
    {ψ : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pushforward h).obj G) ⟶ G'}
    (hψ : Θ ≫ ψ = (Scheme.Modules.pullback c).map
        ((Scheme.Modules.pullbackPushforwardAdjunction h).counit.app G) ≫ φ) :
    (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app
          ((Scheme.Modules.pushforward h).obj G) ≫
        (Scheme.Modules.pushforward k).map ψ =
      (pushUnit h c k hk).app G ≫ (Scheme.Modules.pushforward k).map φ := by
  have hcoc := unit_comp_pushUnit_comp_map_pullbackCompHom h c hk
    ((Scheme.Modules.pushforward h).obj G)
  have hnat := (pushUnit h c k hk).naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction h).counit.app G)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hnat
  have htri := (Scheme.Modules.pullbackPushforwardAdjunction h).right_triangle_components
    (Y := G)
  rw [← hcoc, ← hΘ]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [hψ, Functor.map_comp, ← Category.assoc ((pushUnit h c k hk).app
    ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pushforward h).obj G))), ← hnat]
  simp only [← Category.assoc]
  rw [htri]
  exact congrArg (fun z => z ≫ (Scheme.Modules.pushforward k).map φ)
    (Category.id_comp ((pushUnit h c k hk).app G))

/-- **The transition square of a family of morphisms, reflected to the thickening.** -/
public theorem pullback_map_comp_eq_of_unit_comp (h : Z' ⟶ Z) (c : Z'' ⟶ Z')
    {k : Z'' ⟶ Z} (hk : c ≫ h = k)
    (hfaith : (Scheme.Modules.pushforward k).Faithful)
    (M : Z.Modules) (G : Z'.Modules) (G' : Z''.Modules)
    (φ : (Scheme.Modules.pullback c).obj G ⟶ G')
    (θ' : (Scheme.Modules.pullback h).obj M ⟶ G)
    (θ : (Scheme.Modules.pullback k).obj M ⟶ G')
    {Θ : (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback h).obj M) ⟶
      (Scheme.Modules.pullback k).obj M}
    (hΘ : Θ = pullbackCompHom c h k hk M)
    {T : (Scheme.Modules.pushforward h).obj G ⟶ (Scheme.Modules.pushforward k).obj G'}
    (hT : (pushUnit h c k hk).app G ≫ (Scheme.Modules.pushforward k).map φ = T)
    (hepi : Epi ((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M))
    (hsq : (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M ≫
        (Scheme.Modules.pushforward h).map θ' ≫ T =
      (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M ≫
        (Scheme.Modules.pushforward k).map θ) :
    (Scheme.Modules.pullback c).map θ' ≫ φ = Θ ≫ θ := by
  have := hfaith
  have hiso : IsIso Θ := by rw [hΘ]; infer_instance
  have hcoc : (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M ≫
      (pushUnit h c k hk).app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pushforward k).map Θ =
      (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M := by
    rw [hΘ]; exact unit_comp_pushUnit_comp_map_pullbackCompHom h c hk M
  have hnat := (pushUnit h c k hk).naturality θ'
  simp only [Functor.comp_map] at hnat
  have hu : Epi ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M ≫
      (pushUnit h c k hk).app ((Scheme.Modules.pullback h).obj M)) := by
    have hfac : (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M ≫
        (pushUnit h c k hk).app ((Scheme.Modules.pullback h).obj M) =
        (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M ≫
          CategoryTheory.inv ((Scheme.Modules.pushforward k).map Θ) := by
      rw [← hcoc]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [hfac]
    exact @epi_comp _ _ _ _ _ _ hepi _ inferInstance
  refine (Scheme.Modules.pushforward k).map_injective ?_
  refine (@cancel_epi _ _ _ _ _ _ hu _ _).mp ?_
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    ← Category.assoc ((pushUnit h c k hk).app ((Scheme.Modules.pullback h).obj M)), ← hnat,
    Category.assoc, hT, hsq, ← hcoc]
  simp only [Category.assoc]

end Generic

/-! ### The counit along a closed immersion -/

/-- **The counit of `i^* ⊣ i_*` at a closed immersion is an isomorphism**: direct image along a
closed immersion is fully faithful (Stacks 08KS, as
`Stacks.ClosedImmersion.fullyFaithfulPushforward`), and the counit of an adjunction whose right
adjoint is fully faithful is an isomorphism. -/
public def closedImmersionCounitIso {Z W : Scheme.{u}} (i : Z ⟶ W)
    [IsClosedImmersion i] (G : Z.Modules) :
    (Scheme.Modules.pullback i).obj ((Scheme.Modules.pushforward i).obj G) ≅ G :=
  haveI := (Stacks.ClosedImmersion.fullyFaithfulPushforward i).full
  haveI := (Stacks.ClosedImmersion.fullyFaithfulPushforward i).faithful
  asIso ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G)

/-- `AlgebraicGeometry.closedImmersionCounitIso` is the counit. -/
public theorem closedImmersionCounitIso_hom {Z W : Scheme.{u}} (i : Z ⟶ W)
    [IsClosedImmersion i] (G : Z.Modules) :
    (closedImmersionCounitIso i G).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G :=
  rfl

/-! ### The direct image of a system on the thickenings -/

section Adic

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [IsLocallyNoetherian X] [LocallyOfFiniteType f]

/-- The direct image on `X` of the `n`-th term of a system on the adic thickenings. -/
public def adicPushforwardObj (S : AdicCoherentModuleSystem A I f) (n : ℕ) : X.Modules :=
  (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).obj (S.obj n)

/-- The direct image of a coherent module on a thickening is coherent. -/
public theorem isCoherent_adicPushforwardObj (S : AdicCoherentModuleSystem A I f) (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} (adicPushforwardObj A I f S n) :=
  have := S.isCoherent n
  isCoherent_pushforward_of_isClosedImmersion (pullback.fst f (adicThickeningι A I n)) (S.obj n)

omit [IsLocallyNoetherian X] in
/-- The direct image of the `n`-th term is annihilated by `𝓘 ⁿ⁺¹`. -/
public theorem idealPowerMultiple_adicPushforwardObj (S : AdicCoherentModuleSystem A I f)
    (n : ℕ) :
    idealPowerMultiple (baseIdealSheaf A I f) (n + 1) (adicPushforwardObj A I f S n) = ⊥ :=
  (idealPowerMultiple_eq_bot_iff_affine_smul_top _ _ _).2
    (idealPower_smul_pushforward_eq_bot_of_ker (baseIdealSheaf A I f) (n + 1)
      (pullback.fst f (adicThickeningι A I n)) (AdicFiniteAlgebra.ker_adicBaseChange_fst A I f n)
      (S.obj n))

/-- The restriction to `Xₙ` of the direct image of `ℱₙ₊₁` is `ℱₙ`. -/
public def adicPushforwardPullbackIso (S : AdicCoherentModuleSystem A I f) (n : ℕ) :
    (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).obj
        (adicPushforwardObj A I f S (n + 1)) ≅ S.obj n :=
  (asIso (pullbackCompHom (adicBaseChangeSucc A I f n)
      (pullback.fst f (adicThickeningι A I (n + 1)))
      (pullback.fst f (adicThickeningι A I n)) (adicBaseChangeSucc_fst A I f n)
      (adicPushforwardObj A I f S (n + 1)))).symm ≪≫
    ((Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).mapIso
        (closedImmersionCounitIso (pullback.fst f (adicThickeningι A I (n + 1)))
          (S.obj (n + 1))) ≪≫
      S.transitionIso n)

omit [IsLocallyNoetherian X] in
/-- `AlgebraicGeometry.adicPushforwardPullbackIso` written out. -/
public theorem adicPushforwardPullbackIso_hom (S : AdicCoherentModuleSystem A I f) (n : ℕ) :
    (adicPushforwardPullbackIso A I f S n).hom =
      CategoryTheory.inv (pullbackCompHom (adicBaseChangeSucc A I f n)
          (pullback.fst f (adicThickeningι A I (n + 1)))
          (pullback.fst f (adicThickeningι A I n)) (adicBaseChangeSucc_fst A I f n)
          (adicPushforwardObj A I f S (n + 1))) ≫
        ((Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (pullback.fst f (adicThickeningι A I (n + 1)))).counit.app (S.obj (n + 1))) ≫
          (S.transitionIso n).hom) :=
  rfl

/-- The transition of the direct image system. -/
public def adicPushforwardTransition (S : AdicCoherentModuleSystem A I f) (n : ℕ) :
    adicPushforwardObj A I f S (n + 1) ⟶ adicPushforwardObj A I f S n :=
  (pushUnit (pullback.fst f (adicThickeningι A I (n + 1))) (adicBaseChangeSucc A I f n)
        (pullback.fst f (adicThickeningι A I n)) (adicBaseChangeSucc_fst A I f n)).app
      (S.obj (n + 1)) ≫
    (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map
      (S.transitionIso n).hom

omit [IsLocallyNoetherian X] in
/-- **The normalization of the transition of the direct image system.** -/
public theorem unit_comp_map_adicPushforwardPullbackIso (S : AdicCoherentModuleSystem A I f)
    (n : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction
            (pullback.fst f (adicThickeningι A I n))).unit.app
          (adicPushforwardObj A I f S (n + 1)) ≫
        (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map
          (adicPushforwardPullbackIso A I f S n).hom =
      adicPushforwardTransition A I f S n := by
  refine unit_comp_map_eq_pushUnit_comp_map (pullback.fst f (adicThickeningι A I (n + 1)))
    (adicBaseChangeSucc A I f n) (adicBaseChangeSucc_fst A I f n) (S.obj (n + 1)) (S.obj n)
    (S.transitionIso n).hom (Θ := pullbackCompHom (adicBaseChangeSucc A I f n)
      (pullback.fst f (adicThickeningι A I (n + 1)))
      (pullback.fst f (adicThickeningι A I n)) (adicBaseChangeSucc_fst A I f n)
      (adicPushforwardObj A I f S (n + 1)))
    (ψ := (adicPushforwardPullbackIso A I f S n).hom) rfl ?_
  rw [adicPushforwardPullbackIso_hom]
  exact IsIso.hom_inv_id_assoc (pullbackCompHom (adicBaseChangeSucc A I f n)
    (pullback.fst f (adicThickeningι A I (n + 1)))
    (pullback.fst f (adicThickeningι A I n)) (adicBaseChangeSucc_fst A I f n)
    (adicPushforwardObj A I f S (n + 1))) _

/-- The inverse system on `X` of the direct images of the terms of a system on the
thickenings. -/
public def adicPushforwardSystemFunctor (S : AdicCoherentModuleSystem A I f) :
    ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence (X := fun n => adicPushforwardObj A I f S n)
    (fun n => adicPushforwardTransition A I f S n)

/-- **The direct images of the terms of a system on the thickenings form a coherent adic
system.** -/
public theorem isCoherentAdicSystem_adicPushforwardSystemFunctor
    (S : AdicCoherentModuleSystem A I f) :
    Stacks.Coherent.IsCoherentAdicSystem (baseIdealSheaf A I f)
      (adicPushforwardSystemFunctor A I f S) := by
  refine ⟨fun n => isCoherent_adicPushforwardObj A I f S n,
    fun n => idealPowerMultiple_adicPushforwardObj A I f S n, fun n => ?_⟩
  have := isCoherent_adicPushforwardObj A I f S (n + 1)
  have : (adicPushforwardObj A I f S (n + 1)).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  refine ⟨idealQuotientPushforwardIso (baseIdealSheaf A I f) (n + 1)
      (adicPushforwardObj A I f S (n + 1)) (pullback.fst f (adicThickeningι A I n))
      (AdicFiniteAlgebra.ker_adicBaseChange_fst A I f n) ≪≫
    (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).mapIso
      (adicPushforwardPullbackIso A I f S n), ?_⟩
  refine Eq.trans (congrArg (fun z => cokernel.π (C := X.Modules)
      ((idealPowerMultiple (baseIdealSheaf A I f) (n + 1)
        (adicPushforwardObj A I f S (n + 1))).ι) ≫ z)
    (Iso.trans_hom _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
      (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map
        (adicPushforwardPullbackIso A I f S n).hom)
    (idealQuotientPushforwardMap_π (baseIdealSheaf A I f) (n + 1)
      (adicPushforwardObj A I f S (n + 1)) (pullback.fst f (adicThickeningι A I n))
      (AdicFiniteAlgebra.ker_adicBaseChange_fst A I f n))) ?_
  exact (unit_comp_map_adicPushforwardPullbackIso A I f S n).trans
    (Functor.ofOpSequence_map_homOfLE_succ _ n).symm

omit [IsLocallyNoetherian X] in
/-- **The support of the first direct image is proper over `Spec A`.** -/
public theorem hasProperSupport_adicPushforwardObj_zero (S : AdicCoherentModuleSystem A I f) :
    HasProperSupport f (adicPushforwardObj A I f S 0) := by
  obtain ⟨W, hWeq, hWproper⟩ := S.properSupport
  have : IsClosedImmersion (adicThickeningι A I 0) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))) Ideal.Quotient.mk_surjective
  have : IsProper (adicThickeningι A I 0) := inferInstance
  refine ⟨(pullback.fst f (adicThickeningι A I 0)).closedImage W, ?_, ?_⟩
  · refine Eq.trans ?_ (supp_pushforward_of_isClosedImmersion
      (pullback.fst f (adicThickeningι A I 0)) (S.obj 0)).symm
    exact congrArg (fun s => (pullback.fst f (adicThickeningι A I 0)).base '' s) hWeq
  · refine isProperOver_closedImage (pullback.fst f (adicThickeningι A I 0)) f W ?_
    have h1 : IsProper ((Scheme.IdealSheafData.vanishingIdeal W).subschemeι ≫
      pullback.snd f (adicThickeningι A I 0)) := hWproper
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal W).subschemeι ≫
      pullback.fst f (adicThickeningι A I 0) ≫ f)
    rw [pullback.condition, ← Category.assoc]
    infer_instance

/-- **The direct image of a system on the thickenings, as an object of the category Stacks 088E
is stated against.** -/
public def adicPushforwardSystem (S : AdicCoherentModuleSystem A I f) :
    CoherentAdicSystemsProperOver f (baseIdealSheaf A I f) :=
  ⟨⟨adicPushforwardSystemFunctor A I f S,
      isCoherentAdicSystem_adicPushforwardSystemFunctor A I f S⟩,
    hasProperSupport_adicPushforwardObj_zero A I f S⟩

end Adic

end AlgebraicGeometry

end
