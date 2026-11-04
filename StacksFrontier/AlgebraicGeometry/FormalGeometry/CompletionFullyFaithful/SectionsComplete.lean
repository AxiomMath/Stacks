module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientComparison.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.LimitSectionsIdentification.Sections
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksCore.Tactic.StacksAttribute

/-!
# Full faithfulness of the completion gives infinitesimal section completeness

Let `X` be a locally Noetherian scheme, `i : Z ⟶ X` a closed immersion with ideal sheaf
`I = i.ker`, and `Y_n` the infinitesimal neighbourhoods of `i`. If the completion functor
`Coh(𝒪_X) ⥤ Coh(X, I)` of Stacks 0880 is bijective on the morphisms between finite locally free
coherent modules, then for every such module `G` the global sections of `G` are exactly the
compatible systems of sections of `G` over the `Y_n`.

The argument applies the hypothesis at `F = 𝒪_X`, which is coherent and finite locally free on a
locally Noetherian scheme, and identifies both sides of the resulting bijection. On the left,
`Hom(𝒪_X, G)` is `Γ(X, G)`. On the right, a morphism `𝒪_X^∧ ⟶ G^∧` of completions is a morphism
`𝒪_X ⟶ lim_n G / Iⁿ G` into the inverse limit, by the adjunction
`Stacks.Algebraization.completionHomLimitEquiv`, hence a compatible system of global sections of
the terms `G / I ^ (n+1) G`; and the Stacks 0EL1 comparison
`G / I ^ (n+1) G ≅ (ι_n)_* (ι_n)^* G` identifies those with the sections of `G` over `Y_n`,
compatibly with the transition maps.

## Main definitions

* `Stacks.Algebraization.idealQuotientPushforwardMap` and
  `Stacks.Algebraization.idealQuotientPushforwardIso` — **Stacks 0EL1** for an arbitrary closed
  immersion `v` with ideal sheaf `I ^ n`: the comparison `F / I ^ n F ⟶ v_* v^* F` normalized by
  the adjunction unit, and the fact that it is an isomorphism.
* `Stacks.Algebraization.infinitesimalSectionsEquiv` — the resulting bijection
  `Γ(X, G / I ^ (n+1) G) ≃ Γ(Y_n, ι_n^* G)`.
* `Stacks.Algebraization.pushforwardSectionComparison` — the comparison of the direct images of
  the restrictions of a module along a factorization `a ≫ b = c`, whose global sections are
  `AlgebraicGeometry.pullbackSectionsMap`.
* `Stacks.Algebraization.homOfGlobalSection` and `Stacks.Algebraization.globalSectionOfHom` —
  global sections of a module are the morphisms out of the structure sheaf.
* `Stacks.Algebraization.completionTermSectionsEquiv` — global sections of the `n`-th term of the
  completion of `G`, read as sections of `G` over the `n`-th infinitesimal neighbourhood.

## Main results

* `Stacks.Algebraization.ker_nthInfinitesimalNeighbourhoodι` — the ideal sheaf cutting out the
  `n`-th infinitesimal neighbourhood of a closed immersion is `i.ker ^ (n + 1)`.
* `Stacks.Algebraization.infinitesimalSectionsEquiv_quotient_apply` and
  `Stacks.Algebraization.infinitesimalSectionsEquiv_transition` — the bijection is compatible with
  the quotient projection and with the transition maps.
* `Stacks.Algebraization.isInfinitesimalSectionsComplete_of_completionFullyFaithful` — **the
  implication (4) implies (3) of Stacks 0EKP**: full faithfulness of the completion functor on
  finite locally free coherent modules implies that every such module is infinitesimal section
  complete.

## Implementation notes

The `n`-th infinitesimal neighbourhood is built on the canonical open through which an immersion
factors as a closed immersion, while the completion functor and the Stacks 0EL1 comparison are
stated for the subscheme cut out by a power of an ideal sheaf. The two are matched by computing
the kernel of `Stacks.Algebraization.nthInfinitesimalNeighbourhoodι`: for a closed immersion the
canonical open is everything, so `Stacks.IdealSheaf.comap_pow` and the mutually inverse direct and
inverse images of ideal sheaves along an isomorphism give `i.ker ^ (n + 1)`. Since both the
comparison and its invertibility depend on the closed immersion only through its ideal sheaf, they
are proved here for an arbitrary closed immersion with that kernel rather than only for the
subscheme presentation.

Invertibility of the comparison is the essential-image half of Stacks 08M3 in the scheme-level
form `Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero`: the quotient `F / I ^ n F` is
annihilated by `I ^ n`, hence by the kernel of the comorphism of any closed immersion cutting out
`I ^ n`, so the unit is invertible there; composing with the invertibility of `v^*` on the
quotient projection gives the comparison.

`Γ((Scheme.Modules.pushforward v).obj M, U)` and `Γ(M, v ⁻¹ᵁ U)` are definitionally but not
syntactically equal, and `rw` cannot cross the projection separating `Γ(F, U)` from a presheaf's
sections, so the statements about sections are chained in term mode with `Eq.trans` and `congrArg`
and the auxiliary bijections are composed as explicit functions.

## References

* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]

/-- Along an isomorphism, inverse image of ideal sheaves is inverted by inverse image along the
inverse isomorphism. -/
public theorem comap_comap_inv (I : Y.IdealSheafData) : (I.comap f).comap (inv f) = I := by
  rw [← comap_comp, IsIso.inv_hom_id, comap_id]

/-- Along an isomorphism, inverse image of ideal sheaves is inverted by inverse image along the
inverse isomorphism, in the other order. -/
public theorem comap_inv_comap (K : X.IdealSheafData) : (K.comap (inv f)).comap f = K := by
  rw [← comap_comp, IsIso.hom_inv_id, comap_id]

/-- Inverse image of ideal sheaves along an isomorphism is injective. -/
public theorem comap_injective : Function.Injective (fun I : Y.IdealSheafData => I.comap f) :=
  fun I J h => by
    rw [← comap_comap_inv f I, ← comap_comap_inv f J]
    exact congrArg (fun K : X.IdealSheafData => K.comap (inv f)) h

/-- Along an isomorphism, the direct image of the inverse image of an ideal sheaf is the ideal
sheaf itself. -/
public theorem map_comap_of_isIso (I : Y.IdealSheafData) : (I.comap f).map f = I :=
  comap_injective f
    (le_antisymm (comap_map_le (I.comap f) f) (comap_mono f (le_map_comap I f)))

/-- Along an isomorphism, the inverse image of the direct image of an ideal sheaf is the ideal
sheaf itself. -/
public theorem comap_map_of_isIso (K : X.IdealSheafData) : (K.map f).comap f = K :=
  have hK : (K.comap (inv f)).comap f = K := comap_inv_comap f K
  have h1 : K.map f = K.comap (inv f) :=
    (congrArg (fun L : X.IdealSheafData => L.map f) hK).symm.trans
      (map_comap_of_isIso f (K.comap (inv f)))
  (congrArg (fun L : Y.IdealSheafData => L.comap f) h1).trans hK

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Algebraization

/-! ### The infinitesimal neighbourhoods of a closed immersion -/

section Neighbourhood

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- For a closed immersion the ideal sheaf of the closed factorization is the inverse image of
the kernel along the canonical open immersion. -/
public theorem ker_liftCoborder_eq_comap :
    i.liftCoborder.ker = i.ker.comap i.coborderRange.ι := by
  have hv : IsIso i.coborderRange.ι := Stacks.Divisors.isIso_coborderRange_ι i
  have he : i.liftCoborder.ker.map i.coborderRange.ι = i.ker := by
    rw [← Scheme.Hom.ker_comp, Scheme.Hom.liftCoborder_ι]
  rw [← he, Scheme.IdealSheafData.comap_map_of_isIso]

/-- **The `n`-th infinitesimal neighbourhood of a closed immersion is cut out by the `(n+1)`-st
power of its ideal sheaf.** -/
public theorem ker_nthInfinitesimalNeighbourhoodι (n : ℕ) :
    (nthInfinitesimalNeighbourhoodι i n).ker = i.ker ^ (n + 1) := by
  have hv : IsIso i.coborderRange.ι := Stacks.Divisors.isIso_coborderRange_ι i
  change ((i.liftCoborder.ker ^ (n + 1)).subschemeι ≫ i.coborderRange.ι).ker = _
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    ker_liftCoborder_eq_comap i, ← Stacks.IdealSheaf.comap_pow,
    Scheme.IdealSheafData.map_comap_of_isIso]

/-- The structure morphism of an infinitesimal neighbourhood of a closed immersion is a closed
immersion. -/
public instance isClosedImmersion_nthInfinitesimalNeighbourhoodι (n : ℕ) :
    IsClosedImmersion (nthInfinitesimalNeighbourhoodι i n) := by
  have hv : IsIso i.coborderRange.ι := Stacks.Divisors.isIso_coborderRange_ι i
  change IsClosedImmersion ((i.liftCoborder.ker ^ (n + 1)).subschemeι ≫ i.coborderRange.ι)
  infer_instance

end Neighbourhood

/-! ### The ideal-power quotient along an arbitrary closed immersion cutting out the ideal -/

section Comparison

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)

/-- The `n`-th power of `I` annihilates the sections, over any affine open, of a pushforward
along a closed immersion whose ideal sheaf is `I ^ n`. -/
public theorem idealPower_smul_pushforward_eq_bot_of_ker {V : Scheme.{u}} (v : V ⟶ X)
    [IsClosedImmersion v] (hv : v.ker = I ^ n) (M : V.Modules) (U : X.affineOpens) :
    I.ideal U ^ n •
        (⊤ : Submodule Γ(X, U) Γ((Scheme.Modules.pushforward v).obj M, U)) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.mpr fun a ha t _ => ?_) bot_le
  have ha' : a ∈ v.ker.ideal U := by
    rwa [hv, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  exact (Submodule.mem_bot _).mpr (pushforward_smul_eq_zero v
    (RingHom.mem_ker.mp (Scheme.Hom.ideal_ker_le v U ha')) t)

variable (F : X.Modules) {V : Scheme.{u}} (v : V ⟶ X) [IsClosedImmersion v]
  (hv : v.ker = I ^ n)

include hv

/-- Every morphism from `F` to a pushforward along a closed immersion with ideal sheaf `I ^ n`
kills the subsheaf `I ^ n F`. -/
public theorem idealPowerMultiple_ι_comp_eq_zero_of_ker {M : V.Modules}
    (u : F ⟶ (Scheme.Modules.pushforward v).obj M) :
    ((idealPowerMultiple I n F).ι :
        ((idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶ F) ≫ u =
      (0 : ((idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶ _) :=
  comp_eq_zero_of_idealPowerMultiple_eq_bot I n u
    ((idealPowerMultiple_eq_bot_iff_affine_smul_top I n _).2
      (idealPower_smul_pushforward_eq_bot_of_ker I n v hv M))

/-- **Stacks 0EL1, the comparison map.** For a closed immersion `v` with ideal sheaf `I ^ n`, the
canonical map `F / I ^ n F ⟶ v_* v^* F`, obtained by factoring the adjunction unit through the
quotient projection. -/
public def idealQuotientPushforwardMap :
    idealPowerQuotient I n F ⟶ (Scheme.Modules.pushforward v).obj
      ((Scheme.Modules.pullback v).obj F) :=
  cokernel.desc (C := X.Modules) (idealPowerMultiple I n F).ι
    ((Scheme.Modules.pullbackPushforwardAdjunction v).unit.app F)
    (idealPowerMultiple_ι_comp_eq_zero_of_ker I n F v hv _)

/-- The comparison is normalized by the adjunction unit. -/
@[simp]
public theorem idealQuotientPushforwardMap_π :
    cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι ≫
        idealQuotientPushforwardMap I n F v hv =
      (Scheme.Modules.pullbackPushforwardAdjunction v).unit.app F :=
  cokernel.π_desc _ _ _

/-- Restriction along `v` inverts the quotient projection `F ⟶ F / I ^ n F`. -/
public theorem isIso_pullback_map_cokernel_π_of_ker :
    IsIso ((Scheme.Modules.pullback v).map
      (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)) :=
  isIso_map_of_unit_fac (Scheme.Modules.pullbackPushforwardAdjunction v) _
    (idealQuotientPushforwardMap I n F v hv) (idealQuotientPushforwardMap_π I n F v hv)

/-- The adjunction unit is an isomorphism at `F / I ^ n F`, for any closed immersion with ideal
sheaf `I ^ n`: the quotient is annihilated by `I ^ n`, hence by the kernel of the comorphism
of `v`. -/
public theorem isIso_unit_app_idealPowerQuotient_of_ker [F.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction v).unit.app
      (idealPowerQuotient I n F)) :=
  Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero v (idealPowerQuotient I n F)
    ((Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal v
      (idealPowerQuotient I n F)).mpr fun U a ha m => by
        rw [hv, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply] at ha
        exact affine_sections_annihilated_of_idealPowerMultiple_eq_bot
          (idealPowerMultiple_idealPowerQuotient_eq_bot I n F) U ha m)

/-- **Stacks 0EL1, for an arbitrary presentation of the infinitesimal neighbourhood.** For a
closed immersion `v` with ideal sheaf `I ^ n`, the canonical comparison `F / I ^ n F ⟶ v_* v^* F`
is an isomorphism. -/
public theorem isIso_idealQuotientPushforwardMap [F.IsQuasicoherent] :
    IsIso (idealQuotientPushforwardMap I n F v hv) := by
  have hunit := isIso_unit_app_idealPowerQuotient_of_ker I n F v hv
  have hpull := isIso_pullback_map_cokernel_π_of_ker I n F v hv
  have hmap : IsIso ((Scheme.Modules.pullback v ⋙ Scheme.Modules.pushforward v).map
      (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)) := by
    dsimp only [CategoryTheory.Functor.comp_map]
    infer_instance
  have key : idealQuotientPushforwardMap I n F v hv ≫
      (Scheme.Modules.pullback v ⋙ Scheme.Modules.pushforward v).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι) =
      (Scheme.Modules.pullbackPushforwardAdjunction v).unit.app
        (idealPowerQuotient I n F) := by
    rw [← cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι),
      ← Category.assoc, idealQuotientPushforwardMap_π]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction v).unit.naturality
      (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)).symm
  have h2 : IsIso (idealQuotientPushforwardMap I n F v hv ≫
      (Scheme.Modules.pullback v ⋙ Scheme.Modules.pushforward v).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)) := by
    rwa [key]
  exact IsIso.of_isIso_comp_right (idealQuotientPushforwardMap I n F v hv)
    ((Scheme.Modules.pullback v ⋙ Scheme.Modules.pushforward v).map
      (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι))

/-- **Stacks 0EL1**, as an isomorphism, for an arbitrary closed immersion with ideal sheaf
`I ^ n`. -/
public def idealQuotientPushforwardIso [F.IsQuasicoherent] :
    idealPowerQuotient I n F ≅
      (Scheme.Modules.pushforward v).obj ((Scheme.Modules.pullback v).obj F) :=
  haveI := isIso_idealQuotientPushforwardMap I n F v hv
  asIso (idealQuotientPushforwardMap I n F v hv)

/-- The comparison isomorphism is normalized by the adjunction unit. -/
@[simp]
public theorem idealQuotientPushforwardIso_hom [F.IsQuasicoherent] :
    (idealQuotientPushforwardIso I n F v hv).hom = idealQuotientPushforwardMap I n F v hv :=
  rfl

end Comparison

/-! ### The adjunction units along a factorization -/

section Factorization

/-- An isomorphism of modules is a bijection on the sections over any open. -/
public def sectionsEquivOfIso {W : Scheme.{u}} {M N : W.Modules} (e : M ≅ N) (U : W.Opens) :
    Γ(M, U) ≃ Γ(N, U) where
  toFun x := e.hom.app U x
  invFun y := e.inv.app U y
  left_inv x := congrArg (fun χ => Scheme.Modules.Hom.app χ U x) e.hom_inv_id
  right_inv y := congrArg (fun χ => Scheme.Modules.Hom.app χ U y) e.inv_hom_id

/-- The adjunction unit is compatible with the identification of inverse and direct images along
equal morphisms of schemes. -/
public theorem unit_app_pullbackCongr {A B : Scheme.{u}} {p q : A ⟶ B} (hw : p = q)
    (M : B.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M ≫
        (Scheme.Modules.pushforward p).map ((Scheme.Modules.pullbackCongr hw).hom.app M) ≫
          (Scheme.Modules.pushforwardCongr hw).hom.app ((Scheme.Modules.pullback q).obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app M := by
  subst hw
  have h1 : (Scheme.Modules.pullbackCongr (rfl : p = p)).hom.app M = 𝟙 _ := rfl
  have h2 : (Scheme.Modules.pushforwardCongr (rfl : p = p)).hom.app
      ((Scheme.Modules.pullback p).obj M) = 𝟙 _ :=
    Scheme.Modules.hom_ext _ _ fun U => by simp
  rw [h1, h2, CategoryTheory.Functor.map_id]
  simp

/-- **The adjunction unit along a composite of morphisms of schemes**, in terms of the units of
the two factors. -/
public theorem unit_app_comp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (M : C.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M ≫
        ((Scheme.Modules.pushforward b).map
            ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
              ((Scheme.Modules.pullback b).obj M)) ≫
          (Scheme.Modules.pushforwardComp a b).hom.app
            ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M))) =
      (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M ≫
        (Scheme.Modules.pushforward (a ≫ b)).map
          ((Scheme.Modules.pullbackComp a b).inv.app M) := by
  have key := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
      (Scheme.Modules.pullbackPushforwardAdjunction a))
    (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b))
    (Scheme.Modules.pullbackComp a b).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at key
  exact (Category.assoc _ _ _).symm.trans key

/-- The comparison of the direct images of the restrictions of a module along a factorization
`a ≫ b = c` of morphisms of schemes: the adjunction unit for `a`, pushed forward along `b`, read
through the identifications of iterated direct and inverse images. -/
public def pushforwardSectionComparison {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    {c : A ⟶ C} (hw : a ≫ b = c) (M : C.Modules) :
    (Scheme.Modules.pushforward b).obj ((Scheme.Modules.pullback b).obj M) ⟶
      (Scheme.Modules.pushforward c).obj ((Scheme.Modules.pullback c).obj M) :=
  (Scheme.Modules.pushforward b).map
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
          ((Scheme.Modules.pullback b).obj M) ≫
        (Scheme.Modules.pushforward a).map
          ((Scheme.Modules.pullbackComp a b).hom.app M ≫
            (Scheme.Modules.pullbackCongr hw).hom.app M)) ≫
    (Scheme.Modules.pushforwardComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
      (Scheme.Modules.pushforwardCongr hw).hom.app ((Scheme.Modules.pullback c).obj M)

/-- **The adjunction units along a factorization form a cone.** For `a ≫ b = c`, the unit for `b`
followed by the comparison of direct images is the unit for `c`. -/
public theorem unit_comp_pushforwardSectionComparison {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    {c : A ⟶ C} (hw : a ≫ b = c) (M : C.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M ≫
        pushforwardSectionComparison a b hw M =
      (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M := by
  have hnat := (Scheme.Modules.pushforwardComp a b).hom.naturality
    ((Scheme.Modules.pullbackComp a b).hom.app M ≫
      (Scheme.Modules.pullbackCongr hw).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hnat
  rw [pushforwardSectionComparison, CategoryTheory.Functor.map_comp]
  slice_lhs 3 4 => rw [hnat]
  slice_lhs 1 3 => rw [unit_app_comp a b M]
  slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp]
  slice_lhs 2 2 => rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  exact unit_app_pullbackCongr hw M

/-- **The canonical map on global sections is the direct-image comparison, read at the top
open.** -/
public theorem pullbackSectionsMap_eq_pushforwardSectionComparison {S : Scheme.{u}}
    {A B : Over S} (g : A ⟶ B) (M : S.Modules)
    (z : Γ((Scheme.Modules.pullback B.hom).obj M, (⊤ : B.left.Opens))) :
    pullbackSectionsMap M g z =
      (pushforwardSectionComparison g.left B.hom (Over.w g) M).app ⊤ z :=
  rfl

end Factorization

/-! ### Sections over the infinitesimal neighbourhoods -/

section Sections

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (G : X.Modules) [G.IsQuasicoherent]

/-- **Stacks 0EL1** at the `n`-th infinitesimal neighbourhood of a closed immersion: the quotient
of `G` by the `(n+1)`-st power of the ideal sheaf is the pushforward of the restriction of `G` to
that neighbourhood. -/
public def infinitesimalQuotientIso (n : ℕ) :
    idealPowerQuotient i.ker (n + 1) G ≅
      (Scheme.Modules.pushforward (nthInfinitesimalNeighbourhoodι i n)).obj
        ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj G) :=
  idealQuotientPushforwardIso i.ker (n + 1) G (nthInfinitesimalNeighbourhoodι i n)
    (ker_nthInfinitesimalNeighbourhoodι i n)

/-- The quotient projection `G ⟶ G / I ^ (n+1) G`. -/
public abbrev infinitesimalQuotientπ (n : ℕ) : G ⟶ idealPowerQuotient i.ker (n + 1) G :=
  cokernel.π (C := X.Modules) (idealPowerMultiple i.ker (n + 1) G).ι

/-- **Global sections of the ideal-power quotient are the sections over the infinitesimal
neighbourhood.** -/
public def infinitesimalSectionsEquiv (n : ℕ) :
    Γ(idealPowerQuotient i.ker (n + 1) G, (⊤ : X.Opens)) ≃
      Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj G,
        (⊤ : (nthInfinitesimalNeighbourhood i n).Opens)) :=
  sectionsEquivOfIso (infinitesimalQuotientIso i G n) ⊤

/-- The bijection is evaluation of the Stacks 0EL1 comparison on global sections. -/
@[simp]
public theorem infinitesimalSectionsEquiv_apply (n : ℕ)
    (x : Γ(idealPowerQuotient i.ker (n + 1) G, (⊤ : X.Opens))) :
    infinitesimalSectionsEquiv i G n x =
      (idealQuotientPushforwardMap i.ker (n + 1) G (nthInfinitesimalNeighbourhoodι i n)
        (ker_nthInfinitesimalNeighbourhoodι i n)).app ⊤ x :=
  rfl

/-- **The comparison is compatible with the canonical map on global sections.** The image of a
global section of `G` in the ideal-power quotient corresponds to its restriction to the `n`-th
infinitesimal neighbourhood. -/
public theorem infinitesimalSectionsEquiv_quotient_apply (n : ℕ) (t : Γ(G, (⊤ : X.Opens))) :
    infinitesimalSectionsEquiv i G n ((infinitesimalQuotientπ i G n).app ⊤ t) =
      pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) G t := by
  rw [infinitesimalSectionsEquiv_apply, pullbackGlobalSections_eq_unit]
  exact congrArg (fun χ => Scheme.Modules.Hom.app χ (⊤ : X.Opens) t)
    (idealQuotientPushforwardMap_π i.ker (n + 1) G (nthInfinitesimalNeighbourhoodι i n)
      (ker_nthInfinitesimalNeighbourhoodι i n))

/-- **The comparison with the sections over the infinitesimal neighbourhoods is compatible with
the transition maps.** Any morphism of ideal-power quotients commuting with the quotient
projections is carried to the canonical map on the sections over the neighbourhoods. -/
public theorem infinitesimalSectionsEquiv_transition {n m : ℕ} (h : n ≤ m)
    (τ : idealPowerQuotient i.ker (m + 1) G ⟶ idealPowerQuotient i.ker (n + 1) G)
    (hτ : infinitesimalQuotientπ i G m ≫ τ = infinitesimalQuotientπ i G n)
    (y : Γ(idealPowerQuotient i.ker (m + 1) G, (⊤ : X.Opens))) :
    pullbackSectionsMap G (nthInfinitesimalNeighbourhoodTransition i h)
        (infinitesimalSectionsEquiv i G m y) =
      infinitesimalSectionsEquiv i G n (τ.app ⊤ y) := by
  have hsq : idealQuotientPushforwardMap i.ker (m + 1) G
        (nthInfinitesimalNeighbourhoodι i m) (ker_nthInfinitesimalNeighbourhoodι i m) ≫
      pushforwardSectionComparison (nthInfinitesimalNeighbourhoodTransition i h).left
        (nthInfinitesimalNeighbourhoodι i m)
        (Over.w (nthInfinitesimalNeighbourhoodTransition i h)) G =
      τ ≫ idealQuotientPushforwardMap i.ker (n + 1) G
        (nthInfinitesimalNeighbourhoodι i n) (ker_nthInfinitesimalNeighbourhoodι i n) := by
    refine (cancel_epi (infinitesimalQuotientπ i G m)).1 ?_
    rw [← Category.assoc, idealQuotientPushforwardMap_π, ← Category.assoc, hτ,
      idealQuotientPushforwardMap_π]
    exact unit_comp_pushforwardSectionComparison _ _ _ G
  rw [infinitesimalSectionsEquiv_apply, infinitesimalSectionsEquiv_apply]
  exact (pullbackSectionsMap_eq_pushforwardSectionComparison
    (nthInfinitesimalNeighbourhoodTransition i h) G _).trans
    (congrArg (fun χ => Scheme.Modules.Hom.app χ (⊤ : X.Opens) y) hsq)

end Sections

/-! ### Global sections as morphisms out of the structure sheaf -/

section GlobalSections

variable {X : Scheme.{u}} (M : X.Modules)

/-- A global section of a module, read as a morphism from the structure sheaf. -/
public def homOfGlobalSection (x : Γ(M, (⊤ : X.Opens))) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf M x)

/-- A morphism from the structure sheaf, read as a global section. -/
public def globalSectionOfHom (u : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    Γ(M, (⊤ : X.Opens)) :=
  (SheafOfModules.unitHomEquiv M u).eval (op ⊤)

/-- Reading a global section as a morphism and back gives the section. -/
@[simp]
public theorem globalSectionOfHom_homOfGlobalSection (x : Γ(M, (⊤ : X.Opens))) :
    globalSectionOfHom M (homOfGlobalSection M x) = x := by
  rw [globalSectionOfHom, homOfGlobalSection, Equiv.apply_symm_apply]
  exact Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top M x

/-- Reading a morphism out of the structure sheaf as a global section and back gives the
morphism. -/
@[simp]
public theorem homOfGlobalSection_globalSectionOfHom
    (u : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    homOfGlobalSection M (globalSectionOfHom M u) = u := by
  refine (SheafOfModules.unitHomEquiv M).injective ?_
  rw [homOfGlobalSection, Equiv.apply_symm_apply]
  refine Stacks.SheafOfModules.sections_ext_of_eval_top M ?_
  exact Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top M _

/-- The global section attached to a composite is the image of the global section. -/
public theorem globalSectionOfHom_comp {N : X.Modules}
    (u : SheafOfModules.unit X.ringCatSheaf ⟶ M) (φ : M ⟶ N) :
    globalSectionOfHom N (u ≫ φ) =
      Scheme.Modules.Hom.app φ ⊤ (globalSectionOfHom M u) :=
  congrArg (fun s => PresheafOfModules.sections.eval s (op ⊤))
    (SheafOfModules.unitHomEquiv_comp_apply u φ)

/-- A morphism out of the structure sheaf is determined by its global section. -/
public theorem hom_ext_of_globalSectionOfHom
    {u v : SheafOfModules.unit X.ringCatSheaf ⟶ M}
    (h : globalSectionOfHom M u = globalSectionOfHom M v) : u = v := by
  rw [← homOfGlobalSection_globalSectionOfHom M u,
    ← homOfGlobalSection_globalSectionOfHom M v, h]

/-- A composite out of the structure sheaf is the morphism of a global section `y` exactly when
the image of its global section is `y`. -/
private theorem comp_eq_homOfGlobalSection_iff {N : X.Modules}
    (u : SheafOfModules.unit X.ringCatSheaf ⟶ M) (φ : M ⟶ N) (y : Γ(N, (⊤ : X.Opens))) :
    u ≫ φ = homOfGlobalSection N y ↔ Scheme.Modules.Hom.app φ ⊤ (globalSectionOfHom M u) = y := by
  rw [← globalSectionOfHom_comp]
  exact ⟨fun h => by rw [h, globalSectionOfHom_homOfGlobalSection], fun h =>
    hom_ext_of_globalSectionOfHom N (by rw [globalSectionOfHom_homOfGlobalSection, h])⟩

end GlobalSections

/-! ### The terms of the completion -/

/-- The structure sheaf of a locally Noetherian scheme, as a coherent module. -/
@[ega "I 10.11.1" "special case"]
public abbrev unitCoherentModule (X : Scheme.{u}) [IsLocallyNoetherian X] :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ⟨SheafOfModules.unit X.ringCatSheaf,
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X⟩

/-- The structure sheaf of a locally Noetherian scheme is finite locally free. -/
public theorem isFiniteLocallyFree_unitCoherentModule (X : Scheme.{u}) [IsLocallyNoetherian X] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (unitCoherentModule X).obj :=
  have := AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit X
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (SheafOfModules.unit X.ringCatSheaf) 1

section Terms

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
  (Gc : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  [Gc.obj.IsQuasicoherent]

omit [IsClosedImmersion i] [Gc.obj.IsQuasicoherent] in
/-- The projection onto the `n`-th term of the completion, followed by the identification of that
term with the ideal-power quotient, is the quotient projection. -/
public theorem completionProjection_comp_eqToHom (n : ℕ) :
    completionProjection X i.ker Gc n ≫ eqToHom (completionFunctor_obj X i.ker Gc n) =
      infinitesimalQuotientπ i Gc.obj n := by
  have h1 : eqToHom (completionFunctor_obj X i.ker Gc n).symm ≫
      eqToHom (completionFunctor_obj X i.ker Gc n) =
      𝟙 (idealPowerQuotient i.ker (n + 1) Gc.obj) := by
    rw [eqToHom_trans, eqToHom_refl]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => cokernel.π (C := X.Modules)
        (idealPowerMultiple i.ker (n + 1) Gc.obj).ι ≫ k) h1).trans (Category.comp_id _))

/-- The global sections of the `n`-th term of the completion of `G` are the sections of `G` over
the `n`-th infinitesimal neighbourhood of `i`. -/
public def completionTermSectionsEquiv (n : ℕ) :
    Γ(((completionFunctor X i.ker).obj Gc).obj.obj (op n), (⊤ : X.Opens)) ≃
      Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj Gc.obj,
        (⊤ : (nthInfinitesimalNeighbourhood i n).Opens)) :=
  (sectionsEquivOfIso (eqToIso (completionFunctor_obj X i.ker Gc n)) ⊤).trans
    (infinitesimalSectionsEquiv i Gc.obj n)

/-- The comparison is evaluation of the Stacks 0EL1 comparison, after identifying the term of the
completion with the ideal-power quotient. -/
@[simp]
public theorem completionTermSectionsEquiv_apply (n : ℕ)
    (y : Γ(((completionFunctor X i.ker).obj Gc).obj.obj (op n), (⊤ : X.Opens))) :
    completionTermSectionsEquiv i Gc n y =
      infinitesimalSectionsEquiv i Gc.obj n
        (Scheme.Modules.Hom.app (eqToHom (completionFunctor_obj X i.ker Gc n)) ⊤ y) :=
  rfl

/-- The comparison carries the image of a global section under the projection onto a term of the
completion to its restriction to the corresponding infinitesimal neighbourhood. -/
public theorem completionTermSectionsEquiv_projection (n : ℕ)
    (t : Γ(Gc.obj, (⊤ : X.Opens))) :
    completionTermSectionsEquiv i Gc n
        (Scheme.Modules.Hom.app (completionProjection X i.ker Gc n) ⊤ t) =
      pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) Gc.obj t := by
  refine Eq.trans ?_ (infinitesimalSectionsEquiv_quotient_apply i Gc.obj n t)
  refine congrArg (infinitesimalSectionsEquiv i Gc.obj n) ?_
  exact congrArg (fun χ => Scheme.Modules.Hom.app χ (⊤ : X.Opens) t)
    (completionProjection_comp_eqToHom i Gc n)

/-- The comparison is compatible with the transition maps of the completion. -/
public theorem completionTermSectionsEquiv_transition {n m : ℕ} (h : n ≤ m)
    (y : Γ(((completionFunctor X i.ker).obj Gc).obj.obj (op m), (⊤ : X.Opens))) :
    pullbackSectionsMap Gc.obj (nthInfinitesimalNeighbourhoodTransition i h)
        (completionTermSectionsEquiv i Gc m y) =
      completionTermSectionsEquiv i Gc n
        (Scheme.Modules.Hom.app
          (((completionFunctor X i.ker).obj Gc).obj.map (homOfLE h).op) ⊤ y) := by
  have hcomp : eqToHom (completionFunctor_obj X i.ker Gc m) ≫
      (eqToIso (completionFunctor_obj X i.ker Gc m)).inv ≫
        (((completionFunctor X i.ker).obj Gc).obj.map (homOfLE h).op ≫
          eqToHom (completionFunctor_obj X i.ker Gc n)) =
      ((completionFunctor X i.ker).obj Gc).obj.map (homOfLE h).op ≫
        eqToHom (completionFunctor_obj X i.ker Gc n) :=
    Iso.hom_inv_id_assoc (eqToIso (completionFunctor_obj X i.ker Gc m)) _
  have hτ : infinitesimalQuotientπ i Gc.obj m ≫
      ((eqToIso (completionFunctor_obj X i.ker Gc m)).inv ≫
        (((completionFunctor X i.ker).obj Gc).obj.map (homOfLE h).op ≫
          eqToHom (completionFunctor_obj X i.ker Gc n))) =
      infinitesimalQuotientπ i Gc.obj n :=
    (congrArg (fun k => k ≫ ((eqToIso (completionFunctor_obj X i.ker Gc m)).inv ≫
        (((completionFunctor X i.ker).obj Gc).obj.map (homOfLE h).op ≫
          eqToHom (completionFunctor_obj X i.ker Gc n))))
      (completionProjection_comp_eqToHom i Gc m)).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => completionProjection X i.ker Gc m ≫ k) hcomp).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ eqToHom (completionFunctor_obj X i.ker Gc n))
                (completionProjection_naturality_le X i.ker Gc h)).trans
              (completionProjection_comp_eqToHom i Gc n)))))
  have key := infinitesimalSectionsEquiv_transition i Gc.obj h _ hτ
    (Scheme.Modules.Hom.app (eqToHom (completionFunctor_obj X i.ker Gc m)) ⊤ y)
  rw [completionTermSectionsEquiv_apply, completionTermSectionsEquiv_apply]
  refine key.trans (congrArg (infinitesimalSectionsEquiv i Gc.obj n) ?_)
  exact congrArg (fun χ => Scheme.Modules.Hom.app χ (⊤ : X.Opens) y) hcomp

/-- The morphisms out of the structure sheaf attached to two sections over the infinitesimal
neighbourhoods related by the transition map commute with the transition map of the
completion. -/
public theorem homOfGlobalSection_completionTermSectionsEquiv_symm_comp_map {n m : ℕ}
    (h : n ≤ m)
    {t : Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i m)).obj Gc.obj, ⊤)}
    {t' : Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj Gc.obj, ⊤)}
    (ht : pullbackSectionsMap Gc.obj (nthInfinitesimalNeighbourhoodTransition i h) t = t') :
    homOfGlobalSection _ ((completionTermSectionsEquiv i Gc m).symm t) ≫
        ((completionFunctor X i.ker).obj Gc).obj.map (homOfLE h).op =
      homOfGlobalSection _ ((completionTermSectionsEquiv i Gc n).symm t') := by
  rw [comp_eq_homOfGlobalSection_iff, globalSectionOfHom_homOfGlobalSection,
    ← (completionTermSectionsEquiv i Gc n).apply_eq_iff_eq,
    ← completionTermSectionsEquiv_transition, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ht]

/-- A morphism out of the structure sheaf followed by the projection onto the `n`-th term of the
completion is the morphism of a global section `y` of that term exactly when its global section
restricts to the section of the `n`-th infinitesimal neighbourhood corresponding to `y`. -/
public theorem comp_completionProjection_eq_homOfGlobalSection_iff (n : ℕ)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ Gc.obj)
    (y : Γ(((completionFunctor X i.ker).obj Gc).obj.obj (op n), (⊤ : X.Opens))) :
    φ ≫ completionProjection X i.ker Gc n = homOfGlobalSection _ y ↔
      pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) Gc.obj
        (globalSectionOfHom Gc.obj φ) = completionTermSectionsEquiv i Gc n y := by
  refine (comp_eq_homOfGlobalSection_iff _ _ _ _).trans ?_
  rw [← (completionTermSectionsEquiv i Gc n).apply_eq_iff_eq,
    completionTermSectionsEquiv_projection]

omit [IsClosedImmersion i] [Gc.obj.IsQuasicoherent] in
/-- A morphism into the limit of the completion is the composite of `φ` with the canonical map
exactly when the two agree after every projection. -/
public theorem comp_completionToLimit_eq_iff {P : X.Modules} (φ : P ⟶ Gc.obj)
    (g : P ⟶ limit (C := X.Modules) ((completionFunctor X i.ker).obj Gc).obj) :
    φ ≫ completionToLimit X i.ker Gc = g ↔
      ∀ n : ℕ, φ ≫ completionProjection X i.ker Gc n =
        g ≫ limit.π (C := X.Modules) ((completionFunctor X i.ker).obj Gc).obj (op n) := by
  refine ⟨fun hφ n => ?_, fun hφ => ?_⟩
  · exact ((congrArg (fun k => φ ≫ k)
        (completionToLimit_projection X i.ker Gc (op n))).symm.trans
      (Category.assoc _ _ _).symm).trans
        (congrArg (fun k => k ≫ limit.π (C := X.Modules)
          ((completionFunctor X i.ker).obj Gc).obj (op n)) hφ)
  · refine limit.hom_ext (C := X.Modules)
      (F := ((completionFunctor X i.ker).obj Gc).obj) fun n => ?_
    exact (Category.assoc _ _ _).trans ((congrArg (fun k => φ ≫ k)
      (completionToLimit_projection X i.ker Gc n)).trans (hφ n.unop))

omit [IsClosedImmersion i] [Gc.obj.IsQuasicoherent] in
/-- The completion of `w : G ⟶ Gc` is the completion map determined by a morphism `f` into the
limit of the completion of `Gc` exactly when `w` and `f` agree after every projection. -/
public theorem completionFunctor_map_eq_completionHomLimitEquiv_iff
    {G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (w : G ⟶ Gc)
    (f : coherentObj G ⟶ limit (C := X.Modules) ((completionFunctor X i.ker).obj Gc).obj) :
    (completionFunctor X i.ker).map w =
        completionHomLimitEquiv (I := i.ker) G ((completionFunctor X i.ker).obj Gc) f ↔
      ∀ n : ℕ, w.hom ≫ completionProjection X i.ker Gc n =
        f ≫ limit.π (C := X.Modules) ((completionFunctor X i.ker).obj Gc).obj (op n) :=
  (Eq.congr_left (completionHomLimitEquiv_comp_completionToLimit i.ker G Gc w)).symm.trans
    ((completionHomLimitEquiv (I := i.ker) G
      ((completionFunctor X i.ker).obj Gc)).injective.eq_iff.trans
        (comp_completionToLimit_eq_iff i Gc w.hom f))

end Terms

/-! ### Section completeness from full faithfulness -/

/-- **Full faithfulness of the completion gives infinitesimal section completeness.** Let
`i : Z ⟶ X` be a closed immersion into a locally Noetherian scheme, with ideal sheaf `I = i.ker`.
If the completion functor `Coh(𝒪_X) ⥤ Coh(X, I)` is bijective on morphisms between finite locally
free coherent modules, then for every finite locally free coherent module `G` every compatible
system of sections of `G` over the infinitesimal neighbourhoods of `i` comes from a unique global
section of `G`.

This is the implication (4) implies (3) of Stacks 0EKP: the hypothesis is applied at the
structure sheaf, which is coherent and finite locally free, and both sides of the resulting
bijection are identified — morphisms out of the structure sheaf with global sections, and
morphisms of completions with compatible systems of sections over the neighbourhoods. -/
public theorem isInfinitesimalSectionsComplete_of_completionFullyFaithful
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (hFF : Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree X i.ker)
    (Gc : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Gc.obj) :
    Stacks.Algebraization.IsInfinitesimalSectionsComplete i Gc.obj := by
  have : Gc.obj.IsCoherent := Gc.property
  have : Gc.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent Gc.obj).1
  have hOflf := isFiniteLocallyFree_unitCoherentModule X
  intro s hs
  set x : ∀ n : ℕ, Γ(((completionFunctor X i.ker).obj Gc).obj.obj (op n), (⊤ : X.Opens)) :=
    fun n => (completionTermSectionsEquiv i Gc n).symm (s n)
  let cone : Cone (C := X.Modules) ((completionFunctor X i.ker).obj Gc).obj :=
    { pt := coherentObj (unitCoherentModule X)
      π :=
        { app := fun n => homOfGlobalSection _ (x n.unop)
          naturality := fun m n a => by
            have hle : n.unop ≤ m.unop := leOfHom a.unop
            exact (Category.id_comp _).trans
              ((homOfGlobalSection_completionTermSectionsEquiv_symm_comp_map i Gc hle
                (hs n.unop m.unop hle)).symm.trans
                (congrArg (fun k => homOfGlobalSection _ (x m.unop) ≫
                  ((completionFunctor X i.ker).obj Gc).obj.map k)
                  (Subsingleton.elim _ _ : (homOfLE hle).op = a))) } }
  set f₀ : coherentObj (unitCoherentModule X) ⟶
      limit (C := X.Modules) ((completionFunctor X i.ker).obj Gc).obj :=
    limit.lift (C := X.Modules) _ cone
  have hmain : ∀ w : unitCoherentModule X ⟶ Gc,
      ((completionFunctor X i.ker).map w = completionHomLimitEquiv (I := i.ker)
          (unitCoherentModule X) ((completionFunctor X i.ker).obj Gc) f₀ ↔
        ∀ n : ℕ, pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) Gc.obj
          (globalSectionOfHom Gc.obj w.hom) = s n) := fun w =>
    ((completionFunctor_map_eq_completionHomLimitEquiv_iff i Gc w f₀).trans
      (forall_congr' fun n => Eq.congr_right (limit.lift_π cone (op n) :
        f₀ ≫ _ = homOfGlobalSection _ (x n)))).trans
        (forall_congr' fun n => (comp_completionProjection_eq_homOfGlobalSection_iff i Gc n
          w.hom (x n)).trans (Eq.congr_right (Equiv.apply_symm_apply _ (s n))))
  obtain ⟨w, hw⟩ := (hFF (unitCoherentModule X) Gc hOflf hG).2
    (completionHomLimitEquiv (I := i.ker) (unitCoherentModule X)
      ((completionFunctor X i.ker).obj Gc) f₀)
  refine ⟨globalSectionOfHom Gc.obj w.hom, (hmain w).1 hw, fun t' ht' => ?_⟩
  have hw' := (hmain (ObjectProperty.homMk (homOfGlobalSection Gc.obj t'))).2 fun n =>
    (congrArg (pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) Gc.obj)
      (globalSectionOfHom_homOfGlobalSection Gc.obj t')).trans (ht' n)
  exact (globalSectionOfHom_homOfGlobalSection Gc.obj t').symm.trans
    (congrArg (fun v : unitCoherentModule X ⟶ Gc => globalSectionOfHom Gc.obj v.hom)
      ((hFF _ _ hOflf hG).1 (hw'.trans hw.symm)))

end Stacks.Algebraization

end
