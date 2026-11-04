module

public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.Infinitesimal

/-!
# Infinitesimal neighbourhoods of an immersion of algebraic spaces

Let `Z` be a closed subspace of an open subspace `U` of an algebraic space `X`, so that `Z` is
immersed in `X`, and let `𝓘 ⊆ 𝒪_U` be the ideal sheaf cutting out `Z`. The `n`th-order
infinitesimal neighbourhood of `Z` in `X` is the closed subspace of `U` cut out by `𝓘^(n+1)`,
and this file proves its universal property: it receives a unique morphism from every
`n`th-order thickening over `X` that is compatible with `Z`.

The neighbourhood is not constructed here. It is instead described by the condition that its
ideal sheaf on every étale chart of `U` be the `(n+1)`st power of that of `Z`, and the
universal property is proved for every closed subspace satisfying that condition. Since
`AlgebraicGeometry.Space.eq_of_ker_eq_ker_pow` shows at most one closed subspace satisfies it,
this is the characterisation of the neighbourhood rather than a statement about a choice, and
it shows in particular that the neighbourhood does not depend on the open subspace `U`.

## Main results

* `AlgebraicGeometry.Space.eq_of_ker_eq_ker_pow`: a closed subspace whose ideal sheaf is a
  given power of another's is unique.
* `AlgebraicGeometry.Space.range_le_of_isNthOrderThickening`: the algebraic-spaces form of
  Stacks 01HP. A morphism to `U` whose restriction to an `n`th-order thickening factors
  through `Z` has image in the closed subspace cut out by the `(n+1)`st power of `𝓘`.
* `AlgebraicGeometry.Space.existsUnique_lift_of_isNthOrderThickening` and
  `AlgebraicGeometry.Space.existsUnique_lift_of_isFirstOrderThickening`: the universal
  property of the `n`th-order and first-order infinitesimal neighbourhoods.

## Implementation notes

The ideal-sheaf condition is phrased with `AlgebraicGeometry.Scheme.Hom.ker` of the closed
immersion of schemes obtained by pulling the subspace back along an étale chart, rather than
with the chartwise global sections `AlgebraicGeometry.Space.definingIdealAt` used to measure
the order of a thickening. The two agree on affine charts, and the sheaf form is what the
factorisation criterion of Stacks 03MB consumes.

The universal property is proved for every `n`, the first-order case being `n = 1`; the source
states the first-order case first and the `n`th-order case for `n ≥ 1`, and the argument is
insensitive to the order. Its substantial ingredient is
`Stacks.Thickenings.ker_pow_le_ker_of_comm_square`, the scheme-theoretic form of Stacks 01HP,
which is applied on a chart after the thickening has been pulled back there: an étale atlas of
the source turns the thickening into one of schemes, and a further base change puts it over the
chart, where the ideal computation takes place. Membership in the neighbourhood is then
descended along the atlas, which is why the ambient presheaves are required to be sheaves.

## References

* [Stacks Project, Tag 05ZW](https://stacks.math.columbia.edu/tag/05ZW)
* [Stacks Project, Tag 05ZU](https://stacks.math.columbia.edu/tag/05ZU)
* [Stacks Project, Tag 01HP](https://stacks.math.columbia.edu/tag/01HP)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Uniqueness of the neighbourhood -/

/-- The pullback of a closed subspace along an étale chart is a closed immersion of schemes. -/
private theorem isClosedImmersion_map_snd {U : AlgebraicSpaces B S hS}
    (M : ClosedSubspaces B S hS U.1) (V : SmallEtale B S hS U.1) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (M.2.2.rep.snd V.1.hom)) :=
  M.2.2.property V.1.hom _ _ (M.2.2.rep.isPullback V.1.hom)

/-- A closed subspace of an algebraic space is determined by its ideal sheaf on the étale
charts, so at most one closed subspace is cut out by a given power of the ideal sheaf of
another. This is the sense in which the `n`th-order infinitesimal neighbourhood is unique. -/
theorem eq_of_ker_eq_ker_pow {n : ℕ} {U : AlgebraicSpaces B S hS}
    (Z N₁ N₂ : ClosedSubspaces B S hS U.1)
    (h₁ : ∀ V : SmallEtale B S hS U.1,
      ((BigFppfOver.toScheme B S hS).map (N₁.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ (n + 1))
    (h₂ : ∀ V : SmallEtale B S hS U.1,
      ((BigFppfOver.toScheme B S hS).map (N₂.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ (n + 1)) :
    N₁ = N₂ := by
  have key : ∀ V : SmallEtale B S hS U.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) →
      definingIdealAt B S hS U N₁ (op V) = definingIdealAt B S hS U N₂ (op V) := by
    intro V hV
    have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := hV
    have hbridge : ∀ M : ClosedSubspaces B S hS U.1,
        definingIdealAt B S hS U M (op V) =
          ((BigFppfOver.toScheme B S hS).map (M.2.2.rep.snd V.1.hom)).ker.ideal
            ⟨⊤, isAffineOpen_top _⟩ := by
      intro M
      have := isClosedImmersion_map_snd B S hS M V
      rw [definingIdealAt_eq_ker B S hS U M V, Scheme.Γ_map_op, Scheme.Hom.ker_apply]
      exact rfl
    rw [hbridge N₁, hbridge N₂, (h₁ V).trans (h₂ V).symm]
  exact Subtype.ext (le_antisymm
    (le_of_forall_definingIdealAt_le B S hS U N₁ N₂ fun V hV => (key V hV).symm.le)
    (le_of_forall_definingIdealAt_le B S hS U N₂ N₁ fun V hV => (key V hV).le))

/-! ### The ideal computation on a chart -/

/-- On an étale chart `V` of `U`, a morphism `k` from a scheme carrying an `n`th-order
thickening whose closed part maps into the closed subspace `Z` kills the `(n+1)`st power of
the ideal sheaf of `Z` on that chart. This is Stacks 01HP read on one chart. -/
theorem ker_pow_le_ker_of_isNthOrderThickening {n : ℕ} {U : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS U.1)
    (V : SmallEtale B S hS U.1) {a₀ A₀ : BigFppfOver B S hS} (k : a₀ ⟶ V.1.left)
    (jA : A₀ ⟶ a₀)
    (hjA : Stacks.Thickenings.IsNthOrderThickening n ((BigFppfOver.toScheme B S hS).map jA))
    (aZ : yoneda.obj A₀ ⟶ Z.1.toFunctor)
    (haZ : aZ ≫ Z.1.ι = yoneda.map (jA ≫ k) ≫ V.1.hom) :
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ (n + 1) ≤
      ((BigFppfOver.toScheme B S hS).map k).ker := by
  have := isClosedImmersion_map_snd B S hS Z V
  have hj : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map jA) := hjA.1
  set ℓ : yoneda.obj A₀ ⟶ yoneda.obj (Z.2.2.rep.pullback V.1.hom) :=
    (Z.2.2.rep.isPullback V.1.hom).lift aZ (yoneda.map (jA ≫ k)) haZ with hℓ
  have hsite : yoneda.preimage ℓ ≫ Z.2.2.rep.snd V.1.hom = jA ≫ k := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, yoneda.map_preimage, hℓ]
    exact (Z.2.2.rep.isPullback V.1.hom).lift_snd _ _ _
  refine Stacks.Thickenings.ker_pow_le_ker_of_comm_square
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom))
    ((BigFppfOver.toScheme B S hS).map jA)
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage ℓ))
    ((BigFppfOver.toScheme B S hS).map k) (n + 1) ?_ hjA.2
  rw [← Functor.map_comp, ← Functor.map_comp, hsite]

/-! ### Étale descent of membership -/

/-- Membership in a subfunctor of a sheaf descends along a surjective étale atlas: if every
point of an algebraic space coming from the atlas lies in the subfunctor, every point does. -/
theorem range_le_of_range_comp_le {Y : AlgebraicSpaces B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (N : Subfunctor F)
    (hNs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) N.toFunctor)
    {W : BigFppfOver B S hS} (f : yoneda.obj W ⟶ Y.1)
    (hfS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hfE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (h : Y.1 ⟶ F) (hle : Subfunctor.range (f ≫ h) ≤ N) :
    Subfunctor.range h ≤ N := by
  intro T x hx
  obtain ⟨x₀, rfl⟩ := hx
  obtain ⟨T⟩ := T
  set τ : yoneda.obj T ⟶ Y.1 := yonedaEquiv.symm x₀ with hτ
  refine mem_obj_of_surjective_etale B S hS hF N hNs (hfE.rep.snd τ)
    (hfS.property_snd τ) (hfE.property_snd τ) _ ?_
  have hw : yoneda.map (hfE.rep.fst' τ) ≫ f = yoneda.map (hfE.rep.snd τ) ≫ τ := by
    rw [hfE.rep.map_fst' τ]
    exact hfE.rep.w τ
  have hval : h.app (op T) x₀ = yonedaEquiv (τ ≫ h) := by
    rw [yonedaEquiv_comp, hτ, Equiv.apply_symm_apply]
  have key : F.map (hfE.rep.snd τ).op (h.app (op T) x₀) =
      (f ≫ h).app (op (hfE.rep.pullback τ)) (hfE.rep.fst' τ) := by
    rw [hval, yonedaEquiv_naturality (τ ≫ h) (hfE.rep.snd τ), ← Category.assoc, ← hw,
      Category.assoc, yonedaEquiv_yoneda_map_comp]
  rw [key]
  exact hle _ ⟨hfE.rep.fst' τ, rfl⟩

/-! ### The algebraic-spaces form of Stacks 01HP -/

/-- **The algebraic-spaces form of Stacks 01HP.** Let `Z` and `N` be closed subspaces of an
algebraic space `U` with the ideal sheaf of `N` the `(n+1)`st power of that of `Z` on every
étale chart. A morphism to `U` whose restriction to an `n`th-order thickening factors through
`Z` has image in `N`. -/
theorem range_le_of_isNthOrderThickening {n : ℕ} {Y U : AlgebraicSpaces B S hS}
    (Z N : ClosedSubspaces B S hS U.1)
    (hN : ∀ V : SmallEtale B S hS U.1,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ (n + 1))
    {G : Subfunctor Y.1} (hG : IsNthOrderThickening B S hS n Y G)
    (h : Y.1 ⟶ U.1) (a : G.toFunctor ⟶ Z.1.toFunctor)
    (hcomp : G.ι ≫ h = a ≫ Z.1.ι) :
    Subfunctor.range h ≤ N.1 := by
  obtain ⟨W, f, hfS, hfE⟩ := Y.2.exists_atlas
  obtain ⟨W₀, j, p, hpb, hj⟩ := exists_nthOrderThickening_chart_pullback B S hS hG W f hfE
  have haZ : (p ≫ a) ≫ Z.1.ι = yoneda.map j ≫ (f ≫ h) := by
    rw [Category.assoc, ← hcomp, ← Category.assoc, hpb.w, Category.assoc]
  have hfac : ∃ g : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ :
      AlgebraicSpaces B S hS) ⟶ (⟨N.1.toFunctor, N.2.1⟩ : AlgebraicSpaces B S hS),
      g ≫ ObjectProperty.homMk N.1.ι =
        (ObjectProperty.homMk (f ≫ h) :
          (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶ U) := by
    refine (exists_comp_eq_iff_forall_ker_le B S hS U _ N _).2 ?_
    intro V a₀ k y hy
    obtain ⟨y₀, rfl⟩ : ∃ y₀ : a₀ ⟶ W, yoneda.map y₀ = y := ⟨yoneda.preimage y, by simp⟩
    have hy' : yoneda.map k ≫ V.1.hom = yoneda.map y₀ ≫ (f ≫ h) := hy
    rw [hN V]
    have hsq : IsPullback (Limits.pullback.fst j y₀) (Limits.pullback.snd j y₀) j y₀ :=
      IsPullback.of_hasPullback j y₀
    have hjA : Stacks.Thickenings.IsNthOrderThickening n
        ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd j y₀)) :=
      Stacks.Thickenings.isNthOrderThickening_of_isPullback
        (((BigFppfOver.toScheme B S hS).map_isPullback hsq).flip) hj
    refine ker_pow_le_ker_of_isNthOrderThickening B S hS Z V k (Limits.pullback.snd j y₀) hjA
      (yoneda.map (Limits.pullback.fst j y₀) ≫ (p ≫ a)) ?_
    have e : yoneda.map (Limits.pullback.fst j y₀) ≫ yoneda.map j =
        yoneda.map (Limits.pullback.snd j y₀) ≫ yoneda.map y₀ := by
      rw [← Functor.map_comp, ← Functor.map_comp, hsq.w]
    rw [Category.assoc, haZ, ← Category.assoc, e, Category.assoc, ← hy', Functor.map_comp,
      Category.assoc]
  obtain ⟨g, hg⟩ := hfac
  have hgh : g.hom ≫ N.1.ι = f ≫ h := congrArg InducedCategory.Hom.hom hg
  have hrange : Subfunctor.range (f ≫ h) ≤ N.1 := by
    intro T x hx
    obtain ⟨x₀, hx₀⟩ := hx
    rw [← hx₀, ← hgh]
    exact (g.hom.app T x₀).2
  exact range_le_of_range_comp_le B S hS U.2.isSheaf N.1 N.2.1.isSheaf f hfS hfE h hrange

/-! ### The universal property -/

/-- **Stacks 05ZW, part (2).** The universal property of the `n`th-order infinitesimal
neighbourhood of an immersion. Let `Z` be a closed subspace of an open subspace `U` of `X` and
let `N` be the closed subspace of `U` cut out by the `(n+1)`st power of the ideal sheaf of `Z`.
Then every `n`th-order thickening `G ⊆ T'` over `X` compatible with `Z` admits a unique
morphism to `N` over `X` extending the given map of its closed part. -/
@[stacks 05ZW "part (2): nth-order universal property"]
theorem existsUnique_lift_of_isNthOrderThickening {n : ℕ} {X T' : AlgebraicSpaces B S hS}
    {U : Subfunctor X.1} (hU : IsOpenSubspace B S hS U)
    (Z N : ClosedSubspaces B S hS U.toFunctor)
    (hN : ∀ V : SmallEtale B S hS U.toFunctor,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ (n + 1))
    {G : Subfunctor T'.1} (hG : IsNthOrderThickening B S hS n T' G)
    (a : G.toFunctor ⟶ Z.1.toFunctor) (b : T'.1 ⟶ X.1)
    (hab : G.ι ≫ b = a ≫ Z.1.ι ≫ U.ι) :
    ∃! a' : T'.1 ⟶ N.1.toFunctor,
      G.ι ≫ a' ≫ N.1.ι = a ≫ Z.1.ι ∧ a' ≫ N.1.ι ≫ U.ι = b := by
  have hpts : Set.range (pointsMap B S hS T'.1 b) ⊆
      Set.range (pointsMap B S hS U.toFunctor U.ι) := by
    rintro q ⟨t', rfl⟩
    obtain ⟨t, rfl⟩ := hG.1.2 t'
    refine ⟨pointsMap B S hS Z.1.toFunctor Z.1.ι (pointsMap B S hS G.toFunctor a t), ?_⟩
    have e₁ := congrFun (pointsMap_comp B S hS G.toFunctor G.ι b) t
    have e₂ := congrFun (pointsMap_comp B S hS G.toFunctor a (Z.1.ι ≫ U.ι)) t
    have e₃ := congrFun (pointsMap_comp B S hS Z.1.toFunctor Z.1.ι U.ι)
      (pointsMap B S hS G.toFunctor a t)
    simp only [Function.comp_apply] at e₁ e₂ e₃
    rw [← e₃, ← e₂, ← hab, e₁]
  obtain ⟨b₁, hb₁⟩ := (factorsThrough_openSubspace_iff_points B S hS X.2 T'.2 U hU b).2 hpts
  have hcomp : G.ι ≫ b₁ = a ≫ Z.1.ι := by
    have h2 : (G.ι ≫ b₁) ≫ U.ι = (a ≫ Z.1.ι) ≫ U.ι := by
      rw [Category.assoc, hb₁, hab, Category.assoc]
    exact (cancel_mono U.ι).1 h2
  have hrange := range_le_of_isNthOrderThickening B S hS
    (U := ⟨U.toFunctor, hU.1⟩) Z N hN hG b₁ a hcomp
  refine ⟨Subfunctor.lift b₁ hrange, ⟨?_, ?_⟩, ?_⟩
  · rw [Subfunctor.lift_ι]; exact hcomp
  · rw [← Category.assoc, Subfunctor.lift_ι]; exact hb₁
  · intro y hy
    refine (cancel_mono N.1.ι).1 ?_
    rw [Subfunctor.lift_ι]
    refine (cancel_mono U.ι).1 ?_
    rw [hb₁, Category.assoc]
    exact hy.2

/-- **Stacks 05ZW, part (1).** The universal property of the first-order infinitesimal
neighbourhood of an immersion: the case `n = 1` of
`AlgebraicGeometry.Space.existsUnique_lift_of_isNthOrderThickening`. -/
@[stacks 05ZW "part (1): first-order universal property"]
theorem existsUnique_lift_of_isFirstOrderThickening {X T' : AlgebraicSpaces B S hS}
    {U : Subfunctor X.1} (hU : IsOpenSubspace B S hS U)
    (Z N : ClosedSubspaces B S hS U.toFunctor)
    (hN : ∀ V : SmallEtale B S hS U.toFunctor,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ 2)
    {G : Subfunctor T'.1} (hG : IsFirstOrderThickening B S hS T' G)
    (a : G.toFunctor ⟶ Z.1.toFunctor) (b : T'.1 ⟶ X.1)
    (hab : G.ι ≫ b = a ≫ Z.1.ι ≫ U.ι) :
    ∃! a' : T'.1 ⟶ N.1.toFunctor,
      G.ι ≫ a' ≫ N.1.ι = a ≫ Z.1.ι ∧ a' ≫ N.1.ι ≫ U.ι = b :=
  existsUnique_lift_of_isNthOrderThickening B S hS hU Z N hN hG a b hab

end Space

end AlgebraicGeometry

end
