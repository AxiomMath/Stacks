module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionFrobeniusTraceInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedTwistComposition

/-!
# The twisted trace along a non-exact direct image, through a base change quasi-isomorphism

Let `G : 𝒞' ⥤ 𝒞` be an additive functor preserving injective objects, for instance the direct
image along a proper morphism of schemes, which is not exact.  Let `K'` be a bounded below complex
on `𝒞'` with a twist `τ' : K' ⟶ P'(K')`, and let `N` be a bounded below complex on `𝒞` with a twist
`τ : N ⟶ P(N)` and a morphism `β : N ⟶ G(K')` carrying `τ` to `G(τ') ≫ ρ`.  If `β` followed by `G`
of any injective resolution of `K'` is a quasi-isomorphism (the proper base change theorem, in the
application), then the derived twisted endomorphism of `RF₂(RF₁(N))` attached to `τ` and that of
`RF₂(RF₁'(K'))` attached to `τ'` have the same trace, and perfectness of one complex is perfectness
of the other.

This generalizes `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_baseChange_eq`, where
`G` is exact and `β` is an isomorphism. The quasi-isomorphism hypothesis is stated on the
underlying morphisms of complexes, the form in which a base change theorem for sheaves is available
without unfolding the bounded below subcategory.  It is the formal part of the Leray step in the
proof of [Stacks, Tag 03V3]: `RΓ(X̄'_k̄, C) = RΓ(X̄_k̄, Rπ_* C)` for a proper morphism
`π : X̄' ⟶ X̄` over a finite field, compatibly with the geometric Frobenius.

## Main results

* `CategoryTheory.Functor.isPerfect_iff_of_baseChange_quasiIso`: perfectness transfers.
* `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_baseChange_quasiIso`: the
  traces agree.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

universe u v u₁ v₁

namespace CategoryTheory.Functor

section NonExact

variable {R : Type u} [Ring R] {C C' D : Type u₁} [Category.{v₁} C] [Category.{v₁} C']
  [Category.{v₁} D] [Abelian C] [Abelian C'] [Abelian D] [EnoughInjectives C]
  [EnoughInjectives C'] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (P' : C' ⥤ C') (F₁' : C' ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R)
  (G : C' ⥤ C) [P.Additive] [F₁.Additive] [P'.Additive] [F₁'.Additive] [F₂.Additive] [G.Additive]
  [P.PreservesInjectiveObjects] [P'.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects]
  [F₁'.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]
  (θ : P ⋙ F₁ ≅ F₁) (θ' : P' ⋙ F₁' ≅ F₁') (γ : G ⋙ F₁ ≅ F₁') (ρ : P' ⋙ G ⟶ G ⋙ P)

omit [EnoughInjectives C] [EnoughInjectives C'] in
/-- `G` of a bounded below complex of injectives is a bounded below complex of injectives. -/
lemma injective_mapCochainComplexPlus_obj {T : CochainComplex.Plus C'}
    (hT : ∀ n, Injective (T.obj.X n)) (n : ℤ) :
    Injective ((G.mapCochainComplexPlus.obj T).obj.X n) :=
  inferInstanceAs (Injective (G.obj (T.obj.X n)))

/-- The isomorphism `RF₂(RF₁(N)) ≅ RF₂(RF₁'(K'))` through an injective resolution `ψ : K' ⟶ T`
such that `β ≫ G(ψ)` is a quasi-isomorphism. -/
def baseChangeResolutionIso {N : CochainComplex.Plus C} {K' T : CochainComplex.Plus C'}
    (β : N ⟶ G.mapCochainComplexPlus.obj K') (ψ : K' ⟶ T) [QuasiIso ψ.hom]
    (hT : ∀ n, Injective (T.obj.X n)) [QuasiIso (β ≫ G.mapCochainComplexPlus.map ψ).hom] :
    DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj N))) ≅
      DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K'))) :=
  twistResolutionIso F₁ F₂ (β ≫ G.mapCochainComplexPlus.map ψ)
      (injective_mapCochainComplexPlus_obj G hT) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (Functor.isoWhiskerRight γ F₂) _).app T.obj) ≪≫
    (twistResolutionIso F₁' F₂ ψ hT).symm

variable {G} in
include γ in
/-- **Perfectness transfers along a base change quasi-isomorphism.**  If `β : N ⟶ G(K')` followed
by `G` of every injective resolution of `K'` is a quasi-isomorphism, then `RF₂(RF₁(N))` is perfect
exactly when `RF₂(RF₁'(K'))` is. -/
lemma isPerfect_iff_of_baseChange_quasiIso {N : CochainComplex.Plus C}
    {K' : CochainComplex.Plus C'}
    (β : N.obj ⟶ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K'.obj)
    (hPBC : ∀ (T : CochainComplex.Plus C') (ψ : K' ⟶ T), QuasiIso ψ.hom →
      (∀ n, Injective (T.obj.X n)) →
        QuasiIso (β ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.hom)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj N)))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K')))) := by
  obtain ⟨T, ψ, hq, hinj, -, -⟩ := exists_twist_lift_of_injectiveResolution (𝟭 C') K' (𝟙 _)
  have : QuasiIso ((ObjectProperty.homMk β : N ⟶ G.mapCochainComplexPlus.obj K') ≫
    G.mapCochainComplexPlus.map ψ).hom := hPBC T ψ hq hinj
  let e := baseChangeResolutionIso F₁ F₁' F₂ G γ (ObjectProperty.homMk β) ψ hinj
  exact ⟨StacksDraft.Perfect.isPerfect_of_iso e.symm, StacksDraft.Perfect.isPerfect_of_iso e⟩

variable (hθ : ∀ X, F₁.map (ρ.app X) ≫ θ.hom.app (G.obj X) ≫ γ.hom.app X =
  γ.hom.app (P'.obj X) ≫ θ'.hom.app X)

include hθ in
/-- **The twisted trace along a base change quasi-isomorphism.**  Let `τ'` be a twist of `K'`,
`τ` a twist of `N` and `β : N ⟶ G(K')` a morphism carrying `τ` to `G(τ') ≫ ρ`.  If `β` followed by
`G` of every injective resolution of `K'` is a quasi-isomorphism, then the trace of the derived
twisted endomorphism of `RF₂(RF₁(N))` attached to `τ` is that of `RF₂(RF₁'(K'))` attached to
`τ'`. -/
theorem perfectDerivedTrace_derivedTwistEndo_eq_of_baseChange_quasiIso
    (K' : CochainComplex.Plus C') (τ' : K' ⟶ P'.mapCochainComplexPlus.obj K')
    (N : CochainComplex.Plus C) (τ : N ⟶ P.mapCochainComplexPlus.obj N)
    (β : N.obj ⟶ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K'.obj)
    (hβ : τ.hom ≫ (P.mapHomologicalComplex (ComplexShape.up ℤ)).map β =
      β ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map τ'.hom ≫
        (NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℤ)).app K'.obj)
    (hPBC : ∀ (T : CochainComplex.Plus C') (ψ : K' ⟶ T), QuasiIso ψ.hom →
      (∀ n, Injective (T.obj.X n)) →
        QuasiIso (β ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.hom))
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj N)))))
    (hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K'))))) :
    perfectDerivedTrace R ⟨_, hK⟩ (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ N τ)) =
      perfectDerivedTrace R ⟨_, hK'⟩
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P' F₁' F₂ θ' K' τ')) := by
  let βp : N ⟶ G.mapCochainComplexPlus.obj K' := ObjectProperty.homMk β
  have hβp : τ ≫ P.mapCochainComplexPlus.map βp =
      βp ≫ G.mapCochainComplexPlus.map τ' ≫ twistTransferMap P P' G ρ K' := by
    ext : 1
    exact hβ
  obtain ⟨T, ψ, hq, hinj, g, hg⟩ := exists_twist_lift_of_injectiveResolution P' K' τ'
  have hT' := StacksDraft.Perfect.isPerfect_of_iso (twistResolutionIso F₁' F₂ ψ hinj).symm hK'
  rw [perfectDerivedTrace_derivedTwistEndo_eq P' F₁' F₂ θ' ψ hinj τ' g hg hK' hT']
  have : QuasiIso (βp ≫ G.mapCochainComplexPlus.map ψ).hom := hPBC T ψ hq hinj
  have hinjG := injective_mapCochainComplexPlus_obj G hinj
  have hgG : DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map
        (βp ≫ G.mapCochainComplexPlus.map ψ)) =
      DerivedCategory.Plus.Q.map ((βp ≫ G.mapCochainComplexPlus.map ψ) ≫
        (G.mapCochainComplexPlus.map g ≫ twistTransferMap P P' G ρ T)) := by
    have h₀ : DerivedCategory.Q.map (τ' ≫ P'.mapCochainComplexPlus.map ψ).hom =
        DerivedCategory.Q.map (ψ ≫ g).hom := DerivedCategory.Plus.ι.congr_map hg
    have := injective_mapCochainComplexPlus_obj P' hinj
    have h₁ : DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map
          (τ' ≫ P'.mapCochainComplexPlus.map ψ)) =
        DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map (ψ ≫ g)) :=
      DerivedCategory.Plus.ι.map_injective
        (Q_map_mapHomologicalComplex_eq_of_injective G (P'.mapCochainComplexPlus.obj T).property h₀)
    have hn : twistTransferMap P P' G ρ K' ≫
          P.mapCochainComplexPlus.map (G.mapCochainComplexPlus.map ψ) =
        G.mapCochainComplexPlus.map (P'.mapCochainComplexPlus.map ψ) ≫
          twistTransferMap P P' G ρ T := by
      ext n : 2
      exact (ρ.naturality (ψ.hom.f n)).symm
    calc DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map
          (βp ≫ G.mapCochainComplexPlus.map ψ))
        = DerivedCategory.Plus.Q.map (βp ≫ G.mapCochainComplexPlus.map
            (τ' ≫ P'.mapCochainComplexPlus.map ψ) ≫ twistTransferMap P P' G ρ T) := by
          congr 1
          rw [Functor.map_comp, reassoc_of% hβp, hn, Functor.map_comp, Category.assoc]
      _ = DerivedCategory.Plus.Q.map βp ≫ DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map
            (ψ ≫ g)) ≫ DerivedCategory.Plus.Q.map (twistTransferMap P P' G ρ T) := by
          rw [DerivedCategory.Plus.Q.map_comp, DerivedCategory.Plus.Q.map_comp, h₁]
      _ = _ := by simp only [Functor.map_comp, Category.assoc]
  have hTG := StacksDraft.Perfect.isPerfect_of_iso
    (twistResolutionIso F₁ F₂ (βp ≫ G.mapCochainComplexPlus.map ψ) hinjG).symm hK
  rw [perfectDerivedTrace_derivedTwistEndo_eq P F₁ F₂ θ (βp ≫ G.mapCochainComplexPlus.map ψ)
    hinjG _ _ hgG hK hTG]
  refine perfectDerivedTrace_congr R _ _ (DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex (Functor.isoWhiskerRight γ F₂) _).app T.obj)) _ _ ?_
  refine (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map ?_).trans (DerivedCategory.Q.map_comp _ _))
  ext n : 1
  have h₂ := γ.hom.naturality (g.hom.f n)
  change F₂.map (F₁.map (G.map (g.hom.f n) ≫ ρ.app (T.obj.X n)) ≫
      θ.hom.app (G.obj (T.obj.X n))) ≫ F₂.map (γ.hom.app (T.obj.X n)) =
    F₂.map (γ.hom.app (T.obj.X n)) ≫ F₂.map (F₁'.map (g.hom.f n) ≫ θ'.hom.app (T.obj.X n))
  rw [← F₂.map_comp, ← F₂.map_comp]
  congr 1
  dsimp only [Functor.comp_map] at h₂
  exact transferChase₂ F₁ _ _ _ _ _ _ _ _ (hθ (T.obj.X n)) h₂

section Functorial

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (I : A ⥤ B) (g : B ⥤ C) (g' : A ⥤ C') [I.Additive] [g.Additive] [g'.Additive]
  (βn : I ⋙ g ⟶ g' ⋙ G) (tw : g ⟶ g ⋙ P) (tw' : g' ⟶ g' ⋙ P')

/-- **The base change map is a quasi-isomorphism on resolutions at `M`**: for every injective
resolution `ψ : g'(M) ⟶ T`, the morphism of complexes `βn_M ≫ G(ψ) : g(I(M)) ⟶ G(T)` is a
quasi-isomorphism. For `βn` the base change map of a proper morphism this is the proper base change
theorem on resolutions. It is a named predicate so that a statement of it about sheaves and its
use in the abstract lemmas below are the same term. -/
def BaseChangeQuasiIsoAt (M : CochainComplex.Plus A) : Prop :=
  ∀ (T : CochainComplex.Plus C') (ψ : g'.mapCochainComplexPlus.obj M ⟶ T),
    QuasiIso ψ.hom → (∀ n, Injective (T.obj.X n)) →
      QuasiIso ((NatTrans.mapHomologicalComplex βn (ComplexShape.up ℤ)).app M.obj ≫
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.hom)

include hθ in
/-- **The twisted trace along a base change quasi-isomorphism, for twists and a base change map
given as natural transformations.**  Let `βn : I ⋙ g ⟶ g' ⋙ G` carry the twist `tw : g ⟶ g ⋙ P` to
`G(tw') ≫ ρ`, objectwise. If at a bounded below complex `M` the morphism `βn_M` followed by `G` of
every injective resolution of `g'(M)` is a quasi-isomorphism, then the derived twisted
endomorphisms of `RF₂(RF₁(g(I(M))))` attached to `tw` and of `RF₂(RF₁'(g'(M)))` attached to `tw'`
have the same trace. The comparison of the twists is taken objectwise, so that it can be supplied
by a statement about sheaves. -/
theorem perfectDerivedTrace_derivedTwistEndo_eq_of_baseChange_quasiIso_app
    (hβn : ∀ X, βn.app X ≫ G.map (tw'.app X) ≫ ρ.app (g'.obj X) =
      tw.app (I.obj X) ≫ P.map (βn.app X))
    (M : CochainComplex.Plus A)
    (hPBC : BaseChangeQuasiIsoAt G I g g' βn M)
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
          (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M)))))))
    (hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
          (g'.mapCochainComplexPlus.obj M)))))) :
    perfectDerivedTrace R ⟨_, hK⟩ (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ
        (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex tw (ComplexShape.up ℤ)).app
          (I.mapCochainComplexPlus.obj M).obj)))) =
      perfectDerivedTrace R ⟨_, hK'⟩ (DerivedCategory.Plus.ι.map (derivedTwistEndo P' F₁' F₂ θ'
        (g'.mapCochainComplexPlus.obj M)
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex tw' (ComplexShape.up ℤ)).app
          M.obj)))) :=
  perfectDerivedTrace_derivedTwistEndo_eq_of_baseChange_quasiIso P F₁ P' F₁' F₂ G θ θ' γ ρ hθ
    (g'.mapCochainComplexPlus.obj M) _ (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))
    _ ((NatTrans.mapHomologicalComplex βn (ComplexShape.up ℤ)).app M.obj)
    (by
      ext n : 1
      exact (hβn (M.obj.X n)).symm)
    hPBC hK hK'

include γ in
/-- Perfectness along a base change quasi-isomorphism given by a natural transformation. -/
lemma isPerfect_iff_of_baseChange_quasiIso_app (M : CochainComplex.Plus A)
    (hPBC : BaseChangeQuasiIsoAt G I g g' βn M) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
          (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M)))))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
          (g'.mapCochainComplexPlus.obj M))))) :=
  isPerfect_iff_of_baseChange_quasiIso F₁ F₁' F₂ γ
    ((NatTrans.mapHomologicalComplex βn (ComplexShape.up ℤ)).app M.obj) hPBC

end Functorial

end NonExact

end CategoryTheory.Functor

end
