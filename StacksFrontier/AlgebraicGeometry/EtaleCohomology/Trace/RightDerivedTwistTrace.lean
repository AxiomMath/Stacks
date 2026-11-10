module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExactPushforwardTwistTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientChangeTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperPushforwardTwistTrace

/-!
# Twisted traces along a left exact functor preserving injectives

Let `G : C' ⥤ C` be an additive functor between abelian categories with enough injectives which
preserves injective objects, but which need not be exact (in the application, the direct image
along a proper morphism), and let twists `P`, `P'`, functors `F₁`, `F₁'`, identifications
`θ : P ⋙ F₁ ≅ F₁`, `θ' : P' ⋙ F₁' ≅ F₁'`, `γ : G ⋙ F₁ ≅ F₁'` and `ρ : P' ⋙ G ⟶ G ⋙ P` be given,
compatibly. For a bounded below complex `T'` of injectives with a twist `g'`, `G(T')` computes
`RG(T')` and carries the twist `G(g') ≫ ρ`. If a bounded below complex `K` with a twist `τ` maps
to `G(T')` by a quasi-isomorphism `φ` compatible with the twists in the derived category, then the
trace of the derived twisted endomorphism of `RF₂(RF₁(K))` attached to `τ` is that of
`RF₂(RF₁'(T'))` attached to `g'`.

This is the abstract form of the invariance of the canonical Frobenius trace under proper direct
images, `RΓ(Y_k̄, (Rh_* N)|_{Y_k̄}) ≅ RΓ(X_k̄, N|_{X_k̄})`, in the fibration step of the proof of
the trace formula in any dimension, [Stacks, Tag 03UI] (1): `φ` is the proper base change map, a
quasi-isomorphism by [Stacks, Tag 095T].

## Main results

* `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_quasiIso_map`.
* `CategoryTheory.Functor.isPerfect_rightDerived_of_quasiIso_map_iff`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

universe u v u₁ v₁

namespace CategoryTheory.Functor

variable {R : Type u} [Ring R] {C C' D : Type u₁} [Category.{v₁} C] [Category.{v₁} C']
  [Category.{v₁} D] [Abelian C] [Abelian C'] [Abelian D] [EnoughInjectives C]
  [EnoughInjectives C'] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (P' : C' ⥤ C') (F₁' : C' ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R)
  (G : C' ⥤ C) [P.Additive] [F₁.Additive] [P'.Additive] [F₁'.Additive] [F₂.Additive] [G.Additive]
  [P.PreservesInjectiveObjects] [P'.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects]
  [F₁'.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]
  (θ : P ⋙ F₁ ≅ F₁) (θ' : P' ⋙ F₁' ≅ F₁') (γ : G ⋙ F₁ ≅ F₁') (ρ : P' ⋙ G ⟶ G ⋙ P)

/-- Perfectness is invariant under isomorphism in the derived category, as an equivalence. -/
private lemma isPerfect_iff_of_derived_iso {X Y : DerivedCategory (ModuleCat.{max u v} R)}
    (e : X ≅ Y) :
    StacksDraft.Perfect.IsPerfect X ↔ StacksDraft.Perfect.IsPerfect Y :=
  ⟨fun h => StacksDraft.Perfect.isPerfect_of_iso e.symm h,
    fun h => StacksDraft.Perfect.isPerfect_of_iso e h⟩

/-- A functor preserving injectives maps a complex of injectives to a complex of injectives. -/
private lemma injective_X_mapCochainComplexPlus {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive] [F.PreservesInjectiveObjects]
    {T : CochainComplex.Plus A} (hT : ∀ n, Injective (T.obj.X n)) (n : ℤ) :
    Injective ((F.mapCochainComplexPlus.obj T).obj.X n) :=
  have := hT n; inferInstanceAs (Injective (F.obj (T.obj.X n)))

/-- The identity of a bounded below complex is a quasi-isomorphism. -/
private instance quasiIso_hom_id {A : Type*} [Category* A] [Abelian A]
    (T : CochainComplex.Plus A) : QuasiIso (InducedCategory.Hom.hom (𝟙 T)) :=
  inferInstanceAs (QuasiIso (𝟙 T.obj))

include γ in
/-- **Perfectness through a quasi-isomorphism into the image of a complex of injectives.** If
`φ : K ⟶ G(T')` is a quasi-isomorphism and `T'` has injective terms, `RF₂(RF₁(K))` is perfect
exactly when `RF₂(RF₁'(T'))` is. -/
lemma isPerfect_rightDerived_of_quasiIso_map_iff {K : CochainComplex.Plus C}
    {T' : CochainComplex.Plus C'} (hT' : ∀ n, Injective (T'.obj.X n))
    (φ : K ⟶ G.mapCochainComplexPlus.obj T') [QuasiIso φ.hom] :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj T')))) := by
  have hinjG := injective_X_mapCochainComplexPlus G hT'
  exact isPerfect_iff_of_derived_iso (twistResolutionIso F₁ F₂ φ hinjG ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (Functor.isoWhiskerRight γ F₂) _).app T'.obj) ≪≫
    (twistResolutionIso F₁' F₂ (𝟙 T') hT').symm)

variable (hθ : ∀ X, F₁.map (ρ.app X) ≫ θ.hom.app (G.obj X) ≫ γ.hom.app X =
  γ.hom.app (P'.obj X) ≫ θ'.hom.app X)

include hθ in
/-- **The twisted trace through a quasi-isomorphism into the image of a complex of injectives.**
Let `T'` be a bounded below complex of injectives with a twist `g' : T' ⟶ P'(T')`, and
`φ : K ⟶ G(T')` a quasi-isomorphism from a bounded below complex `K` with a twist `τ`, compatible
with `τ` and `G(g') ≫ ρ` in the derived category. Then the trace of the derived twisted
endomorphism of `RF₂(RF₁(K))` attached to `τ` equals that of `RF₂(RF₁'(T'))` attached to `g'`. -/
theorem perfectDerivedTrace_derivedTwistEndo_eq_of_quasiIso_map {K : CochainComplex.Plus C}
    {T' : CochainComplex.Plus C'} (hT' : ∀ n, Injective (T'.obj.X n))
    (τ : K ⟶ P.mapCochainComplexPlus.obj K) (g' : T' ⟶ P'.mapCochainComplexPlus.obj T')
    (φ : K ⟶ G.mapCochainComplexPlus.obj T') [QuasiIso φ.hom]
    (hφ : DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map φ) =
      DerivedCategory.Plus.Q.map (φ ≫ G.mapCochainComplexPlus.map g' ≫
        twistTransferMap P P' G ρ T'))
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)))))
    (hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj T'))))) :
    perfectDerivedTrace R ⟨_, hK⟩
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τ)) =
      perfectDerivedTrace R ⟨_, hK'⟩
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P' F₁' F₂ θ' T' g')) := by
  have hinjG := injective_X_mapCochainComplexPlus G hT'
  have hTG := StacksDraft.Perfect.isPerfect_of_iso (twistResolutionIso F₁ F₂ φ hinjG).symm hK
  have hT := StacksDraft.Perfect.isPerfect_of_iso (twistResolutionIso F₁' F₂ (𝟙 T') hT').symm hK'
  rw [perfectDerivedTrace_derivedTwistEndo_eq P F₁ F₂ θ φ hinjG τ _ hφ hK hTG,
    perfectDerivedTrace_derivedTwistEndo_eq P' F₁' F₂ θ' (𝟙 T') hT' g' g'
      (by simp) hK' hT]
  refine perfectDerivedTrace_congr R _ _ (DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex (Functor.isoWhiskerRight γ F₂) _).app T'.obj)) _ _ ?_
  refine (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map ?_).trans (DerivedCategory.Q.map_comp _ _))
  ext n : 1
  have h₁ := hθ (T'.obj.X n)
  have h₂ := γ.hom.naturality (g'.hom.f n)
  change F₂.map (F₁.map (G.map (g'.hom.f n) ≫ ρ.app (T'.obj.X n)) ≫
      θ.hom.app (G.obj (T'.obj.X n))) ≫ F₂.map (γ.hom.app (T'.obj.X n)) =
    F₂.map (γ.hom.app (T'.obj.X n)) ≫ F₂.map (F₁'.map (g'.hom.f n) ≫ θ'.hom.app (T'.obj.X n))
  rw [← F₂.map_comp, ← F₂.map_comp]
  congr 1
  dsimp only [Functor.comp_map] at h₂
  rw [show F₁.map (G.map (g'.hom.f n) ≫ ρ.app (T'.obj.X n)) =
      F₁.map (G.map (g'.hom.f n)) ≫ F₁.map (ρ.app (T'.obj.X n)) from F₁.map_comp _ _,
    Category.assoc, Category.assoc]
  refine (congrArg (fun t => F₁.map (G.map (g'.hom.f n)) ≫ t) h₁).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ θ'.hom.app (T'.obj.X n)) h₂).trans (Category.assoc _ _ _))

include hθ in
/-- **The twisted trace through a base change map which is a quasi-isomorphism after
resolving.** Let `β : K ⟶ G(K')` carry the twist `τ` of `K` to the twist `G(τ') ≫ ρ` of `G(K')`,
strictly, and suppose that `β ≫ G(ψ)` is a quasi-isomorphism for every quasi-isomorphism
`ψ : K' ⟶ T'` into a bounded below complex of injectives (that is, the derived base change map
`K ⟶ RG(K')` attached to `β` is invertible). Then the trace of the derived twisted endomorphism of
`RF₂(RF₁(K))` attached to `τ` equals that of `RF₂(RF₁'(K'))` attached to `τ'`, and the two
complexes are perfect together. -/
theorem perfectDerivedTrace_derivedTwistEndo_eq_of_baseChange {K : CochainComplex.Plus C}
    {K' : CochainComplex.Plus C'} (τ : K ⟶ P.mapCochainComplexPlus.obj K)
    (τ' : K' ⟶ P'.mapCochainComplexPlus.obj K') (β : K ⟶ G.mapCochainComplexPlus.obj K')
    (hβ : β ≫ G.mapCochainComplexPlus.map τ' ≫ twistTransferMap P P' G ρ K' =
      τ ≫ P.mapCochainComplexPlus.map β)
    (hq : ∀ (T' : CochainComplex.Plus C') (ψ : K' ⟶ T'), QuasiIso ψ.hom →
      (∀ n, Injective (T'.obj.X n)) → QuasiIso (β ≫ G.mapCochainComplexPlus.map ψ).hom) :
    ∃ (_hiff : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (F₂.rightDerivedFunctorPlus.obj (F₁.rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj K)))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K'))))),
      ∀ hK hK', perfectDerivedTrace R ⟨_, hK⟩
          (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τ)) =
        perfectDerivedTrace R ⟨_, hK'⟩
          (DerivedCategory.Plus.ι.map (derivedTwistEndo P' F₁' F₂ θ' K' τ')) := by
  obtain ⟨T', ψ, hψ, hT', g', hg⟩ := exists_twist_lift_of_injectiveResolution P' K' τ'
  have := hq T' ψ hψ hT'
  -- `K'` and `T'` have the same twisted trace
  have hT'iff : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (F₂.rightDerivedFunctorPlus.obj (F₁'.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj K')))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj T')))) := by
    exact isPerfect_iff_of_derived_iso
      (twistResolutionIso F₁' F₂ ψ hT' ≪≫ (twistResolutionIso F₁' F₂ (𝟙 T') hT').symm)
  -- the twists are compatible along `φ = β ≫ G(ψ)` in the derived category
  have hφ : DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map
      (β ≫ G.mapCochainComplexPlus.map ψ)) =
      DerivedCategory.Plus.Q.map ((β ≫ G.mapCochainComplexPlus.map ψ) ≫
        G.mapCochainComplexPlus.map g' ≫ twistTransferMap P P' G ρ T') := by
    obtain ⟨b, hb⟩ := (P'.mapCochainComplexPlus.obj T').property
    have := injective_X_mapCochainComplexPlus P' hT'
    have := CochainComplex.isKInjective_of_injective (P'.mapCochainComplexPlus.obj T').obj b
    obtain ⟨hhom⟩ := Stacks.EtaleCohomology.homotopy_of_Q_map_eq_of_isKInjective
      (τ' ≫ P'.mapCochainComplexPlus.map ψ).hom (ψ ≫ g').hom
      (congrArg DerivedCategory.Plus.ι.map hg)
    have hG := DerivedCategory.Q_map_eq_of_homotopy (h := G.mapHomotopy hhom)
    have hGeq : DerivedCategory.Plus.Q.map
        (G.mapCochainComplexPlus.map (τ' ≫ P'.mapCochainComplexPlus.map ψ)) =
        DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map (ψ ≫ g')) :=
      DerivedCategory.Plus.ι.map_injective hG
    have hnat : twistTransferMap P P' G ρ K' ≫
        P.mapCochainComplexPlus.map (G.mapCochainComplexPlus.map ψ) =
        G.mapCochainComplexPlus.map (P'.mapCochainComplexPlus.map ψ) ≫
          twistTransferMap P P' G ρ T' := by
      ext n : 2
      exact (ρ.naturality (ψ.hom.f n)).symm
    have e1 : τ ≫ P.mapCochainComplexPlus.map (β ≫ G.mapCochainComplexPlus.map ψ) =
        β ≫ G.mapCochainComplexPlus.map (τ' ≫ P'.mapCochainComplexPlus.map ψ) ≫
          twistTransferMap P P' G ρ T' := by
      rw [Functor.map_comp, ← Category.assoc, ← hβ, Functor.map_comp]
      simp only [Category.assoc, hnat]
    have e2 : (β ≫ G.mapCochainComplexPlus.map ψ) ≫ G.mapCochainComplexPlus.map g' ≫
        twistTransferMap P P' G ρ T' =
        β ≫ G.mapCochainComplexPlus.map (ψ ≫ g') ≫ twistTransferMap P P' G ρ T' := by
      rw [Functor.map_comp]; simp only [Category.assoc]
    rw [e1, e2, DerivedCategory.Plus.Q.map_comp β, DerivedCategory.Plus.Q.map_comp β,
      DerivedCategory.Plus.Q.map_comp (G.mapCochainComplexPlus.map _),
      DerivedCategory.Plus.Q.map_comp (G.mapCochainComplexPlus.map _), hGeq]
  have hiff := isPerfect_rightDerived_of_quasiIso_map_iff F₁ F₁' F₂ G γ hT'
    (β ≫ G.mapCochainComplexPlus.map ψ)
  refine ⟨hiff.trans hT'iff.symm, fun hK hK' => ?_⟩
  have hT := hT'iff.1 hK'
  rw [perfectDerivedTrace_derivedTwistEndo_eq_of_quasiIso_map P F₁ P' F₁' F₂ G θ θ' γ ρ hθ hT' τ
    g' _ hφ hK hT]
  have hT₀ := StacksDraft.Perfect.isPerfect_of_iso (twistResolutionIso F₁' F₂ (𝟙 T') hT').symm hT
  rw [perfectDerivedTrace_derivedTwistEndo_eq P' F₁' F₂ θ' (𝟙 T') hT' g' g' (by simp) hT hT₀,
    perfectDerivedTrace_derivedTwistEndo_eq P' F₁' F₂ θ' ψ hT' τ' g' hg hK' hT₀]

section Square

variable {A B E E' : Type*} [Category* A] [Category* B] [Category* E] [Category* E']
  [Abelian A] [Abelian B] [Abelian E] [Abelian E']
  (I : A ⥤ B) (g : B ⥤ E) (g' : A ⥤ E') (G' : E' ⥤ E) (Q : E ⥤ E) (Q' : E' ⥤ E')
  [I.Additive] [g.Additive] [g'.Additive] [G'.Additive] [Q.Additive] [Q'.Additive]

/-- **A base change map compatible with twists objectwise is compatible with them on complexes.**
For `β : I ⋙ g ⟶ g' ⋙ G'`, twists `tw : g ⟶ g ⋙ Q`, `tw' : g' ⟶ g' ⋙ Q'` and `ρ : Q' ⋙ G' ⟶ G' ⋙ Q`
with `β ≫ G'(tw') ≫ ρ = tw ≫ Q(β)` on objects, the same identity holds degreewise on every bounded
below complex. -/
lemma mapCochainComplexPlus_baseChange_comp_twist (β : I ⋙ g ⟶ g' ⋙ G') (tw : g ⟶ g ⋙ Q)
    (tw' : g' ⟶ g' ⋙ Q') (ρ : Q' ⋙ G' ⟶ G' ⋙ Q)
    (hβ : ∀ X, β.app X ≫ G'.map (tw'.app X) ≫ ρ.app (g'.obj X) = tw.app (I.obj X) ≫ Q.map (β.app X))
    (M : CochainComplex.Plus A) :
    (ObjectProperty.homMk (X := g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))
        (Y := G'.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M))
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app M.obj)) ≫
      G'.mapCochainComplexPlus.map (ObjectProperty.homMk
        (X := g'.mapCochainComplexPlus.obj M)
        (Y := Q'.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M))
        ((NatTrans.mapHomologicalComplex tw' (ComplexShape.up ℤ)).app M.obj)) ≫
      (ObjectProperty.homMk
        (X := G'.mapCochainComplexPlus.obj (Q'.mapCochainComplexPlus.obj
          (g'.mapCochainComplexPlus.obj M)))
        (Y := Q.mapCochainComplexPlus.obj (G'.mapCochainComplexPlus.obj
          (g'.mapCochainComplexPlus.obj M)))
        ((NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℤ)).app
          (g'.mapCochainComplexPlus.obj M).obj)) =
    (ObjectProperty.homMk (X := g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))
        (Y := Q.mapCochainComplexPlus.obj (g.mapCochainComplexPlus.obj
          (I.mapCochainComplexPlus.obj M)))
        ((NatTrans.mapHomologicalComplex tw (ComplexShape.up ℤ)).app
          (I.mapCochainComplexPlus.obj M).obj)) ≫
      Q.mapCochainComplexPlus.map (ObjectProperty.homMk
        (X := g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))
        (Y := G'.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M))
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app M.obj)) := by
  ext n : 2
  exact hβ (M.obj.X n)

end Square

section NatTrans

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (I : A ⥤ B) (g : B ⥤ C) (g' : A ⥤ C') [I.Additive] [g.Additive] [g'.Additive]
  (β : I ⋙ g ⟶ g' ⋙ G) (tw : g ⟶ g ⋙ P) (tw' : g' ⟶ g' ⋙ P')
  (hβ : ∀ X, β.app X ≫ G.map (tw'.app X) ≫ ρ.app (g'.obj X) = tw.app (I.obj X) ≫ P.map (β.app X))

/-- The composite `g(I M) ⟶ G(g' M) ⟶ G(T')` of the base change map `β_M` and `G(ψ)`. -/
abbrev baseChangeComp (M : CochainComplex.Plus A) {T' : CochainComplex.Plus C'}
    (ψ : g'.mapCochainComplexPlus.obj M ⟶ T') :
    g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M) ⟶ G.mapCochainComplexPlus.obj T' :=
  (ObjectProperty.homMk
    (X := g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))
    (Y := G.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M))
    ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app M.obj)) ≫
      G.mapCochainComplexPlus.map ψ

omit [EnoughInjectives C] [EnoughInjectives C'] [G.PreservesInjectiveObjects] in
/-- `BaseChangeQuasiIsoAt` only depends on the transformation. -/
lemma BaseChangeQuasiIsoAt.of_eq {β β' : I ⋙ g ⟶ g' ⋙ G} {M : CochainComplex.Plus A}
    (h : BaseChangeQuasiIsoAt G I g g' β M) (e : β = β') : BaseChangeQuasiIsoAt G I g g' β' M :=
  e ▸ h

omit [EnoughInjectives C] [EnoughInjectives C'] [G.PreservesInjectiveObjects] in
/-- `BaseChangeQuasiIsoAt` at a resolution `ψ`, stated through `baseChangeComp`. -/
lemma BaseChangeQuasiIsoAt.quasiIso_baseChangeComp {M : CochainComplex.Plus A}
    (h : BaseChangeQuasiIsoAt G I g g' β M) {T' : CochainComplex.Plus C'}
    (ψ : g'.mapCochainComplexPlus.obj M ⟶ T') (hψ : QuasiIso ψ.hom)
    (hT : ∀ n, Injective (T'.obj.X n)) : QuasiIso (baseChangeComp G I g g' β M ψ).hom :=
  h T' ψ hψ hT

include hθ hβ in
/-- **The twisted trace through a base change transformation which is a quasi-isomorphism after
resolving.** For `β : I ⋙ g ⟶ g' ⋙ G` carrying the twist `tw` to `tw'` through `ρ`, objectwise,
and a bounded below complex `M` such that `β_M ≫ G(ψ)` is a quasi-isomorphism for every resolution
`ψ` of `g'(M)` by injectives, the derived twisted endomorphisms of `RF₂(RF₁(g(I M)))` and
`RF₂(RF₁'(g' M))` attached to `tw` and `tw'` are perfect together and have the same trace. -/
theorem perfectDerivedTrace_derivedTwistEndo_eq_of_baseChangeTrans (M : CochainComplex.Plus A)
    (hq : BaseChangeQuasiIsoAt G I g g' β M) :
    ∃ (_hiff : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (F₂.rightDerivedFunctorPlus.obj (F₁.rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M)))))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
          (g'.mapCochainComplexPlus.obj M)))))),
      ∀ hK hK', perfectDerivedTrace R ⟨_, hK⟩ (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂
          θ (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))
          (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex tw (ComplexShape.up ℤ)).app
            (I.mapCochainComplexPlus.obj M).obj)))) =
        perfectDerivedTrace R ⟨_, hK'⟩ (DerivedCategory.Plus.ι.map (derivedTwistEndo P' F₁' F₂ θ'
          (g'.mapCochainComplexPlus.obj M)
          (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex tw' (ComplexShape.up ℤ)).app
            M.obj)))) :=
  perfectDerivedTrace_derivedTwistEndo_eq_of_baseChange P F₁ P' F₁' F₂ G θ θ' γ ρ hθ _ _ _
    (mapCochainComplexPlus_baseChange_comp_twist I g g' G P P' β tw tw' ρ hβ M) hq

end NatTrans

end CategoryTheory.Functor

end
