module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification.Coverings

/-!
# The pullback of a stackification: the local injectivity of `Ψ`

The local content of Stacks 04WR: two morphisms of a fibre of `u_p 𝒮` with the same image under
`Ψ : u_p 𝒮 ⥤ u_p 𝒮'` agree locally on `𝒟`, and a morphism of a fibre of `u_p 𝒮'` between objects
in the image of `Ψ` lifts locally along `Ψ`.

## References

* [Stacks Project, Tag 04WR](https://stacks.math.columbia.edu/tag/04WR)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

/-! ### The local content of Stacks 04WR: injectivity -/

section CoreInjective

universe v

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v} 𝒮] {𝒮' : Type u₄} [Category.{v} 𝒮']
  (u : 𝒞 ⥤ 𝒟) (p : 𝒮 ⥤ 𝒞) (p' : 𝒮' ⥤ 𝒞) {G : 𝒮 ⥤ 𝒮'}

/-- A strongly cartesian morphism composed with another is `stronglyCartesianOver`. -/
private theorem stronglyCartesianOver_comp_of_isStronglyCartesian {R S T : 𝒞} {a b c : 𝒮}
    {k : R ⟶ S} {e : S ⟶ T} {φ : a ⟶ b} {γ : b ⟶ c} (hφ : p.IsStronglyCartesian k φ)
    (hγ : p.IsStronglyCartesian e γ) : stronglyCartesianOver p (φ ≫ γ) :=
  Comma.stronglyCartesianOver_of_isStronglyCartesian p
    (inferInstance : p.IsStronglyCartesian (k ≫ e) (φ ≫ γ))

/-- A strongly cartesian `ζ : Z ⟶ G c` of `𝒮'` is `δ.hom ≫ G γ` for a strongly cartesian `γ` of
`𝒮` into `c` and an isomorphism `δ` lying over an identity. -/
private theorem exists_stronglyCartesian_lift_fiber [p.IsFibered] [p'.IsFibered]
    (hGG : p.IsFibredOneMorphism p' G) {c : 𝒮} {Z : 𝒮'} (ζ : Z ⟶ G.obj c)
    (hζ : p'.IsStronglyCartesian (p'.map ζ) ζ) :
    ∃ (c₀ : p.Fiber (p'.obj Z)) (γ : c₀.1 ⟶ c) (δ : Z ≅ G.obj c₀.1),
      p.IsStronglyCartesian (p'.map ζ ≫ eqToHom (Functor.congr_obj hGG.comp_eq c)) γ ∧
        δ.hom ≫ G.map γ = ζ ∧ p'.IsHomLift (𝟙 (p'.obj Z)) δ.inv := by
  set e' : p'.obj Z ⟶ p.obj c := p'.map ζ ≫ eqToHom (Functor.congr_obj hGG.comp_eq c)
  have hζsc' : p'.IsStronglyCartesian e' ζ :=
    PullbackAdjunction.isStronglyCartesian_comp_eqToHom _ (p'.map ζ) ζ hζ
  set cF : p.Fiber (p.obj c) := Functor.Fiber.mk rfl
  set γ := Functor.IsPreFibered.pullbackMap cF.2 e'
  have hγsc : p.IsStronglyCartesian e' γ := inferInstance
  have hGγsc := hGG.map_isStronglyCartesian e' γ hγsc
  have hrefl : e' = (Iso.refl (p'.obj Z)).hom ≫ e' := by simp
  refine ⟨Functor.pullbackFiber p cF e', γ,
    Functor.IsStronglyCartesian.domainIsoOfBaseIso p' hrefl (G.map γ) ζ, hγsc,
    Functor.IsStronglyCartesian.fac p' e' (G.map γ) hrefl ζ, ?_⟩
  simpa using Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift p' hrefl (G.map γ) ζ

/-- **Two morphisms of a fibre of `u_p 𝒮` with the same image in `u_p 𝒮'` agree locally on
`𝒟`.** If the maps of morphism presheaves induced by `G` are locally injective, two morphisms
`Q(V, a, ψ) ⟶ Q(V, b, ω)` over `𝟙 V` with the same image under `Ψ` agree after precomposition
with the reindexing morphisms along the members of a `K`-covering sieve of `V`. -/
theorem locallyEqual_of_pullbackLocalizationMap_map_eq
    [p.IsFibered] [p'.IsFibered] [HasNonemptyFiniteLimits 𝒞]
    (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟) [u.IsContinuous J K]
    (hu : ∀ (J' : Type) [SmallCategory J'] [FinCategory J'] [Nonempty J'],
      Limits.PreservesLimitsOfShape J' u)
    (hGG : p.IsFibredOneMorphism p' G)
    (hinj : ∀ (U : 𝒞) (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hGG.morPresheafMap x y))
    {V : 𝒟} {a b : 𝒮} (ψ : V ⟶ u.obj (p.obj a)) (ω : V ⟶ u.obj (p.obj b))
    (n₁ n₂ : (Comma.idBaseStronglyCartesian p u).Q.obj (Comma.mk V a ψ) ⟶
      (Comma.idBaseStronglyCartesian p u).Q.obj (Comma.mk V b ω))
    (hn₁ : (Comma.pullbackProj p u).map n₁ = 𝟙 V)
    (hn₂ : (Comma.pullbackProj p u).map n₂ = 𝟙 V)
    (hΨn : (pullbackLocalizationMap u hGG).map n₁ = (pullbackLocalizationMap u hGG).map n₂) :
    ∃ T ∈ K V, ∀ ⦃V' : 𝒟⦄ ⦃β : V' ⟶ V⦄, T.arrows β →
      (Comma.idBaseStronglyCartesian p u).Q.map
          (Comma.baseChangeHom p u (Comma.mk V a ψ : Comma (𝟭 𝒟) (p ⋙ u)) β) ≫ n₁ =
        (Comma.idBaseStronglyCartesian p u).Q.map
          (Comma.baseChangeHom p u (Comma.mk V a ψ : Comma (𝟭 𝒟) (p ⋙ u)) β) ≫ n₂ := by
  classical
  have hrcf' := Comma.hasRightCalculusOfFractions_idBaseStronglyCartesian p' u hu
  obtain ⟨c, ψ', σ, hσ, hψ, α₁, α₂, hω₁, hω₂, e₁, e₂⟩ :=
    Comma.exists_common_fraction_fiber p u hu ψ ω n₁ n₂ hn₁ hn₂
  have hΦeq : (Comma.idBaseStronglyCartesian p' u).Q.map
        ((commaMapOver u hGG.comp_eq).map (Comma.idBaseHomTo p u α₁ ψ' ω hω₁)) =
      (Comma.idBaseStronglyCartesian p' u).Q.map
        ((commaMapOver u hGG.comp_eq).map (Comma.idBaseHomTo p u α₂ ψ' ω hω₂)) := by
    have key : (pullbackLocalizationMap u hGG).map
          ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.idBaseHomTo p u α₁ ψ' ω hω₁)) =
        (pullbackLocalizationMap u hGG).map
          ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.idBaseHomTo p u α₂ ψ' ω hω₂)) := by
      rw [← e₁, ← e₂, Functor.map_comp, Functor.map_comp, hΨn]
    rw [pullbackLocalizationMap_map, pullbackLocalizationMap_map] at key
    simpa using key
  rw [MorphismProperty.map_eq_iff_precomp (Comma.idBaseStronglyCartesian p' u).Q
    (Comma.idBaseStronglyCartesian p' u)] at hΦeq
  obtain ⟨Z, r, hr, hrfac⟩ := hΦeq
  obtain ⟨⟨hrl, hrleft⟩, hrsc⟩ := hr
  have hζ : r.right ≫ G.map α₁ = r.right ≫ G.map α₂ :=
    congrArg CommaMorphism.right hrfac
  set W₀ : 𝒞 := p'.obj Z.right with hW₀
  obtain ⟨c₀, γ, δ, hγsc, hδfac, -⟩ :=
    exists_stronglyCartesian_lift_fiber p p' hGG (c := c) r.right hrsc
  set e' : W₀ ⟶ p.obj c := p'.map r.right ≫ eqToHom (Functor.congr_obj hGG.comp_eq c) with he'
  have hGγα : G.map (γ ≫ α₁) = G.map (γ ≫ α₂) := by
    refine (cancel_epi δ.hom).1 ?_
    rw [G.map_comp, G.map_comp, ← Category.assoc, ← Category.assoc, hδfac, hζ]
  have hpγα : p.map (γ ≫ α₁) = p.map (γ ≫ α₂) := by
    have h3 : (G ⋙ p').map (γ ≫ α₁) = (G ⋙ p').map (γ ≫ α₂) := by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [hGγα]
    rw [Functor.congr_hom hGG.comp_eq (γ ≫ α₁), Functor.congr_hom hGG.comp_eq (γ ≫ α₂)] at h3
    exact (cancel_mono _).1 ((cancel_epi _).1 h3)
  have hc₀obj : p.obj c₀.1 = W₀ := c₀.2
  set s : W₀ ⟶ p.obj b := eqToHom hc₀obj.symm ≫ p.map (γ ≫ α₁) with hs
  have hlift₁ : p.IsHomLift s (γ ≫ α₁) :=
    IsHomLift.of_fac' p s (γ ≫ α₁) hc₀obj rfl (by rw [hs]; simp)
  have hlift₂ : p.IsHomLift s (γ ≫ α₂) :=
    IsHomLift.of_fac' p s (γ ≫ α₂) hc₀obj rfl (by rw [hs, ← hpγα]; simp)
  set bF : p.Fiber (p.obj b) := Functor.Fiber.mk rfl with hbF
  set sb : p.Fiber W₀ := Functor.pullbackFiber p bF s with hsb
  set lam : sb.1 ⟶ b := Functor.IsPreFibered.pullbackMap bF.2 s with hlam
  set m₁ : c₀ ⟶ sb := ⟨Functor.IsCartesian.map p s lam (γ ≫ α₁),
    Functor.IsCartesian.map_isHomLift p s lam (γ ≫ α₁)⟩ with hm₁def
  set m₂ : c₀ ⟶ sb := ⟨Functor.IsCartesian.map p s lam (γ ≫ α₂),
    Functor.IsCartesian.map_isHomLift p s lam (γ ≫ α₂)⟩ with hm₂def
  have hm₁ : Functor.Fiber.fiberInclusion.map m₁ ≫ lam = γ ≫ α₁ :=
    Functor.IsCartesian.fac p s lam (γ ≫ α₁)
  have hm₂ : Functor.Fiber.fiberInclusion.map m₂ ≫ lam = γ ≫ α₂ :=
    Functor.IsCartesian.fac p s lam (γ ≫ α₂)
  have hFGm : (Functor.fiberFunctorOfCompEq hGG.comp_eq W₀).map m₁ =
      (Functor.fiberFunctorOfCompEq hGG.comp_eq W₀).map m₂ := by
    refine Functor.Fiber.hom_ext ?_
    have hGlam : p'.IsStronglyCartesian s (G.map lam) :=
      hGG.map_isStronglyCartesian s lam inferInstance
    have hl1 : p'.IsHomLift (𝟙 W₀) (G.map (Functor.Fiber.fiberInclusion.map m₁)) :=
      hGG.map_isHomLift (𝟙 W₀) _
    have hl2 : p'.IsHomLift (𝟙 W₀) (G.map (Functor.Fiber.fiberInclusion.map m₂)) :=
      hGG.map_isHomLift (𝟙 W₀) _
    dsimp only [Functor.fiberInclusion_map_fiberFunctorOfCompEq_map]
    refine Functor.IsStronglyCartesian.ext p' s (G.map lam) (𝟙 W₀) ?_
    rw [← G.map_comp, ← G.map_comp, hm₁, hm₂, hGγα]
  obtain ⟨R₀, hR₀, hR₀eq⟩ := exists_covering_eq hGG J (hinj W₀ c₀ sb) m₁ m₂ hFGm
  set ρ : V ⟶ u.obj W₀ := eqToHom hrl.symm ≫ Z.hom with hρ
  refine ⟨Sieve.pullback ρ (Sieve.functorPushforward u R₀),
    mem_pullback_functorPushforward u J K hR₀ ρ, ?_⟩
  intro V' β hβ
  obtain ⟨W₁, k, χ, hk, hkfac⟩ :=
    exists_factorisation_of_mem_pullback_functorPushforward u ρ hβ
  set ck : p.Fiber W₁ := Functor.pullbackFiber p c₀ k with hck
  set γk : ck.1 ⟶ c := Functor.IsPreFibered.pullbackMap c₀.2 k ≫ γ with hγk
  have hbase : Functor.IsPreFibered.pullbackMap c₀.2 k ≫ Functor.Fiber.fiberInclusion.map m₁ =
      Functor.IsPreFibered.pullbackMap c₀.2 k ≫ Functor.Fiber.fiberInclusion.map m₂ := by
    have f1 := Functor.pullbackFiberHom_fac m₁ k
    have f2 := Functor.pullbackFiberHom_fac m₂ k
    rw [hR₀eq k hk] at f1
    exact f1.symm.trans f2
  have hkey : γk ≫ α₁ = γk ≫ α₂ := by
    have h1 : Functor.IsPreFibered.pullbackMap c₀.2 k ≫
        (Functor.Fiber.fiberInclusion.map m₁ ≫ lam) =
        Functor.IsPreFibered.pullbackMap c₀.2 k ≫
          (Functor.Fiber.fiberInclusion.map m₂ ≫ lam) := by
      rw [← Category.assoc, ← Category.assoc, hbase]
    rw [hm₁, hm₂] at h1
    rw [hγk]
    simpa using h1
  have hγksc : stronglyCartesianOver p γk :=
    stronglyCartesianOver_comp_of_isStronglyCartesian p
      (inferInstance : p.IsStronglyCartesian k (Functor.IsPreFibered.pullbackMap c₀.2 k)) hγsc
  set χ' : V' ⟶ u.obj (p.obj ck.1) := χ ≫ eqToHom (congrArg u.obj ck.2.symm) with hχ'
  have hrw := r.w
  rw [commaMapOver_obj_hom u p p' hGG.comp_eq (Comma.mk V c ψ'), hrleft] at hrw
  have hρe : ρ ≫ u.map e' = ψ' := by
    rw [hρ, he', Functor.map_comp, Category.assoc, ← Category.assoc Z.hom]
    have h : Z.hom ≫ u.map (p'.map r.right) = eqToHom hrl ≫ ψ' ≫
        eqToHom (comp_obj_eq u p p' hGG.comp_eq c) := by simpa using hrw.symm
    rw [h]
    simp [eqToHom_map]
  have hτw : χ' ≫ (p ⋙ u).map γk = β ≫ ψ' := by
    have hmapk : p.map (Functor.IsPreFibered.pullbackMap c₀.2 k) =
        eqToHom ck.2 ≫ k ≫ eqToHom hc₀obj.symm := IsHomLift.fac' p k _
    have hmapγ : p.map γ = eqToHom hc₀obj ≫ e' ≫ eqToHom rfl := IsHomLift.fac' p e' γ
    rw [hχ', hγk, Functor.comp_map, p.map_comp, hmapk, hmapγ]
    simp only [eqToHom_map, Functor.map_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rw [← Category.assoc, ← hkfac, Category.assoc, hρe]
  set τ := Comma.commaHomMk p u γk β χ' ψ' hτw with hτdef
  have hff : τ ≫ Comma.idBaseHomTo p u α₁ ψ' ω hω₁ =
      τ ≫ Comma.idBaseHomTo p u α₂ ψ' ω hω₂ := by
    refine Comma.hom_ext _ _ rfl ?_
    rw [hτdef]
    simpa using hkey
  have h24 : (Comma.idBaseStronglyCartesian p u).Q.map
        (τ ≫ Comma.idBaseHomTo p u σ ψ' ψ hψ) ≫ n₁ =
      (Comma.idBaseStronglyCartesian p u).Q.map
        (τ ≫ Comma.idBaseHomTo p u σ ψ' ψ hψ) ≫ n₂ := by
    rw [Functor.map_comp, Category.assoc, Category.assoc, e₁, e₂, ← Functor.map_comp,
      ← Functor.map_comp, hff]
  have hψ'' : χ' ≫ (p ⋙ u).map (γk ≫ σ) = β ≫ ψ := by
    rw [Functor.map_comp, ← Category.assoc, hτw, Category.assoc, hψ]
  have hfac : τ ≫ Comma.idBaseHomTo p u σ ψ' ψ hψ =
      Comma.idBaseHomTo p u (γk ≫ σ) χ' (β ≫ ψ) hψ'' ≫
        Comma.baseChangeHom p u (Comma.mk V a ψ : Comma (𝟭 𝒟) (p ⋙ u)) β := by
    refine Comma.hom_ext _ _ ?_ ?_
    · rw [hτdef]; simp
    · rw [hτdef]; simp
  have hiso : IsIso ((Comma.idBaseStronglyCartesian p u).Q.map
      (Comma.idBaseHomTo p u (γk ≫ σ) χ' (β ≫ ψ) hψ'')) :=
    Localization.inverts _ (Comma.idBaseStronglyCartesian p u) _
      (Comma.idBaseStronglyCartesian_idBaseHomTo p u
        (stronglyCartesianOver_comp p γk σ hγksc hσ) χ' (β ≫ ψ) hψ'')
  refine (cancel_epi ((Comma.idBaseStronglyCartesian p u).Q.map
    (Comma.idBaseHomTo p u (γk ≫ σ) χ' (β ≫ ψ) hψ''))).1 ?_
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← hfac]
  exact h24

/-- **The local content of Stacks 04WR, surjectivity half.** A morphism `Ψ A ⟶ Ψ B` of `u_p 𝒮'`
becomes, after precomposition with a morphism lying over a member of a `K`-covering sieve of the
base of `A`, the image under `Ψ` of a morphism of `u_p 𝒮`. -/
theorem exists_covering_lift_pullbackLocalizationMap
    [p.IsFibered] [p'.IsFibered] [HasNonemptyFiniteLimits 𝒞]
    (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟) [u.IsContinuous J K]
    (hu : ∀ (J' : Type) [SmallCategory J'] [FinCategory J'] [Nonempty J'],
      Limits.PreservesLimitsOfShape J' u)
    (hGG : p.IsFibredOneMorphism p' G)
    (hmor : ∀ (U : 𝒞) (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hGG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over U) (hGG.morPresheafMap x y))
    {A B : Comma.pullbackLocalization p u}
    (θ : (pullbackLocalizationMap u hGG).obj A ⟶ (pullbackLocalizationMap u hGG).obj B) :
    ∃ S ∈ K ((Comma.pullbackProj p u).obj A), ∀ ⦃w : Comma.pullbackLocalization p u⦄
      (ρ : w ⟶ A), S.arrows ((Comma.pullbackProj p u).map ρ) →
        ∃ f : w ⟶ B, (pullbackLocalizationMap u hGG).map ρ ≫ θ =
          (pullbackLocalizationMap u hGG).map f := by
  classical
  obtain ⟨X, rfl⟩ : ∃ X, (Comma.idBaseStronglyCartesian p u).Q.obj X = A :=
    ⟨_, (Localization.Construction.objEquiv (Comma.idBaseStronglyCartesian p u)).apply_symm_apply A⟩
  obtain ⟨Y, rfl⟩ : ∃ Y, (Comma.idBaseStronglyCartesian p u).Q.obj Y = B :=
    ⟨_, (Localization.Construction.objEquiv (Comma.idBaseStronglyCartesian p u)).apply_symm_apply B⟩
  obtain ⟨V, a, ψ⟩ := X
  set θ' : (Comma.idBaseStronglyCartesian p' u).Q.obj
        ((commaMapOver u hGG.comp_eq).obj (Comma.mk V a ψ)) ⟶
      (Comma.idBaseStronglyCartesian p' u).Q.obj ((commaMapOver u hGG.comp_eq).obj Y) :=
    eqToHom (pullbackLocalizationMap_obj u hGG (Comma.mk V a ψ)).symm ≫ θ ≫
      eqToHom (pullbackLocalizationMap_obj u hGG Y) with hθ'
  obtain ⟨z, ρ₀, ζ, hζsc, hζψ, f', hf'⟩ := Comma.exists_fraction_gen p' u hu θ'
  obtain ⟨c₀, γ, δ, hγsc, hδfac, hδinvlift⟩ :=
    exists_stronglyCartesian_lift_fiber p p' hGG ζ hζsc
  set e' : p'.obj z ⟶ p.obj a := p'.map ζ ≫ eqToHom (Functor.congr_obj hGG.comp_eq a) with he'
  obtain ⟨R, hR, hlift⟩ := exists_covering_lift_hom hGG J hmor (δ.inv ≫ f'.right)
  set ρ'' : V ⟶ u.obj (p.obj c₀.1) := ρ₀ ≫ eqToHom (congrArg u.obj c₀.2.symm) with hρ''
  refine ⟨Sieve.pullback ρ'' (Sieve.functorPushforward u R),
    mem_pullback_functorPushforward u J K hR ρ'', ?_⟩
  intro w ρ hρ
  set V₁ : 𝒟 := (Comma.pullbackProj p u).obj w with hV₁
  set β : V₁ ⟶ V := (Comma.pullbackProj p u).map ρ with hβdef
  obtain ⟨W₁, k, χ, hk, hkfac⟩ :=
    exists_factorisation_of_mem_pullback_functorPushforward u ρ'' hρ
  have hbchsc := Comma.isStronglyCartesian_Q_baseChangeHom p u hu (Comma.mk V a ψ) β
  have hρlift : (Comma.pullbackProj p u).IsHomLift β ρ := IsHomLift.map _ _
  have hone : β = 𝟙 _ ≫ β := by simp
  set ρ' := Functor.IsStronglyCartesian.map (Comma.pullbackProj p u) β
    ((Comma.idBaseStronglyCartesian p u).Q.map
      (Comma.baseChangeHom p u (Comma.mk V a ψ : Comma (𝟭 𝒟) (p ⋙ u)) β)) hone ρ with hρ'
  have hρ'fac : ρ' ≫ (Comma.idBaseStronglyCartesian p u).Q.map
      (Comma.baseChangeHom p u (Comma.mk V a ψ : Comma (𝟭 𝒟) (p ⋙ u)) β) = ρ :=
    Functor.IsStronglyCartesian.fac (Comma.pullbackProj p u) _ _ hone ρ
  set ck : p.Fiber W₁ :=
    Functor.pullbackFiber p (Functor.Fiber.mk (rfl : p.obj c₀.1 = p.obj c₀.1)) k with hck
  set πk : ck.1 ⟶ c₀.1 :=
    Functor.IsPreFibered.pullbackMap (Functor.Fiber.mk (rfl : p.obj c₀.1 = p.obj c₀.1)).2 k
    with hπk
  obtain ⟨wmor, hw⟩ := hlift k hk
  set γk : ck.1 ⟶ a := πk ≫ γ with hγk
  have hγksc : stronglyCartesianOver p γk :=
    stronglyCartesianOver_comp_of_isStronglyCartesian p
      (PullbackAdjunction.isStronglyCartesian_comp_eqToHom c₀.2 k πk inferInstance) hγsc
  set χ' : V₁ ⟶ u.obj (p.obj ck.1) := χ ≫ eqToHom (congrArg u.obj ck.2.symm) with hχ'
  have hπkmap : p.map πk = eqToHom ck.2 ≫ k := by simpa using IsHomLift.fac' p k πk
  have hγmap : p.map γ = eqToHom c₀.2 ≫ e' := by simpa using IsHomLift.fac' p e' γ
  have hχ'πk : χ' ≫ (p ⋙ u).map πk = χ ≫ u.map k := by
    rw [hχ', Functor.comp_map, hπkmap]
    simp [eqToHom_map]
  have hβρ₀ : β ≫ ρ₀ = χ ≫ u.map k ≫ eqToHom (congrArg u.obj c₀.2) := by
    rw [hρ'', ← Category.assoc] at hkfac
    rw [← Category.assoc, ← hkfac]
    simp
  have hρe : ρ₀ ≫ u.map e' = ψ := by
    have h0 := hζψ
    rw [commaMapOver_obj_hom u p p' hGG.comp_eq (Comma.mk V a ψ)] at h0
    rw [he', Functor.map_comp, ← Category.assoc]
    dsimp only [Comma.map_obj_left, Functor.id_obj, Comma.map_obj_right]
    rw [show ρ₀ ≫ u.map (p'.map ζ) = ψ ≫ eqToHom (comp_obj_eq u p p' hGG.comp_eq a) from h0]
    simp [eqToHom_map]
  have hτw : χ' ≫ (p ⋙ u).map γk = β ≫ ψ := by
    have hRHS : β ≫ ψ = (χ ≫ u.map k ≫ eqToHom (congrArg u.obj c₀.2)) ≫ u.map e' := by
      rw [← hβρ₀, Category.assoc, hρe]
    rw [hRHS, hγk, show (p ⋙ u).map (πk ≫ γ) = (p ⋙ u).map πk ≫ (p ⋙ u).map γ from
      (p ⋙ u).map_comp _ _, ← Category.assoc, hχ'πk]
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [hγmap]
    simp [eqToHom_map]
  have hηw : (𝟭 𝒟).map β ≫ (Comma.mk _ z ρ₀ : Comma (𝟭 𝒟) (p' ⋙ u)).hom =
      ((commaMapOver u hGG.comp_eq).obj
          (Comma.mk V₁ ck.1 χ' : Comma (𝟭 𝒟) (p ⋙ u))).hom ≫
        (p' ⋙ u).map (G.map πk ≫ δ.inv) := by
    have := hδinvlift
    rw [commaMapOver_obj_hom u p p' hGG.comp_eq (Comma.mk V₁ ck.1 χ'), Functor.map_comp,
      ← Category.assoc, commaCond_map u p p' hGG.comp_eq πk χ', hχ'πk]
    dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Comma.map_obj_left,
        Functor.comp_map]
    rw [IsHomLift.fac' p' (𝟙 (p'.obj z)) δ.inv]
    dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, eqToHom_refl]
    rw [hβρ₀]
    simp [eqToHom_map]
  set η : (commaMapOver u hGG.comp_eq).obj (Comma.mk V₁ ck.1 χ' : Comma (𝟭 𝒟) (p ⋙ u)) ⟶
      (Comma.mk _ z ρ₀ : Comma (𝟭 𝒟) (p' ⋙ u)) :=
    { left := β, right := G.map πk ≫ δ.inv, w := hηw } with hη
  have hf₀w : χ' ≫ (p ⋙ u).map wmor = (β ≫ f'.left) ≫ Y.hom := by
    have hcomp := (η ≫ f').w
    rw [commaMapOver_obj_hom u p p' hGG.comp_eq Y,
      commaMapOver_obj_hom u p p' hGG.comp_eq (Comma.mk V₁ ck.1 χ')] at hcomp
    have hright : (η ≫ f').right = G.map wmor := by
      rw [Comma.comp_right, hη]
      dsimp only
      rw [Category.assoc]
      exact hw
    have hηleft : η.left = β := by rw [hη]
    rw [hright, commaCond_map u p p' hGG.comp_eq wmor χ'] at hcomp
    refine (cancel_mono (eqToHom (comp_obj_eq u p p' hGG.comp_eq Y.right))).1 ?_
    simpa [hηleft] using hcomp.symm
  set f₀ := Comma.commaHomMk p u wmor (β ≫ f'.left) χ' Y.hom hf₀w with hf₀
  set ν := Comma.idBaseHomTo p u γk χ' (β ≫ ψ) hτw with hν
  have hνmem : Comma.idBaseStronglyCartesian p u ν :=
    Comma.idBaseStronglyCartesian_idBaseHomTo p u hγksc χ' (β ≫ ψ) hτw
  have hνiso : IsIso ((Comma.idBaseStronglyCartesian p u).Q.map ν) :=
    Localization.inverts _ (Comma.idBaseStronglyCartesian p u) _ hνmem
  have hτ : ν ≫ Comma.baseChangeHom p u (Comma.mk V a ψ : Comma (𝟭 𝒟) (p ⋙ u)) β =
      Comma.commaHomMk p u γk β χ' ψ hτw := by
    refine Comma.hom_ext _ _ ?_ ?_
    · rw [hν]; simp
    · rw [hν]; simp
  have hi : (commaMapOver u hGG.comp_eq).map (Comma.commaHomMk p u γk β χ' ψ hτw) =
      η ≫ Comma.idBaseHomTo p' u ζ ρ₀
        ((commaMapOver u hGG.comp_eq).obj (Comma.mk V a ψ)).hom hζψ := by
    refine Comma.hom_ext _ _ ?_ ?_
    · rw [hη]; simp
    · rw [hη]
      dsimp only [Comma.map_obj_right, Comma.map_map_right, Comma.commaHomMk_right, Functor.id_obj,
          Comma.map_obj_left, Comma.map_obj_hom, Functor.comp_obj, NatTrans.id_app, Functor.id_map,
          Comma.comp_right, Comma.idBaseHomTo_right]
      rw [hγk, G.map_comp, Category.assoc, ← hδfac, Iso.inv_hom_id_assoc]
  have hii : (commaMapOver u hGG.comp_eq).map f₀ = η ≫ f' := by
    refine Comma.hom_ext _ _ ?_ ?_
    · rw [hη, hf₀]; simp
    · rw [hη, hf₀]
      dsimp only [Comma.map_obj_right, Comma.map_obj_left, Functor.id_obj, Comma.map_map_right,
          Comma.commaHomMk_right, Comma.comp_right]
      rw [Category.assoc]
      exact hw.symm
  refine ⟨ρ' ≫ inv ((Comma.idBaseStronglyCartesian p u).Q.map ν) ≫
    (Comma.idBaseStronglyCartesian p u).Q.map f₀, ?_⟩
  have hmain : (pullbackLocalizationMap u hGG).map
        ((Comma.idBaseStronglyCartesian p u).Q.map
          (ν ≫ Comma.baseChangeHom p u (Comma.mk V a ψ : Comma (𝟭 𝒟) (p ⋙ u)) β)) ≫ θ =
      (pullbackLocalizationMap u hGG).map
        ((Comma.idBaseStronglyCartesian p u).Q.map f₀) := by
    rw [pullbackLocalizationMap_map, pullbackLocalizationMap_map, hτ, hi, Functor.map_comp,
      Category.assoc, Category.assoc, Category.assoc]
    rw [show eqToHom (pullbackLocalizationMap_obj u hGG (Comma.mk V a ψ)).symm ≫ θ =
        θ' ≫ eqToHom (pullbackLocalizationMap_obj u hGG Y).symm by
      rw [hθ']; simp]
    rw [← Category.assoc ((Comma.idBaseStronglyCartesian p' u).Q.map
      (Comma.idBaseHomTo p' u ζ ρ₀ _ hζψ)), hf',
      ← Category.assoc ((Comma.idBaseStronglyCartesian p' u).Q.map η), ← Functor.map_comp, ← hii]
  have hfinal : (pullbackLocalizationMap u hGG).map
        ((Comma.idBaseStronglyCartesian p u).Q.map
          (Comma.baseChangeHom p u (Comma.mk V a ψ : Comma (𝟭 𝒟) (p ⋙ u)) β)) ≫ θ =
      (pullbackLocalizationMap u hGG).map
          (inv ((Comma.idBaseStronglyCartesian p u).Q.map ν)) ≫
        (pullbackLocalizationMap u hGG).map
          ((Comma.idBaseStronglyCartesian p u).Q.map f₀) := by
    have := hνiso
    refine (cancel_epi ((pullbackLocalizationMap u hGG).map
      ((Comma.idBaseStronglyCartesian p u).Q.map ν))).1 ?_
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hmain, ← Category.assoc,
      ← Functor.map_comp, IsIso.hom_inv_id, Functor.map_id, Category.id_comp]
  rw [← hρ'fac, Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc, hfinal]

end CoreInjective

end CategoryTheory

end
