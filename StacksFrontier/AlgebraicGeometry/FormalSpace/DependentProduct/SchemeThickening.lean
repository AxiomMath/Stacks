module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Universal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
import StacksFrontier.AlgebraicGeometry.FormalSpace.StageThickening

/-!
# The dependent product along a thickening of objects of the site

Let `S` be a scheme contained in a big fppf site `B`, let `k : T₀ ⟶ T` be a morphism of the big
fppf site over `S` whose underlying morphism of schemes is a thickening, and let `e₀ : L₀ ⟶ T₀`
be étale. Then the dependent product of `h_{L₀} ⟶ h_{T₀}` along `h_k`
(`AlgebraicGeometry.FormalSpace.DependentProduct.liftAlong`) is represented by an object `L`
étale over `T` whose base change along `k` is `L₀`: it is the étale lift of `L₀` across the
thickening (Stacks 039R).

## Main results

* `existsUnique_lift_of_etale_of_universalHomeomorphism`: a morphism into an étale object of the
  site, prescribed along a universal homeomorphism, extends uniquely.
* `AlgebraicGeometry.FormalSpace.DependentProduct.exists_iso_liftAlong_of_isThickening`: the
  representability statement above.

## Implementation notes

A section of the dependent product over `T'` is a morphism `a : T' ⟶ T` together with a rule on
the points of `T' ×_T T₀`; that rule is determined by its value at the universal point, the
projection of the fibre product `P = T' ×_T T₀` itself. Its value there is a morphism `P ⟶ L₀`,
hence a morphism `P ⟶ L` over `T`, and since `P ⟶ T'` is a thickening it extends uniquely to a
morphism `T' ⟶ L` over `T`, by the section form of the topological invariance of the étale
site, `Stacks.Etale.existsUnique_section_of_universalHomeomorphism`.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the big fppf site commutes with the structure morphisms to `S`. -/
private theorem map_comp_inclusion_map_hom {X Y : BigFppfOver B S hS} (f : X ⟶ Y) :
    (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom := by
  rw [← Over.w f]
  rfl

/-- **A morphism into an étale object of the site, prescribed along a universal homeomorphism,
extends uniquely.** Let `q : L ⟶ T` be a morphism of the big fppf site over `S` whose underlying
morphism of schemes is étale, let `a : T' ⟶ T` be a morphism and let `ι : P ⟶ T'` be a morphism
whose underlying morphism of schemes is a universal homeomorphism. Every `β : P ⟶ L` with
`β ≫ q = ι ≫ a` is `ι ≫ σ` for a unique `σ : T' ⟶ L` over `T`.

This is `Stacks.Etale.existsUnique_section_of_universalHomeomorphism` for the base change of `q`
along `a`, read in the big fppf site. -/
theorem existsUnique_lift_of_etale_of_universalHomeomorphism
    {P T' L T : BigFppfOver B S hS} (a : T' ⟶ T) (q : L ⟶ T)
    (hq : Etale ((BigFppfOver.toScheme B S hS).map q)) (ι : P ⟶ T')
    (hι : UniversalHomeomorphism ((BigFppfOver.toScheme B S hS).map ι)) (β : P ⟶ L)
    (hβ : β ≫ q = ι ≫ a) :
    ∃! σ : T' ⟶ L, σ ≫ q = a ∧ ι ≫ σ = β := by
  set F := BigFppfOver.toScheme B S hS
  have hβ' : F.map β ≫ F.map q = F.map ι ≫ F.map a := by
    rw [← F.map_comp, ← F.map_comp, hβ]
  -- the base change of `q` along `a`, and the section of it over `P` determined by `β`
  have : Etale (pullback.snd (F.map q) (F.map a)) := inferInstance
  have hσ' : pullback.lift (F.map β) (F.map ι) hβ' ≫ pullback.snd (F.map q) (F.map a) =
      F.map ι := pullback.lift_snd _ _ _
  obtain ⟨σs, ⟨hσs₁, hσs₂⟩, hσsu⟩ :=
    Stacks.Etale.existsUnique_section_of_universalHomeomorphism (F.map ι)
      (pullback.snd (F.map q) (F.map a)) (pullback.lift (F.map β) (F.map ι) hβ') hσ'
  -- the scheme morphism `T' ⟶ L`
  set σ₀ := σs ≫ pullback.fst (F.map q) (F.map a) with hσ₀
  have hσ₀q : σ₀ ≫ F.map q = F.map a := by
    rw [hσ₀, Category.assoc, pullback.condition, ← Category.assoc, hσs₁, Category.id_comp]
  have hσ₀S : σ₀ ≫ B.inclusion.map L.hom = B.inclusion.map T'.hom := by
    rw [← map_comp_inclusion_map_hom q, ← Category.assoc, hσ₀q, map_comp_inclusion_map_hom a]
  obtain ⟨σ, hσ⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS σ₀ hσ₀S
  refine ⟨σ, ⟨F.map_injective (by rw [F.map_comp, hσ, hσ₀q]), F.map_injective ?_⟩, ?_⟩
  · rw [F.map_comp, hσ, hσ₀, ← Category.assoc, hσs₂, pullback.lift_fst]
  · rintro τ ⟨hτ₁, hτ₂⟩
    apply F.map_injective
    rw [hσ]
    have hτq : F.map τ ≫ F.map q = F.map a := by rw [← F.map_comp, hτ₁]
    have hτs := hσsu (pullback.lift (F.map τ) (𝟙 _) (by rw [hτq, Category.id_comp]))
      ⟨pullback.lift_snd _ _ _, by
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← F.map_comp, hτ₂]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]⟩
    rw [hσ₀, ← hτs, pullback.lift_fst]

/-! ### Sections of the universe-lifted Yoneda sheaf -/

/-- A morphism of universe-lifted representable sheaves acts on sections by postcomposition. -/
theorem uliftYoneda_map_app_up {X Y T : BigFppfOver B S hS} (f : X ⟶ Y) (x : T ⟶ X) :
    ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map f).hom.app (Opposite.op T)
      (ULift.up x) = ULift.up (x ≫ f) :=
  rfl

/-- Restriction of a section of a universe-lifted representable sheaf is precomposition. -/
theorem uliftYoneda_obj_map_up {X T T' : BigFppfOver B S hS} (r : T' ⟶ T) (x : T ⟶ X) :
    ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj X).obj.map r.op (ULift.up x) =
      ULift.up (r ≫ x) :=
  rfl

/-- **A cartesian square of the big fppf site is cartesian on the sections of the
universe-lifted representable sheaves.** -/
theorem isSectionwisePullback_uliftYoneda {A C D E : BigFppfOver B S hS} {t : A ⟶ C}
    {l : A ⟶ D} {r : C ⟶ E} {b : D ⟶ E} (h : IsPullback t l r b) :
    IsSectionwisePullback B S hS ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map t)
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map l)
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map r)
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map b) := by
  rintro T ⟨c⟩ ⟨d⟩ hcd
  have hcd' : c ≫ r = d ≫ b := congrArg ULift.down hcd
  refine ⟨ULift.up (h.lift c d hcd'), ⟨congrArg ULift.up (h.lift_fst c d hcd'),
    congrArg ULift.up (h.lift_snd c d hcd')⟩, ?_⟩
  rintro ⟨m⟩ ⟨hm₁, hm₂⟩
  exact congrArg ULift.up (h.hom_ext ((congrArg ULift.down hm₁).trans (h.lift_fst _ _ _).symm)
    ((congrArg ULift.down hm₂).trans (h.lift_snd _ _ _).symm))

/-! ### The dependent product along a thickening -/

section Thickening

variable {T₀ T L₀ L : BigFppfOver B S hS} {k : T₀ ⟶ T} {q₀ : L₀ ⟶ T₀} {q : L ⟶ T}
  {c₀ : L₀ ⟶ L}

/-- The base change of a thickening of the site along a morphism of the site is a universal
homeomorphism. -/
theorem universalHomeomorphism_pullback_fst_of_isThickening (hk : Stacks.Thickenings.IsThickening
    ((BigFppfOver.toScheme B S hS).map k)) {T' : BigFppfOver B S hS} (a : T' ⟶ T) :
    haveI := hasPullbacks_bigFppfOver B S hS
    UniversalHomeomorphism ((BigFppfOver.toScheme B S hS).map (pullback.fst a k)) := by
  have := hasPullbacks_bigFppfOver B S hS
  have := preservesPullbacks_bigFppfOverToScheme B S hS
  have := isThickening_isStableUnderBaseChange.{u}
  have hth : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (pullback.fst a k)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback a k).flip.map (BigFppfOver.toScheme B S hS)) hk
  have := hth.1
  exact Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective _ hth.2

variable (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
  (hq : Etale ((BigFppfOver.toScheme B S hS).map q)) (hsq : IsPullback c₀ q₀ q k)

include hk hq in
/-- The comparison morphism `h_L ⟶ Π_{h_k} h_{L₀}` is injective on sections. -/
private theorem injective_liftAlongMk_app (T' : BigFppfOver B S hS) :
    Function.Injective ((liftAlongMk (isSectionwisePullback_uliftYoneda hsq)).hom.app
      (Opposite.op T')) := by
  have := hasPullbacks_bigFppfOver B S hS
  set hex := isSectionwisePullback_uliftYoneda hsq
  -- two morphisms `T' ⟶ L` with the same section agree on `T' ×_T T₀`
  rintro ⟨z₁⟩ ⟨z₂⟩ hz
  have hz' : mkApp hex T' (ULift.up z₁) = mkApp hex T' (ULift.up z₂) := hz
  have hb : z₁ ≫ q = z₂ ≫ q := congrArg ULift.down (congrArg LiftAlong.base hz')
  set π₁ := pullback.fst (z₁ ≫ q) k
  set π₂ := pullback.snd (z₁ ≫ q) k
  have h₁ : ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map k).hom.app (Opposite.op _)
        (ULift.up π₂) =
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T).obj.map π₁.op
        (((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map q).hom.app (Opposite.op T')
          (ULift.up z₁)) :=
    congrArg ULift.up (pullback.condition (f := z₁ ≫ q) (g := k)).symm
  have h₂ : ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map k).hom.app (Opposite.op _)
        (ULift.up π₂) =
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T).obj.map π₁.op
        (((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map q).hom.app (Opposite.op T')
          (ULift.up z₂)) := by
    rw [h₁]
    exact congrArg ULift.up (congrArg (π₁ ≫ ·) hb)
  have hr := LiftAlong.lift_congr hz' rfl rfl h₁ h₂
  have e₁ := mkRule_fst hex (ULift.up z₁) _ π₁ (ULift.up π₂) h₁
  have e₂ := mkRule_fst hex (ULift.up z₂) _ π₁ (ULift.up π₂) h₂
  change mkRule hex (ULift.up z₁) _ π₁ (ULift.up π₂) h₁ =
    mkRule hex (ULift.up z₂) _ π₁ (ULift.up π₂) h₂ at hr
  rw [hr] at e₁
  have hπ : π₁ ≫ z₁ = π₁ ≫ z₂ := congrArg ULift.down (e₁.symm.trans e₂)
  obtain ⟨σ, -, hσu⟩ := existsUnique_lift_of_etale_of_universalHomeomorphism (z₁ ≫ q) q hq π₁
    (universalHomeomorphism_pullback_fst_of_isThickening hk _) (π₁ ≫ z₁) (by simp)
  exact congrArg ULift.up ((hσu z₁ ⟨rfl, rfl⟩).trans (hσu z₂ ⟨hb.symm, hπ.symm⟩).symm)

include hk hq in
/-- The comparison morphism `h_L ⟶ Π_{h_k} h_{L₀}` is surjective on sections: the rule at the
universal point extends across the thickening. -/
private theorem surjective_liftAlongMk_app (T' : BigFppfOver B S hS) :
    Function.Surjective ((liftAlongMk (isSectionwisePullback_uliftYoneda hsq)).hom.app
      (Opposite.op T')) := by
  have := hasPullbacks_bigFppfOver B S hS
  set hex := isSectionwisePullback_uliftYoneda hsq
  intro ξ
  set a : T' ⟶ T := ξ.base.down
  set π₁ := pullback.fst a k
  set π₂ := pullback.snd a k
  have hw₀ : ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map k).hom.app (Opposite.op _)
        (ULift.up π₂) =
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T).obj.map π₁.op ξ.base :=
    congrArg ULift.up (pullback.condition (f := a) (g := k)).symm
  set l := ξ.lift _ π₁ (ULift.up π₂) hw₀
  have hlq : l.down ≫ q₀ = π₂ := congrArg ULift.down (ξ.lift_proj _ π₁ (ULift.up π₂) hw₀)
  have hβ : (l.down ≫ c₀) ≫ q = π₁ ≫ a := by
    rw [Category.assoc, hsq.w, ← Category.assoc, hlq, pullback.condition]
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, -⟩ := existsUnique_lift_of_etale_of_universalHomeomorphism a q hq π₁
    (universalHomeomorphism_pullback_fst_of_isThickening hk _) (l.down ≫ c₀) hβ
  refine ⟨ULift.up σ, ?_⟩
  show mkApp hex T' (ULift.up σ) = ξ
  refine LiftAlong.ext _ _ (congrArg ULift.up hσ₁) fun T'' t w h h' ↦ ?_
  show mkRule hex (ULift.up σ) T'' t w h = ξ.lift T'' t w h'
  refine (bcPoint_eq hex _ w _ (ξ.lift T'' t w h') ?_ (ξ.lift_proj T'' t w h')).symm
  -- the point `(t, w)` factors through the universal point
  have hu : t ≫ a = w.down ≫ k := (congrArg ULift.down h').symm
  set u : T'' ⟶ pullback a k := pullback.lift t w.down hu
  have h'' : ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map k).hom.app
      (Opposite.op T'')
      (((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T₀).obj.map u.op (ULift.up π₂)) =
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T).obj.map (u ≫ π₁).op ξ.base :=
    congrArg ULift.up (show (u ≫ π₂) ≫ k = (u ≫ π₁) ≫ a by
      rw [Category.assoc, Category.assoc, pullback.condition])
  have hm := ξ.lift_map _ T'' u π₁ (ULift.up π₂) hw₀ h''
  have hm' : ξ.lift T'' (u ≫ π₁)
      (((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T₀).obj.map u.op (ULift.up π₂))
      h'' = ξ.lift T'' t w h' :=
    LiftAlong.lift_congr rfl (pullback.lift_fst _ _ _)
      (show ULift.up (u ≫ π₂) = w from congrArg ULift.up (pullback.lift_snd _ _ _)) _ _
  rw [← hm', ← hm]
  refine congrArg ULift.up ?_
  show (u ≫ l.down) ≫ c₀ = t ≫ σ
  rw [Category.assoc, ← hσ₂, ← Category.assoc, pullback.lift_fst]

include hk hq in
/-- **The comparison morphism `h_L ⟶ Π_{h_k} h_{L₀}` is bijective on sections.** -/
theorem bijective_liftAlongMk_app (T' : BigFppfOver B S hS) :
    Function.Bijective ((liftAlongMk (isSectionwisePullback_uliftYoneda hsq)).hom.app
      (Opposite.op T')) :=
  ⟨injective_liftAlongMk_app hk hq hsq T', surjective_liftAlongMk_app hk hq hsq T'⟩

include hk hq in
/-- The comparison morphism `h_L ⟶ Π_{h_k} h_{L₀}` is an isomorphism. -/
theorem isIso_liftAlongMk : IsIso (liftAlongMk (isSectionwisePullback_uliftYoneda hsq)) := by
  have : IsIso ((sheafToPresheaf _ _).map
      (liftAlongMk (isSectionwisePullback_uliftYoneda hsq))) := by
    refine (NatTrans.isIso_iff_isIso_app _).mpr fun T' ↦ ?_
    exact (isIso_iff_bijective _).mpr (bijective_liftAlongMk_app hk hq hsq T'.unop)
  exact isIso_of_fully_faithful (sheafToPresheaf _ _) _

end Thickening

/-- **The dependent product of an étale object along a thickening of the site is represented
by its étale lift.** Let `k : T₀ ⟶ T` be a morphism of the big fppf site over `S` whose
underlying morphism of schemes is a thickening and let `q₀ : L₀ ⟶ T₀` be étale. Then there is
an object `L` étale over `T` whose base change along `k` is `L₀`, affine as soon as `L₀` is, and
the universe-lifted representable sheaf of `L` is the dependent product of `h_{q₀}` along
`h_k`, over `h_T`.

The lift is Stacks 039R for objects of a big fppf site,
`Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective`, its
affineness is Stacks 06AD, and the identification with the dependent product is
`AlgebraicGeometry.FormalSpace.DependentProduct.isIso_liftAlongMk`. -/
theorem exists_iso_liftAlong_of_isThickening {T₀ T L₀ : BigFppfOver B S hS} (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    (q₀ : L₀ ⟶ T₀) (hq₀ : Etale ((BigFppfOver.toScheme B S hS).map q₀)) :
    ∃ (L : BigFppfOver B S hS) (q : L ⟶ T) (c₀ : L₀ ⟶ L),
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧ IsPullback c₀ q₀ q k ∧
      (IsAffine ((BigFppfOver.toScheme B S hS).obj L₀) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj L)) ∧
      ∃ φ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj L ≅
          liftAlong B S hS ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map k)
            ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map q₀),
        φ.hom ≫ liftAlongBase B S hS _ _ =
          (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map q := by
  set F := BigFppfOver.toScheme B S hS
  have : IsClosedImmersion (F.map k) := hk.1
  obtain ⟨L, q, hq, e, he⟩ :=
    Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective
      B S hS k hk.2 L₀ (F.map q₀) hq₀
  -- the morphism `L₀ ⟶ L` of the site
  have hc₀S : (e.inv ≫ pullback.fst (F.map q) (F.map k)) ≫ B.inclusion.map L.hom =
      B.inclusion.map L₀.hom := by
    have hsnd : e.inv ≫ pullback.snd (F.map q) (F.map k) = F.map q₀ := by
      rw [← he, Iso.inv_hom_id_assoc]
    rw [← map_comp_inclusion_map_hom q, Category.assoc, ← Category.assoc (pullback.fst _ _),
      pullback.condition, Category.assoc, ← Category.assoc e.inv, hsnd,
      map_comp_inclusion_map_hom k, map_comp_inclusion_map_hom q₀]
  obtain ⟨c₀, hc₀⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS _ hc₀S
  -- the square is cartesian in the site, being cartesian after `F`
  have hsqF : IsPullback (F.map c₀) (F.map q₀) (F.map q) (F.map k) := by
    rw [hc₀]
    refine (IsPullback.of_hasPullback (F.map q) (F.map k)).of_iso e (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · exact he.symm.trans (by simp)
    · simp
    · simp
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have hsq : IsPullback c₀ q₀ q k := IsPullback.of_map_of_faithful F hsqF
  refine ⟨L, q, c₀, hq, hsq, fun hL₀ ↦ ?_, ?_⟩
  · have := isThickening_isStableUnderBaseChange.{u}
    have hth : Stacks.Thickenings.IsThickening (F.map c₀) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqF.flip hk
    exact Stacks.Thickenings.isAffine_of_isThickening hth
  · have := isIso_liftAlongMk hk hq hsq
    exact ⟨asIso (liftAlongMk (isSectionwisePullback_uliftYoneda hsq)),
      liftAlongMk_comp_liftAlongBase _⟩

end AlgebraicGeometry.FormalSpace.DependentProduct

end
