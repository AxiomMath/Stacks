module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.CategoryTheory.MonoPushforward

/-!
# Extending an étale morphism across a thickening of arbitrary order

Let `i : F₀ ⟶ F` be a monomorphism of presheaves on the big fppf site of `S` with values in
`Type (u + 1)` which is a representable thickening, and let `u₀ : C₀ ⟶ F₀` be étale,
representably by schemes. The pushforward `CategoryTheory.monoPushforward i u₀` is étale over
`F`, representably by schemes, and its base change along `i` is `C₀`
(`CategoryTheory.isPullback_monoPushforward_unit`). So `u₀` extends across the thickening to a
representable étale morphism, with a cartesian square: this is the essential surjectivity of
base change of étale morphisms along a thickening, Stacks 05ZH, at a thickening of arbitrary
order, for a morphism which is representable by schemes.

## Main results

* `AlgebraicGeometry.Space.isPullback_extensionHom`: over an object `T` of the site with a
  morphism `ξ : T ⟶ F`, the étale lift `V ⟶ T` of the base change of `u₀` represents the base
  change of the pushforward along `ξ`.
* `AlgebraicGeometry.Space.hasSchemePropertyULift_etale_monoPushforward_π`: the pushforward is
  étale over `F`, representably by schemes.
* `AlgebraicGeometry.Space.exists_etale_isPullback_of_isRepresentableThickeningULift`: an étale
  morphism to `F₀`, representable by schemes, is the base change along `i` of one to `F`.

## Implementation notes

Over an object `T` of the site with a morphism `ξ : T ⟶ F`, the base change of `i` is a
thickening `t : T₀ ⟶ T` of objects of the site, the base change of `u₀` to `T₀` is an object
`C₁` étale over `T₀`, and Stacks 039R with size control
(`Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective`) lifts
`C₁` to an object `V` étale over `T` with `C₁ = V ×_T T₀`. A section of the pushforward over
`T' ⟶ T` is a morphism `T' ×_T T₀ ⟶ C₁` over `T₀`, and those are the morphisms `T' ⟶ V` over
`T` by `AlgebraicGeometry.Space.existsUnique_extend_of_isPullback_of_isThickening` (Stacks
0BTY). The order of the thickening plays no role, and no quotient of an étale equivalence
relation is formed.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Restricting the point of a presheaf given by a morphism out of a representable presheaf. -/
theorem map_app_uliftYoneda_up {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {X : BigFppfOver B S hS} (α : uliftYoneda.{u + 1}.obj X ⟶ G) {T₁ T₂ : BigFppfOver B S hS}
    (g : T₂ ⟶ T₁) (h : T₁ ⟶ X) :
    G.map g.op (α.app (op T₁) (ULift.up h : (uliftYoneda.{u + 1}.obj X).obj (op T₁))) =
      α.app (op T₂) (ULift.up (g ≫ h) : (uliftYoneda.{u + 1}.obj X).obj (op T₂)) :=
  (NatTrans.naturality_apply α g.op _).symm

/-- A commutative square of presheaves of types commutes on every section. -/
theorem app_app_eq_of_comp_eq {P X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {f : P ⟶ X} {g : P ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z} (w : f ≫ h = g ≫ k)
    (U : (BigFppfOver B S hS)ᵒᵖ) (x : P.obj U) : h.app U (f.app U x) = k.app U (g.app U x) := by
  simpa using congrArg (fun φ : P ⟶ Z ↦ φ.app U x) w

/-- A point of the top-right corner of a cartesian square with a represented corner whose image
agrees with the point `h` of the base is the image of a morphism `τ` lifting `h`. -/
private theorem exists_comp_eq_of_isPullback
    {F₀ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {i : F₀ ⟶ F} {T₀ T : BigFppfOver B S hS}
    {t : T₀ ⟶ T} {ξ : uliftYoneda.{u + 1}.obj T ⟶ F} {e₀ : uliftYoneda.{u + 1}.obj T₀ ⟶ F₀}
    (sq : IsPullback e₀ (uliftYoneda.{u + 1}.map t) i ξ) {T' : BigFppfOver B S hS}
    (x : F₀.obj (op T')) (h : T' ⟶ T)
    (hx : i.app (op T') x = ξ.app (op T') (ULift.up h : (uliftYoneda.{u + 1}.obj T).obj (op T'))) :
    ∃ τ : T' ⟶ T₀, τ ≫ t = h ∧
      e₀.app (op T') (ULift.up τ : (uliftYoneda.{u + 1}.obj T₀).obj (op T')) = x := by
  have hw : uliftYonedaEquiv.symm x ≫ i = uliftYoneda.{u + 1}.map h ≫ ξ := by
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp, Equiv.apply_symm_apply, hx,
      uliftYonedaEquiv_uliftYoneda_map]
  refine ⟨uliftYoneda.{u + 1}.preimage (sq.lift _ _ hw), ?_, ?_⟩
  · apply uliftYoneda.{u + 1}.map_injective
    rw [Functor.map_comp, Functor.map_preimage, sq.lift_snd]
  · have h' := congrArg uliftYonedaEquiv (sq.lift_fst _ _ hw)
    rwa [← Functor.map_preimage uliftYoneda.{u + 1} (sq.lift _ _ hw), uliftYonedaEquiv_comp,
      uliftYonedaEquiv_uliftYoneda_map, Equiv.apply_symm_apply] at h'

/-- A section of a presheaf over the base of a cartesian square with a represented corner lies
in the image of the other side exactly when the corresponding morphism of the site factors
through the represented corner. -/
theorem mem_range_app_iff_of_isPullback
    {F₀ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {i : F₀ ⟶ F} {T₀ T : BigFppfOver B S hS}
    {t : T₀ ⟶ T} {ξ : uliftYoneda.{u + 1}.obj T ⟶ F} {e₀ : uliftYoneda.{u + 1}.obj T₀ ⟶ F₀}
    (sq : IsPullback e₀ (uliftYoneda.{u + 1}.map t) i ξ) {T' : BigFppfOver B S hS}
    (h : T' ⟶ T) :
    ξ.app (op T') (ULift.up h : (uliftYoneda.{u + 1}.obj T).obj (op T')) ∈
      Set.range (i.app (op T')) ↔ ∃ τ : T' ⟶ T₀, τ ≫ t = h := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨τ, hτ, -⟩ := exists_comp_eq_of_isPullback sq b h hb
    exact ⟨τ, hτ⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨e₀.app (op T') (ULift.up τ : (uliftYoneda.{u + 1}.obj T₀).obj (op T')),
      app_app_eq_of_comp_eq sq.w (op T') _⟩

/-- The base change of a representable thickening `i`, read over an object `T` of the site
through a cartesian square `sq₀`, along any morphism `k : T' ⟶ T` of the site. -/
theorem exists_isPullback_of_isPullback_of_rep {F₀ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {i : F₀ ⟶ F} (hi : uliftYoneda.{u + 1}.relativelyRepresentable i)
    {T₀ T : BigFppfOver B S hS} {t : T₀ ⟶ T} {ξ : uliftYoneda.{u + 1}.obj T ⟶ F}
    {e₀ : uliftYoneda.{u + 1}.obj T₀ ⟶ F₀} (sq₀ : IsPullback e₀ (uliftYoneda.{u + 1}.map t) i ξ)
    {T' : BigFppfOver B S hS} (k : T' ⟶ T) :
    ∃ (T'₀ : BigFppfOver B S hS) (a : T'₀ ⟶ T') (b : T'₀ ⟶ T₀), IsPullback a b k t := by
  let g := uliftYoneda.{u + 1}.map k ≫ ξ
  have H := hi.isPullback g
  have hw : hi.fst g ≫ i = (uliftYoneda.{u + 1}.map (hi.snd g) ≫ uliftYoneda.{u + 1}.map k) ≫ ξ :=
    by rw [H.w, Category.assoc]
  let b' := sq₀.lift (hi.fst g) (uliftYoneda.{u + 1}.map (hi.snd g) ≫ uliftYoneda.{u + 1}.map k) hw
  have hout : IsPullback (b' ≫ e₀) (uliftYoneda.{u + 1}.map (hi.snd g)) i
      (uliftYoneda.{u + 1}.map k ≫ ξ) := by
    rw [sq₀.lift_fst]
    exact H
  have hsq : IsPullback b' (uliftYoneda.{u + 1}.map (hi.snd g)) (uliftYoneda.{u + 1}.map t)
      (uliftYoneda.{u + 1}.map k) := IsPullback.of_right hout (sq₀.lift_snd _ _ _) sq₀
  refine ⟨hi.pullback g, hi.snd g, uliftYoneda.{u + 1}.preimage b', ?_⟩
  refine IsPullback.flip (IsPullback.of_map_of_faithful uliftYoneda.{u + 1} ?_)
  rw [Functor.map_preimage]
  exact hsq

section extension

variable {F₀ F C₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {i : F₀ ⟶ F} {u₀ : C₀ ⟶ F₀}
  {T₀ T V C₁ : BigFppfOver B S hS} {t : T₀ ⟶ T} {ξ : uliftYoneda.{u + 1}.obj T ⟶ F}
  {e₀ : uliftYoneda.{u + 1}.obj T₀ ⟶ F₀}
  (sq₀ : IsPullback e₀ (uliftYoneda.{u + 1}.map t) i ξ) {q : V ⟶ T} {ψ : C₁ ⟶ V}
  {p : C₁ ⟶ T₀} (hC : IsPullback ψ p q t) {c : uliftYoneda.{u + 1}.obj C₁ ⟶ C₀}
  (sq₁ : IsPullback c (uliftYoneda.{u + 1}.map p) u₀ e₀)

include sq₀ sq₁ in
/-- The image in `F` of the point of `C₀` given by a morphism into `C₁`. -/
theorem app_app_extension {T₂ : BigFppfOver B S hS} (L : T₂ ⟶ C₁) {τ : T₂ ⟶ T₀}
    (hL : L ≫ p = τ) :
    i.app (op T₂) (u₀.app (op T₂)
      (c.app (op T₂) (ULift.up L : (uliftYoneda.{u + 1}.obj C₁).obj (op T₂)))) =
      ξ.app (op T₂) (ULift.up (τ ≫ t) : (uliftYoneda.{u + 1}.obj T).obj (op T₂)) := by
  rw [app_app_eq_of_comp_eq sq₁.w (op T₂) (ULift.up L : (uliftYoneda.{u + 1}.obj C₁).obj (op T₂))]
  show i.app (op T₂)
    (e₀.app (op T₂) (ULift.up (L ≫ p) : (uliftYoneda.{u + 1}.obj T₀).obj (op T₂))) = _
  rw [hL]
  exact app_app_eq_of_comp_eq sq₀.w (op T₂) (ULift.up τ : (uliftYoneda.{u + 1}.obj T₀).obj (op T₂))

open Classical in
/-- The section over `T'` of the pushforward of `u₀` along `i` attached to a morphism
`v : T' ⟶ V`: its base is the point `v ≫ q` of `F`, and at `g : T'' ⟶ T'` its lift is the
point of `C₀` given by the morphism `T'' ⟶ C₁ = V ×_T T₀` with components `g ≫ v` and the
factorization of `g ≫ v ≫ q` through `T₀`, when there is one. -/
noncomputable def extensionSection [Mono t] {T' : BigFppfOver B S hS} (v : T' ⟶ V) :
    MonoPushforwardSection i u₀ T' where
  base := ξ.app (op T') (ULift.up (v ≫ q) : (uliftYoneda.{u + 1}.obj T).obj (op T'))
  sect T'' g := if h : ∃ τ : T'' ⟶ T₀, τ ≫ t = g ≫ v ≫ q then
      some (c.app (op T'') (ULift.up (hC.lift (g ≫ v) h.choose
        (by rw [h.choose_spec, Category.assoc])) : (uliftYoneda.{u + 1}.obj C₁).obj (op T'')))
    else none
  isSome_sect_iff T'' g := by
    rw [map_app_uliftYoneda_up, mem_range_app_iff_of_isPullback sq₀]
    split_ifs with h <;> simp [h]
  sect_over T'' g a ha := by
    split_ifs at ha with h
    cases ha
    rw [map_app_uliftYoneda_up, app_app_extension sq₀ sq₁ _ (hC.lift_snd _ _ _), h.choose_spec]
  sect_comp T'' T''' g h a ha := by
    split_ifs at ha with hg
    cases ha
    have hτ : (h ≫ hg.choose) ≫ t = (h ≫ g) ≫ v ≫ q := by
      rw [Category.assoc, hg.choose_spec, Category.assoc]
    have hex : ∃ τ : T''' ⟶ T₀, τ ≫ t = (h ≫ g) ≫ v ≫ q := ⟨_, hτ⟩
    rw [dif_pos hex, map_app_uliftYoneda_up]
    congr 3
    apply hC.hom_ext
    · simp only [hC.lift_fst, Category.assoc]
    · simp only [hC.lift_snd, Category.assoc]
      exact (cancel_mono t).1 (hex.choose_spec.trans hτ.symm)

open Classical in
/-- The lift of `extensionSection` at `g` is the point of `C₀` given by any morphism into `C₁`
whose component to `V` is `g ≫ v`. -/
theorem extensionSection_sect_eq [Mono t] {T' T'' : BigFppfOver B S hS} (v : T' ⟶ V)
    (g : T'' ⟶ T') (L : T'' ⟶ C₁) (hL : L ≫ ψ = g ≫ v) :
    (extensionSection sq₀ hC sq₁ v).sect g =
      some (c.app (op T'') (ULift.up L : (uliftYoneda.{u + 1}.obj C₁).obj (op T''))) := by
  have hex : ∃ τ : T'' ⟶ T₀, τ ≫ t = g ≫ v ≫ q :=
    ⟨L ≫ p, by rw [Category.assoc, ← hC.w, ← Category.assoc, hL, Category.assoc]⟩
  show (if h : ∃ τ : T'' ⟶ T₀, τ ≫ t = g ≫ v ≫ q then _ else none) = _
  rw [dif_pos hex]
  congr 3
  apply hC.hom_ext
  · rw [hC.lift_fst, hL]
  · rw [hC.lift_snd]
    apply (cancel_mono t).1
    rw [hex.choose_spec, Category.assoc, ← hC.w, reassoc_of% hL]

open Classical in
/-- `extensionSection` has no lift at `g` when `g ≫ v ≫ q` does not factor through `T₀`. -/
theorem extensionSection_sect_eq_none [Mono t] {T' T'' : BigFppfOver B S hS} (v : T' ⟶ V)
    (g : T'' ⟶ T') (h : ¬ ∃ τ : T'' ⟶ T₀, τ ≫ t = g ≫ v ≫ q) :
    (extensionSection sq₀ hC sq₁ v).sect g = none :=
  dif_neg h

/-- The morphism from the presheaf represented by the étale lift `V` to the pushforward of
`u₀` along `i`, given on sections by `AlgebraicGeometry.Space.extensionSection`. -/
noncomputable def extensionHom [Mono t] : uliftYoneda.{u + 1}.obj V ⟶ monoPushforward i u₀ where
  app T' := ↾fun v ↦ extensionSection sq₀ hC sq₁ (T' := T'.unop) v.down
  naturality T₁ T₂ k := by
    ext v
    change extensionSection sq₀ hC sq₁ (k.unop ≫ v.down) =
      (extensionSection sq₀ hC sq₁ v.down).restrict k.unop
    refine MonoPushforwardSection.ext ?_ ?_
    · change ξ.app _ (ULift.up ((k.unop ≫ v.down) ≫ q) : (uliftYoneda.{u + 1}.obj T).obj _) =
        F.map k (ξ.app _ (ULift.up (v.down ≫ q) : (uliftYoneda.{u + 1}.obj T).obj _))
      rw [Category.assoc]
      exact (map_app_uliftYoneda_up ξ k.unop _).symm
    · funext T'' g
      rw [MonoPushforwardSection.restrict_sect]
      by_cases h : ∃ τ : T'' ⟶ T₀, τ ≫ t = g ≫ (k.unop ≫ v.down) ≫ q
      · obtain ⟨τ, hτ⟩ := h
        have hw : (g ≫ k.unop ≫ v.down) ≫ q = τ ≫ t := by
          rw [hτ, Category.assoc, Category.assoc]
        rw [extensionSection_sect_eq sq₀ hC sq₁ _ g (hC.lift _ τ hw) (by rw [hC.lift_fst]),
          extensionSection_sect_eq sq₀ hC sq₁ _ (g ≫ k.unop) (hC.lift _ τ hw)
            (by rw [hC.lift_fst, Category.assoc])]
      · rw [extensionSection_sect_eq_none sq₀ hC sq₁ _ g h,
          extensionSection_sect_eq_none sq₀ hC sq₁ _ (g ≫ k.unop) (by
            simpa only [Category.assoc] using h)]

/-- `AlgebraicGeometry.Space.extensionHom` sends a morphism `v : T' ⟶ V` to the section
`AlgebraicGeometry.Space.extensionSection` attached to `v`. -/
@[simp]
lemma extensionHom_app_apply [Mono t] (T' : (BigFppfOver B S hS)ᵒᵖ)
    (v : (uliftYoneda.{u + 1}.obj V).obj T') :
    (extensionHom sq₀ hC sq₁).app T' v = extensionSection sq₀ hC sq₁ (T' := T'.unop) v.down :=
  rfl

include sq₀ hC sq₁ in
/-- **The étale lift represents the base change of the pushforward.** Over an object `T` of the
site with a morphism `ξ : T ⟶ F`, let `t : T₀ ⟶ T` be the base change of the thickening `i`,
let `C₁ ⟶ T₀` be the base change of `u₀`, and let `V ⟶ T` be étale with `C₁ = V ×_T T₀`. Then
`V` is the base change of the pushforward of `u₀` along `i` to `T`. -/
theorem isPullback_extensionHom (hi : uliftYoneda.{u + 1}.relativelyRepresentable i) [Mono i]
    (ht : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map t))
    (hq : Etale ((BigFppfOver.toScheme B S hS).map q)) [Mono t] :
    IsPullback (extensionHom sq₀ hC sq₁) (uliftYoneda.{u + 1}.map q) (monoPushforward.π i u₀)
      ξ := by
  refine IsPullback.of_forall_isPullback_app fun T' ↦ ?_
  rw [Types.isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro x₁ x₂ ⟨h₁, h₂⟩
    set v₁ := x₁.down
    set v₂ := x₂.down
    change extensionSection sq₀ hC sq₁ v₁ = extensionSection sq₀ hC sq₁ v₂ at h₁
    have hq₁₂ : v₁ ≫ q = v₂ ≫ q := congrArg ULift.down h₂
    obtain ⟨T'₀, a, b, hT'⟩ := exists_isPullback_of_isPullback_of_rep hi sq₀ (v₁ ≫ q)
    have hw₁ : (a ≫ v₁) ≫ q = b ≫ t := by rw [Category.assoc, hT'.w]
    have hw₂ : (a ≫ v₂) ≫ q = b ≫ t := by rw [Category.assoc, ← hq₁₂, hT'.w]
    have hs := congrArg (fun s : MonoPushforwardSection i u₀ T'.unop ↦ s.sect a) h₁
    rw [extensionSection_sect_eq sq₀ hC sq₁ v₁ a (hC.lift _ b hw₁) (hC.lift_fst _ _ _),
      extensionSection_sect_eq sq₀ hC sq₁ v₂ a (hC.lift _ b hw₂) (hC.lift_fst _ _ _),
      Option.some_inj] at hs
    have hL : hC.lift _ b hw₁ = hC.lift _ b hw₂ := by
      apply uliftYoneda.{u + 1}.map_injective
      apply sq₁.hom_ext
      · apply uliftYonedaEquiv.injective
        rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map,
          uliftYonedaEquiv_uliftYoneda_map]
        exact hs
      · rw [← Functor.map_comp, ← Functor.map_comp, hC.lift_snd, hC.lift_snd]
    have hav : a ≫ v₁ = a ≫ v₂ := by
      rw [← hC.lift_fst _ b hw₁, ← hC.lift_fst _ b hw₂, hL]
    obtain ⟨w, -, hwu⟩ := existsUnique_extend_of_isPullback_of_isThickening B S hS ht hq hT'
      (a ≫ v₁) (by rw [Category.assoc])
    have e₁ := hwu v₁ ⟨rfl, rfl⟩
    have e₂ := hwu v₂ ⟨hq₁₂.symm, hav.symm⟩
    exact ULift.ext (e₁.trans e₂.symm)
  · intro s y hsk
    set k := y.down
    change s.base = ξ.app T' (ULift.up k : (uliftYoneda.{u + 1}.obj T).obj T') at hsk
    obtain ⟨T'₀, a, b, hT'⟩ := exists_isPullback_of_isPullback_of_rep hi sq₀ k
    have hbase : F.map a.op s.base =
        ξ.app (op T'₀) (ULift.up (b ≫ t) : (uliftYoneda.{u + 1}.obj T).obj (op T'₀)) := by
      rw [hsk, ← hT'.w]
      exact map_app_uliftYoneda_up ξ a k
    have hsome : (s.sect a).isSome := by
      rw [s.isSome_sect_iff, hbase, mem_range_app_iff_of_isPullback sq₀]
      exact ⟨b, rfl⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
    have hover : u₀.app (op T'₀) x =
        e₀.app (op T'₀) (ULift.up b : (uliftYoneda.{u + 1}.obj T₀).obj (op T'₀)) := by
      apply (mono_iff_injective (i.app (op T'₀))).1 inferInstance
      rw [s.sect_over a x hx, hbase]
      exact (app_app_eq_of_comp_eq sq₀.w (op T'₀) _).symm
    obtain ⟨L, hLp, hLc⟩ := exists_comp_eq_of_isPullback sq₁ x b hover
    have hn : (L ≫ ψ) ≫ q = a ≫ k := by
      rw [Category.assoc, hC.w, ← Category.assoc, hLp, hT'.w]
    obtain ⟨v, ⟨hvq, hav⟩, -⟩ :=
      existsUnique_extend_of_isPullback_of_isThickening B S hS ht hq hT' (L ≫ ψ) hn
    refine ⟨(ULift.up v : (uliftYoneda.{u + 1}.obj V).obj T'), ?_, ULift.ext hvq⟩
    show extensionSection sq₀ hC sq₁ v = s
    refine MonoPushforwardSection.ext ?_ ?_
    · show ξ.app _ (ULift.up (v ≫ q) : (uliftYoneda.{u + 1}.obj T).obj _) = s.base
      rw [hvq, hsk]
    · funext T'' g
      by_cases h : ∃ τ : T'' ⟶ T₀, τ ≫ t = g ≫ v ≫ q
      · obtain ⟨τ, hτ⟩ := h
        have hgk : g ≫ k = τ ≫ t := by rw [hτ, hvq]
        let g' := hT'.lift g τ hgk
        have hg'a : g' ≫ a = g := hT'.lift_fst _ _ _
        have hL' : (g' ≫ L) ≫ ψ = g ≫ v := by
          rw [Category.assoc, ← hav, ← Category.assoc, hg'a]
        rw [extensionSection_sect_eq sq₀ hC sq₁ v g (g' ≫ L) hL', ← hg'a,
          s.sect_comp a g' x hx, ← hLc, map_app_uliftYoneda_up]
      · rw [extensionSection_sect_eq_none sq₀ hC sq₁ v g h]
        symm
        rw [← Option.not_isSome_iff_eq_none, s.isSome_sect_iff, hsk, map_app_uliftYoneda_up,
          mem_range_app_iff_of_isPullback sq₀, ← hvq]
        simpa only [Category.assoc] using h

end extension

variable (B S hS) in
/-- **Stacks 05ZH, essential surjectivity, at a thickening of arbitrary order, for a morphism
representable by schemes.** Let `i : F₀ ⟶ F` be a monomorphism of presheaves on the big fppf
site of `S` which is a representable thickening, and let `u₀ : C₀ ⟶ F₀` be étale, representably
by schemes. The pushforward `CategoryTheory.monoPushforward i u₀` is étale over `F`,
representably by schemes. -/
theorem hasSchemePropertyULift_etale_monoPushforward_π
    {F₀ F C₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (i : F₀ ⟶ F) [Mono i]
    (hi : IsRepresentableThickeningULift.{u + 1} B S hS i) (u₀ : C₀ ⟶ F₀)
    (hu₀ : HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) :
    HasSchemePropertyULift.{u + 1} B S hS (@Etale) (monoPushforward.π i u₀) := by
  have : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage (@Etale) (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists (fun T ξ ↦ ?_)
  have sq₀ := hi.rep.isPullback ξ
  have ht : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd ξ)) := hi.property_snd ξ
  have sq₁ := hu₀.rep.isPullback (hi.rep.fst ξ)
  have hp : Etale ((BigFppfOver.toScheme B S hS).map (hu₀.rep.snd (hi.rep.fst ξ))) :=
    hu₀.property_snd _
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd ξ)) := ht.1
  have : Mono (hi.rep.snd ξ) :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  obtain ⟨V, q, hq, e, he⟩ :=
    Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective B S hS
      (hi.rep.snd ξ) ht.2 _ _ hp
  obtain ⟨ψ, hC⟩ := exists_isPullback_of_iso_pullback_toScheme B S hS q _ _ e he
  exact ⟨V, extensionHom sq₀ hC sq₁, q, isPullback_extensionHom sq₀ hC sq₁ hi.rep ht hq, hq⟩

variable (B S hS) in
/-- **Stacks 05ZH, essential surjectivity, at a thickening of arbitrary order, for a morphism
representable by schemes**, in the form of a cartesian square: an étale morphism `u₀ : C₀ ⟶ F₀`,
representable by schemes, is the base change along a representable thickening `i : F₀ ⟶ F` of
an étale morphism to `F`, representable by schemes. -/
theorem exists_etale_isPullback_of_isRepresentableThickeningULift
    {F₀ F C₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (i : F₀ ⟶ F) [Mono i]
    (hi : IsRepresentableThickeningULift.{u + 1} B S hS i) (u₀ : C₀ ⟶ F₀)
    (hu₀ : HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) :
    ∃ (C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) (u : C ⟶ F) (j : C₀ ⟶ C),
      HasSchemePropertyULift.{u + 1} B S hS (@Etale) u ∧ IsPullback j u₀ u i :=
  ⟨_, _, _, hasSchemePropertyULift_etale_monoPushforward_π B S hS i hi u₀ hu₀,
    isPullback_monoPushforward_unit i u₀⟩

end AlgebraicGeometry.Space

end
