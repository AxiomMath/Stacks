module

public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedIsomLifting

/-!
# The open locus where an isomorphism lifts along an unramified 1-morphism

Let `g : 𝒜 ⟶ ℬ` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`
which is representable by algebraic spaces and unramified in the sense of **Stacks 04XB**. Let
`s₁`, `s₂` be objects of `𝒜` over a scheme `T` and let `φ : g s₁ ⟶ g s₂` lie over `𝟙 T`. This
file shows that the set of points of `T` near which `φ` is the image of a morphism `s₁ ⟶ s₂` is
open: there is an open subset `V` of `T` such that the pullback of `φ` along a morphism
`t : T' ⟶ T` of the site lifts exactly when `t` lands in `V`.

This is the openness statement behind the proof of **Stacks 0DUA**: there the comparison
`G → H` of automorphism group algebraic spaces over a chart is an open immersion, and the set
of points of `H` lying in `G` is open.

## Main results

* `AlgebraicGeometry.Stack.exists_isOpen_map_eq_iff_range_subset`: two sections over `T` of an
  algebraic space unramified over `T` agree on the pullback along `t : T' ⟶ T` exactly when `t`
  lands in a fixed open subset of `T`.
* `AlgebraicGeometry.Stack.exists_isOpen_lift_iff_range_subset`: the lifting locus of `φ` is
  open, in the form described above.

## Implementation notes

For the sections, the relative diagonal of an unramified algebraic space over `T` is an open
immersion (**Stacks 05W1**), so its pullback along the pair of sections is an open subscheme of
`T`, and a morphism to `T` equalises the two sections exactly when it factors through that open
subscheme.

For the lifting locus, `φ` is read as the pair of sections `(s₁, φ)` and `(s₂, 𝟙)` of the
algebraic space over `T` representing the base change of `g` along the point `g s₂`, exactly as
in `AlgebraicGeometry.Stack.exists_isHomLift_map_eq_of_isRelativelyUnramified`, and the two
sections agree after pulling back along `t` exactly when the pullback of `φ` lifts.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 0DUA](https://stacks.math.columbia.edu/tag/0DUA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the big fppf site of `S` factors through a morphism whose underlying morphism
of schemes is an open immersion as soon as its image lies in the image of that open immersion. -/
theorem exists_comp_eq_of_range_subset_of_isOpenImmersion {X Y Z : BigFppfOver B S hS}
    (f : Y ⟶ X) (hf : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map f)) (g : Z ⟶ X)
    (hg : Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map f)) :
    ∃ h : Z ⟶ Y, h ≫ f = g := by
  refine ⟨Over.homMk (ObjectProperty.homMk
    (IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map g) hg)) ?_, ?_⟩
  · refine B.inclusion.map_injective ?_
    have hwg := congrArg B.inclusion.map (Over.w g)
    have hwf := congrArg B.inclusion.map (Over.w f)
    simp only [Functor.map_comp] at hwg hwf ⊢
    have hfac := IsOpenImmersion.lift_fac ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map g) hg
    change _ ≫ B.inclusion.map f.left = B.inclusion.map g.left at hfac
    rw [← hwf, ← Category.assoc]
    show (IsOpenImmersion.lift _ _ hg ≫ B.inclusion.map f.left) ≫ _ = _
    rw [hfac]
    exact hwg
  · refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp]
    exact IsOpenImmersion.lift_fac _ _ hg

end AlgebraicGeometry

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_UnramifiedLiftingLocus :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_UnramifiedLiftingLocus
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Two sections of an unramified algebraic space agree on an open subscheme.** Let `F` be an
algebraic space over a scheme `T` of the big fppf site of `S` whose structure morphism, read over
`S`, is unramified, and let `e₁`, `e₂` be two sections of `F` over `T`. There is an open subset
`V` of `T` such that for every object `a` of the big fppf site of `T`, the restrictions of `e₁`
and `e₂` to `a` agree exactly when the image of `a` in `T` lies in `V`. -/
theorem exists_isOpen_map_eq_iff_range_subset (T : BigFppfOver B S hS)
    (F : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B T.left.1 T.left.2 F)
    (hu : Space.IsUnramified B S hS
      (algebraicSpaceMap B S hS T
        ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)).hom)
    (e₁ e₂ : F.obj (op (Over.mk (𝟙 T.left)))) :
    ∃ V : Set ((BigFppfOver.toScheme B S hS).obj T), IsOpen V ∧
      ∀ (a : BigFppfOver B T.left.1 T.left.2) (t : a ⟶ Over.mk (𝟙 T.left)),
        F.map t.op e₁ = F.map t.op e₂ ↔
          Set.range ((BigFppfOver.toScheme B T.left.1 T.left.2).map t) ⊆ V := by
  letI := hasPullbacks_presheaf_UnramifiedLiftingLocus B T.left.1 T.left.2
  letI : ∀ {X Y Z : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z),
      HasLimit (cospan f g) := fun f g =>
    hasPullback_presheaf_UnramifiedLiftingLocus B T.left.1 T.left.2 f g
  have hu' : Space.IsUnramified B T.left.1 T.left.2 (Space.toYonedaId B T.left.1 T.left.2 F) :=
    (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B T.left.1 S T.left.2 hS T.hom
      (@AlgebraicGeometry.Unramified.{u}) F).mp
      ((prop_algebraicSpaceMap_iff B S hS (Space.unramifiedMorphismProperty B S hS) T F hF).mp hu)
  set h := Space.toYonedaId B T.left.1 T.left.2 F
  have hΔ : Space.IsOpenImmersion B T.left.1 T.left.2 (pullback.diagonal h) :=
    Space.isOpenImmersion_diagonal_of_isUnramified B T.left.1 T.left.2 hF
      (isAlgebraicSpace_yoneda B T.left.1 T.left.2 _) _ hu'
  let σ₁ : yoneda.obj (Over.mk (𝟙 T.left)) ⟶ F := yonedaEquiv.symm e₁
  let σ₂ : yoneda.obj (Over.mk (𝟙 T.left)) ⟶ F := yonedaEquiv.symm e₂
  have hσ : σ₁ ≫ h = σ₂ ≫ h := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    exact Over.OverMorphism.ext rfl
  let τ : yoneda.obj (Over.mk (𝟙 T.left)) ⟶ CategoryTheory.Limits.pullback h h := pullback.lift σ₁ σ₂ hσ
  have hsq : IsPullback (pullback.fst τ (pullback.diagonal h))
      (pullback.snd τ (pullback.diagonal h)) τ (pullback.diagonal h) :=
    IsPullback.of_hasPullback _ _
  have hopen : Space.IsOpenImmersion B T.left.1 T.left.2
      (pullback.fst τ (pullback.diagonal h)) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B T.left.1 T.left.2))).of_isPullback hsq.flip hΔ
  let j := pullback.fst τ (pullback.diagonal h)
  let i := hopen.rep.snd (𝟙 _)
  have hi : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B T.left.1 T.left.2).map i) :=
    hopen.property_snd (𝟙 _)
  refine ⟨Set.range ((BigFppfOver.toScheme B T.left.1 T.left.2).map i),
    hi.base_open.isOpen_range, fun a t => ?_⟩
  -- equality of the restrictions is equality of the two composites out of `yoneda a`
  have key₁ : F.map t.op e₁ = F.map t.op e₂ ↔ yoneda.map t ≫ σ₁ = yoneda.map t ≫ σ₂ := by
    rw [show yoneda.map t ≫ σ₁ = yonedaEquiv.symm (F.map t.op e₁) from
        (yonedaEquiv_symm_map t.op e₁).symm,
      show yoneda.map t ≫ σ₂ = yonedaEquiv.symm (F.map t.op e₂) from
        (yonedaEquiv_symm_map t.op e₂).symm]
    exact yonedaEquiv.symm.injective.eq_iff.symm
  -- which is a factorisation through the pullback of the diagonal
  have key₂ : yoneda.map t ≫ σ₁ = yoneda.map t ≫ σ₂ ↔
      ∃ k : yoneda.obj a ⟶ CategoryTheory.Limits.pullback τ (pullback.diagonal h), k ≫ j = yoneda.map t := by
    constructor
    · intro heq
      refine ⟨pullback.lift (yoneda.map t) (yoneda.map t ≫ σ₁) ?_, pullback.lift_fst _ _ _⟩
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
          Category.comp_id]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
          Category.comp_id, heq]
    · rintro ⟨k, hk⟩
      have hc := pullback.condition (f := τ) (g := pullback.diagonal h)
      have e₁' := congrArg (fun m => k ≫ m ≫ pullback.fst h h) hc
      have e₂' := congrArg (fun m => k ≫ m ≫ pullback.snd h h) hc
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
        Category.comp_id, pullback.lift_fst, pullback.lift_snd, τ] at e₁' e₂'
      rw [← hk]
      show k ≫ j ≫ σ₁ = k ≫ j ≫ σ₂
      exact e₁'.trans e₂'.symm
  -- which is a factorisation through the open subscheme `i`
  have key₃ : (∃ k : yoneda.obj a ⟶ CategoryTheory.Limits.pullback τ (pullback.diagonal h), k ≫ j = yoneda.map t) ↔
      ∃ l : a ⟶ hopen.rep.pullback (𝟙 _), l ≫ i = t := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨hopen.rep.lift k t (by rw [hk, Category.comp_id]),
        hopen.rep.lift_snd _ _ _⟩
    · rintro ⟨l, hl⟩
      refine ⟨yoneda.map l ≫ hopen.rep.fst (𝟙 _), ?_⟩
      rw [Category.assoc, (hopen.rep.isPullback (𝟙 _)).w, Category.comp_id, ← Functor.map_comp,
        hl]
  refine key₁.trans (key₂.trans (key₃.trans
    ⟨?_, exists_comp_eq_of_range_subset_of_isOpenImmersion i hi t⟩))
  rintro ⟨l, rfl⟩ _ ⟨y, rfl⟩
  exact ⟨(BigFppfOver.toScheme B T.left.1 T.left.2).map l y, by
    rw [Functor.map_comp, Scheme.Hom.comp_apply]⟩

/-- **The locus where an isomorphism lifts along a representable unramified 1-morphism is
open.** Let `g : 𝒜 ⟶ ℬ` be a 1-morphism of categories fibred in groupoids over the big fppf site
of `S` which is representable by algebraic spaces and unramified in the sense of Stacks 04XB.
Let `s₁`, `s₂` be objects of `𝒜` over a scheme `T` and let `φ : g s₁ ⟶ g s₂` lie over `𝟙 T`.
There is an open subset `V` of `T` such that for every object `a` of the big fppf site of `T`
with structure morphism `t`, and all pullbacks `s₁' ⟶ s₁`, `s₂' ⟶ s₂` along `t`, the pullback of
`φ` is the image of a morphism `s₁' ⟶ s₂'` over `𝟙 a` exactly when the image of `a` in `T` lies
in `V`. -/
theorem exists_isOpen_lift_iff_range_subset
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (g : 𝒜 ⟶ ℬ)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hur : IsRelativelyUnramified B S hS g)
    {T : BigFppfOver B S hS} {s₁ s₂ : 𝒜.val.obj} (h₁ : 𝒜.val.p.obj s₁ = T)
    (h₂ : 𝒜.val.p.obj s₂ = T)
    (φ : (CatFiberedInGroupoids.homFunctor g).obj s₁ ⟶
      (CatFiberedInGroupoids.homFunctor g).obj s₂)
    (hφ : ℬ.val.p.IsHomLift (𝟙 T) φ) :
    ∃ V : Set ((BigFppfOver.toScheme B S hS).obj T), IsOpen V ∧
      ∀ (a : BigFppfOver B T.left.1 T.left.2) (t : a ⟶ Over.mk (𝟙 T.left))
        (s₁' s₂' : 𝒜.val.obj) (m₁ : s₁' ⟶ s₁) (m₂ : s₂' ⟶ s₂),
        𝒜.val.p.IsHomLift ((Over.map T.hom).map t ≫ eqToHom (Functor.overMap_obj_mkId T)) m₁ →
        𝒜.val.p.IsHomLift ((Over.map T.hom).map t ≫ eqToHom (Functor.overMap_obj_mkId T)) m₂ →
        ((∃ γ : s₁' ⟶ s₂', 𝒜.val.p.IsHomLift (𝟙 ((Over.map T.hom).obj a)) γ ∧
            (CatFiberedInGroupoids.homFunctor g).map γ ≫
                (CatFiberedInGroupoids.homFunctor g).map m₂ =
              (CatFiberedInGroupoids.homFunctor g).map m₁ ≫ φ) ↔
          Set.range ((BigFppfOver.toScheme B T.left.1 T.left.2).map t) ⊆ V) := by
  classical
  let G := CatFiberedInGroupoids.homFunctor g
  have hG : G ⋙ ℬ.val.p = 𝒜.val.p := CatFiberedInGroupoids.homFunctor_comp_p g
  have hq := ℬ.isFiberedInGroupoids
  let _ : ℬ.val.p.IsFibered := hq.isFibered
  have _ : ℬ.val.p.IsStronglyCartesian (𝟙 T) φ := hq.isStronglyCartesian_homLift (𝟙 T) φ
  have _ : IsIso φ := Functor.IsStronglyCartesian.isIso_of_base_isIso ℬ.val.p (𝟙 T) φ
  have hs₂ : ℬ.val.p.obj (G.obj s₂) = T := (Functor.congr_obj hG s₂).trans h₂
  -- the scheme-valued point of `ℬ` at `g s₂`, read as a 1-morphism out of the slice site of `T`
  obtain ⟨y, hy, ξ, hξ⟩ := StacksRepresentableCFG.exists_pointOverMap_of_obj ℬ.val.p hq T
    (G.obj s₂) hs₂
  obtain ⟨F, hF, ⟨E⟩⟩ := hrep T y hy
  have hu := hur T y hy F hF ⟨E⟩
  have hT' : (Over.map T.hom).obj (Over.mk (𝟙 T.left)) = T := Functor.overMap_obj_mkId T
  have hm₁ : ℬ.val.p.IsHomLift (𝟙 T) (ξ.hom ≫ inv φ) := by
    have := hξ
    infer_instance
  -- the two objects of the 2-fibre product over the terminal object of the slice site
  let c₁ : TwoFibreProductOver (Over.map T.hom) 𝒜.val.p ℬ.val.p y G :=
    { base := T, x := Over.mk (𝟙 T.left), y := s₁, hx := hT', hy := h₁,
      iso := asIso (ξ.hom ≫ inv φ), vertical := hm₁ }
  let c₂ : TwoFibreProductOver (Over.map T.hom) 𝒜.val.p ℬ.val.p y G :=
    { base := T, x := Over.mk (𝟙 T.left), y := s₂, hx := hT', hy := h₂,
      iso := ξ, vertical := hξ }
  have hE : ∀ c, (presheafOfCategories (F ⋙ typeToCat)).p.obj (E.hom.functor.obj c) =
      (TwoFibreProductOver.fst (Over.map T.hom) 𝒜.val.p ℬ.val.p y G).obj c :=
    fun c => Functor.congr_obj E.hom.w c
  let e₁ := PresheafOfCategories.elementOf F (hE c₁)
  let e₂ := PresheafOfCategories.elementOf F (hE c₂)
  have hel : ∀ {c c' : TwoFibreProductOver (Over.map T.hom) 𝒜.val.p ℬ.val.p y G} (u : c ⟶ c'),
      PresheafOfCategories.elementOf F (hE c) =
        F.map u.a.op (PresheafOfCategories.elementOf F (hE c')) := by
    intro c c' u
    have : (TwoFibreProductOver.fst (Over.map T.hom) 𝒜.val.p ℬ.val.p y G).IsHomLift u.a u :=
      IsHomLift.map _ u
    exact PresheafOfCategories.elementOf_eq_map _ _ u.a (E.hom.functor.map u)
      (Functor.isHomLift_map_of_comp_eq E.hom.w u.a u)
  -- the pullback of a point of the 2-fibre product along `t : a ⟶ c.x`
  let mk (a : BigFppfOver B T.left.1 T.left.2) {s' s : 𝒜.val.obj} (i : y.obj a ≅ G.obj s')
      (hv : ℬ.val.p.IsHomLift (𝟙 _) i.hom) (m : s' ⟶ s)
      {r} {f : (Over.map T.hom).obj a ⟶ r} (hm : 𝒜.val.p.IsHomLift f m) :
      TwoFibreProductOver (Over.map T.hom) 𝒜.val.p ℬ.val.p y G :=
    { base := (Over.map T.hom).obj a, x := a, y := s', hx := rfl,
      hy := IsHomLift.domain_eq _ f m, iso := i, vertical := hv }
  have hpull : ∀ (c : TwoFibreProductOver (Over.map T.hom) 𝒜.val.p ℬ.val.p y G)
      (a : BigFppfOver B T.left.1 T.left.2) (t : a ⟶ c.x) (f : (Over.map T.hom).obj a ⟶ c.base)
      (s' : 𝒜.val.obj) (m : s' ⟶ c.y), (Over.map T.hom).IsHomLift f t →
      (hm : 𝒜.val.p.IsHomLift f m) → ∃ (i : y.obj a ≅ G.obj s')
        (hv : ℬ.val.p.IsHomLift (𝟙 _) i.hom),
        i.hom ≫ G.map m = y.map t ≫ c.iso.hom ∧ ℬ.val.p.IsStronglyCartesian f (G.map m) ∧
        PresheafOfCategories.elementOf F (hE (mk a i hv m hm)) =
          F.map t.op (PresheafOfCategories.elementOf F (hE c)) := by
    intro c a t f s' m ht hm
    have _ := c.vertical
    have _ : ℬ.val.p.IsHomLift f (y.map t) := Functor.isHomLift_map_of_comp_eq hy f t
    have _ : ℬ.val.p.IsHomLift f (G.map m) := Functor.isHomLift_map_of_comp_eq hG f m
    have hc := hq.isStronglyCartesian_homLift f (G.map m)
    have _ := hq.isStronglyCartesian_homLift f (y.map t ≫ c.iso.hom)
    let i := Functor.IsCartesian.domainUniqueUpToIso ℬ.val.p f (G.map m) (y.map t ≫ c.iso.hom)
    have hi := Functor.IsCartesian.fac ℬ.val.p f (G.map m) (y.map t ≫ c.iso.hom)
    have hv : ℬ.val.p.IsHomLift (𝟙 ((Over.map T.hom).obj a)) i.hom := inferInstance
    let u : mk a i hv m hm ⟶ c := { hbase := f, a := t, b := m, ha := ht, hb := hm, w := hi.symm }
    exact ⟨i, hv, hi, hc, hel u⟩
  obtain ⟨V, hV, hVe⟩ := exists_isOpen_map_eq_iff_range_subset B S hS T F hF hu e₁ e₂
  refine ⟨V, hV, fun a t s₁' s₂' m₁ m₂ hm₁' hm₂' => ?_⟩
  rw [← hVe a t]
  let t' : (Over.map T.hom).obj a ⟶ T := (Over.map T.hom).map t ≫ eqToHom hT'
  have _ : (Over.map T.hom).IsHomLift ((Over.map T.hom).map t) t := IsHomLift.map _ t
  obtain ⟨i₁, hv₁, hi₁, -, k₁⟩ := hpull c₁ a t t' s₁' m₁ inferInstance hm₁'
  obtain ⟨i₂, hv₂, hi₂, _, k₂⟩ := hpull c₂ a t t' s₂' m₂ inferInstance hm₂'
  let c₁' := mk a i₁ hv₁ m₁ hm₁'
  let c₂' := mk a i₂ hv₂ m₂ hm₂'
  constructor
  · rintro ⟨γ', hγ', hγeq⟩
    have hw : y.map (𝟙 a) ≫ i₂.hom = i₁.hom ≫ G.map γ' := by
      rw [y.map_id, Category.id_comp]
      have _ : ℬ.val.p.IsHomLift (𝟙 ((Over.map T.hom).obj a)) (G.map γ') :=
        Functor.isHomLift_map_of_comp_eq hG (𝟙 _) γ'
      refine Functor.IsCartesian.ext ℬ.val.p t' (G.map m₂) _ _ ?_
      rw [hi₂, Category.assoc, hγeq, ← Category.assoc, hi₁]
      simp [c₁, c₂]
    let v : c₁' ⟶ c₂' :=
      { hbase := 𝟙 _, a := 𝟙 a, b := γ', ha := IsHomLift.id rfl, hb := hγ', w := hw }
    have k₃ := (hel v).trans (show F.map (𝟙 a).op _ = _ by rw [op_id, F.map_id])
    exact k₁.symm.trans (k₃.trans k₂)
  · intro heq
    have hobj : E.hom.functor.obj c₁' = E.hom.functor.obj c₂' :=
      PresheafOfCategories.obj_eq_of_elementOf_eq (hE c₁') (hE c₂') (k₁.trans (heq.trans k₂.symm))
    have hfull : E.hom.functor.Full := E.toEquivalence.full_functor
    have hfaith : E.hom.functor.Faithful := E.toEquivalence.faithful_functor
    let ψ : c₁' ⟶ c₂' := E.hom.functor.preimage (eqToHom hobj)
    have hψa : ψ.a = 𝟙 a := by
      have hc := Functor.congr_hom E.hom.w ψ
      rw [Functor.comp_map, Functor.map_preimage, eqToHom_map] at hc
      have hc' := (eqToHom_comp_iff _ _ _).1 hc.symm
      rwa [comp_eqToHom_iff, eqToHom_trans, eqToHom_trans] at hc'
    have hψbase : ψ.hbase = 𝟙 _ := by
      have _ := ψ.ha
      have _ : (Over.map T.hom).IsHomLift (𝟙 ((Over.map T.hom).obj a)) ψ.a := by
        rw [hψa]
        exact IsHomLift.id rfl
      exact (IsHomLift.fac (Over.map T.hom) ψ.hbase ψ.a).trans
        (IsHomLift.fac (Over.map T.hom) (𝟙 _) ψ.a).symm
    have hb := ψ.hb
    rw [hψbase] at hb
    refine ⟨ψ.b, hb, ?_⟩
    have hw := ψ.w
    rw [hψa, y.map_id, Category.id_comp] at hw
    change i₂.hom = i₁.hom ≫ G.map ψ.b at hw
    rw [← cancel_epi i₁.hom, ← Category.assoc, ← hw, hi₂, ← Category.assoc, hi₁]
    simp [c₁, c₂]

end AlgebraicGeometry.Stack

end
