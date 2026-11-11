module

public import StacksFrontier.CategoryTheory.Sites.OverPullbackPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.ClassRestrictionToAnObject
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization

/-!
# Locally trivial first cohomology classes over a base change come from the base

Let `(C, J)` be a site with pullbacks, `f : X ⟶ Y` a monomorphism of `C` and `F` an abelian
sheaf on the slice site `(Over Y, J.over Y)`. Write `𝒢 = F.baseChangePushforward f` for the
sheaf `T ↦ F(T ×_Y X)`, the direct image along `π : T ↦ T ×_Y X` of the restriction of `F`
to the objects over `X`.

For `U : Over Y` this file proves the low-degree part of the Leray spectral sequence for `π`:
a class `c ∈ H¹(U ×_Y X, 𝒢)` which vanishes on `T ×_Y X` for every `T ⟶ U` in a covering
sieve of `U` is the restriction along the first projection `U ×_Y X ⟶ U` of a class in
`H¹(U, 𝒢)`.

## Main results

* `Stacks.Cohomology.OverObjectCohomology.freeYonedaSheafHomEquiv_naturality_left`: the
  corepresentation of evaluation by the free abelian sheaf on `yoneda.obj U` turns
  precomposition with the map induced by `g : V ⟶ U` into restriction along `g`.
* `Stacks.Cohomology.OverObjectCohomology.eq_zero_of_forall_freeYonedaSheaf_map_comp_eq_zero`:
  a morphism out of the free abelian sheaf on `yoneda.obj U` vanishing on a covering sieve
  vanishes.
* `CategoryTheory.Sheaf.baseChangePushforwardFunctor`: `F ↦ F.baseChangePushforward f` as a
  left exact functor, with `toBaseChangePushforward_naturality`.
* `CategoryTheory.Sheaf.isIso_toBaseChangePushforward_baseChangePushforward`: for `f` a
  monomorphism, `𝒢 ⟶ 𝒢.baseChangePushforward f` is an isomorphism.
* `CategoryTheory.Sheaf.exists_baseChangeFst_cohomologyPresheaf_map_eq`: **the main
  result**.

## Implementation notes

Choose an embedding `𝒢 ⟶ I` into an injective sheaf, with cokernel `Q`, and apply the left
exact functor `Φ = baseChangePushforwardFunctor f`. The cokernel `Q''` of `Φ 𝒢 ⟶ Φ I` embeds
into `Φ Q` by left exactness. The class `c` is the boundary of a section `q` of `Q` over
`U ×_Y X`, that is, of a section of `Φ Q` over `U`; the local vanishing of `c` says that this
section of `Φ Q` lies locally in the image of `Φ I`, hence comes from a section of `Q''` over
`U`, whose boundary in `H¹(U, Φ 𝒢) ≅ H¹(U, 𝒢)` is the class sought. Comparing it with `c`
uses that the two maps `(U ×_Y X) ×_Y X ⟶ U ×_Y X` agree when `f` is a monomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w v u v' u'

namespace CategoryTheory.Abelian.Ext

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]

/-- Transport of a boundary class along a morphism of extensions whose first map is an
isomorphism: if `E.comp (mk₀ η) = (mk₀ τ).comp E''` and `a ≫ s = q ≫ τ`, then
`(mk₀ a).comp (((mk₀ s).comp E'').comp (mk₀ η⁻¹)) = (mk₀ q).comp E`. -/
lemma mk₀_comp_comp_mk₀_inv_eq_of_comp_eq {A A' X₁ X₃ X₁'' X₃'' : D} (a : A' ⟶ A)
    (s : A ⟶ X₃'') (q : A' ⟶ X₃) (τ : X₃ ⟶ X₃'') (η : X₁ ⟶ X₁'') [IsIso η]
    (E : Ext.{w} X₃ X₁ 1) (E'' : Ext.{w} X₃'' X₁'' 1) (h : a ≫ s = q ≫ τ)
    (hE : E.comp (mk₀ η) (add_zero 1) = (mk₀ τ).comp E'' (zero_add 1)) :
    (mk₀ a).comp (((mk₀ s).comp E'' (zero_add 1)).comp (mk₀ (inv η)) (add_zero 1))
        (zero_add 1) = (mk₀ q).comp E (zero_add 1) := by
  rw [← comp_assoc_of_third_deg_zero, mk₀_comp_mk₀_assoc, h, ← mk₀_comp_mk₀_assoc, ← hE,
    comp_assoc_of_third_deg_zero, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀,
    IsIso.hom_inv_id, comp_mk₀_id]

end CategoryTheory.Abelian.Ext

namespace Stacks.Cohomology.OverObjectCohomology

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
  [HasSheafify K AddCommGrpCat.{v}]

/-- **The corepresentation of evaluation is natural in the object.** Precomposition with the
morphism of free abelian sheaves induced by `g : V ⟶ U` corresponds to restriction of sections
along `g`. -/
lemma freeYonedaSheafHomEquiv_naturality_left {U V : C} (g : V ⟶ U)
    (P : Sheaf K AddCommGrpCat.{v}) (α : freeYonedaSheaf K U ⟶ P) :
    freeYonedaSheafHomEquiv K V P
        ((presheafToSheaf K AddCommGrpCat.{v}).map
          (Functor.whiskerRight (yoneda.map g) AddCommGrpCat.free) ≫ α) =
      P.obj.map g.op (freeYonedaSheafHomEquiv K U P α) := by
  dsimp only [freeYonedaSheafHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left,
    show Functor.whiskerRight (yoneda.map g) AddCommGrpCat.free =
      ((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free).map
        (yoneda.map g) from rfl, Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ g).symm

/-- **A morphism out of a free abelian sheaf on a representable is determined locally.** If
its precompositions with the maps induced by the members of a covering sieve vanish, it
vanishes. -/
lemma eq_zero_of_forall_freeYonedaSheaf_map_comp_eq_zero {U : C} {P : Sheaf K AddCommGrpCat.{v}}
    (α : freeYonedaSheaf K U ⟶ P) (R : Sieve U) (hR : R ∈ K U)
    (h : ∀ ⦃T : C⦄ (t : T ⟶ U), R t →
      (presheafToSheaf K AddCommGrpCat.{v}).map
        (Functor.whiskerRight (yoneda.map t) AddCommGrpCat.free) ≫ α = 0) :
    α = 0 := by
  apply (freeYonedaSheafHomEquiv K U P).injective
  refine Sheaf.isSeparated P U R hR _ _ fun T t ht => ?_
  rw [← freeYonedaSheafHomEquiv_naturality_left, ← freeYonedaSheafHomEquiv_naturality_left,
    h t ht, comp_zero]

end Stacks.Cohomology.OverObjectCohomology

namespace CategoryTheory.Sheaf

open Stacks.Cohomology

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {J : GrothendieckTopology C}

section Functor

variable {X Y : C} (f : X ⟶ Y) (A : Type u') [Category.{v'} A]

/-- The functor `F ↦ F.baseChangePushforward f`, restriction along `Over.map f` followed by
pushforward along `Over.pullback f`. -/
abbrev baseChangePushforwardFunctor : Sheaf (J.over Y) A ⥤ Sheaf (J.over Y) A :=
  (Over.map f).sheafPushforwardContinuous A (J.over X) (J.over Y) ⋙
    (Over.pullback f).sheafPushforwardContinuous A (J.over Y) (J.over X)

variable {A}

/-- The restriction maps of `(baseChangePushforwardFunctor f A).obj P` are those of `P` along
the base changes `T ×_Y X ⟶ T' ×_Y X`. -/
lemma baseChangePushforwardFunctor_obj_obj_map (P : Sheaf (J.over Y) A) {T T' : Over Y}
    (g : T ⟶ T') :
    ((baseChangePushforwardFunctor f A).obj P).obj.map g.op =
      P.obj.map ((Over.map f).map ((Over.pullback f).map g)).op :=
  rfl

/-- The component at `T` of `(baseChangePushforwardFunctor f A).map α` is the component of `α`
at `T ×_Y X`. -/
lemma baseChangePushforwardFunctor_map_hom_app {P P' : Sheaf (J.over Y) A} (α : P ⟶ P')
    (T : Over Y) :
    ((baseChangePushforwardFunctor f A).map α).hom.app (op T) =
      α.hom.app (op ((Over.map f).obj ((Over.pullback f).obj T))) :=
  rfl

/-- The morphisms `F ⟶ F.baseChangePushforward f` are natural in `F`. -/
@[reassoc]
lemma toBaseChangePushforward_naturality {F G : Sheaf (J.over Y) A} (g : F ⟶ G) :
    F.toBaseChangePushforward f ≫ (baseChangePushforwardFunctor f A).map g =
      g ≫ G.toBaseChangePushforward f :=
  Sheaf.hom_ext (NatTrans.ext (funext fun T => g.hom.naturality (baseChangeFst f T.unop).op))

/-- If `f` is a monomorphism, the two morphisms `(T ×_Y X) ×_Y X ⟶ T ×_Y X` given by the base
change of the first projection and by the first projection itself agree. -/
lemma map_pullback_map_baseChangeFst [Mono f] (T : Over Y) :
    (Over.map f).map ((Over.pullback f).map (baseChangeFst f T)) =
      baseChangeFst f ((Over.map f).obj ((Over.pullback f).obj T)) := by
  ext
  apply pullback.hom_ext
  · simp only [Over.map_map_left, Over.pullback_map_left, baseChangeFst, Over.homMk_left]
    exact pullback.lift_fst _ _ _
  · simp only [Over.map_map_left, Over.pullback_map_left, baseChangeFst, Over.homMk_left]
    rw [← cancel_mono f, Category.assoc]
    refine (pullback.lift_snd_assoc _ _ _ _).trans ?_
    exact (pullback.condition (f := ((Over.map f).obj ((Over.pullback f).obj T)).hom)
      (g := f)).symm.trans (Category.assoc _ _ _).symm

/-- If `f` is a monomorphism, the sheaf `𝒢 = F.baseChangePushforward f` is its own base change:
`𝒢 ⟶ 𝒢.baseChangePushforward f` is an isomorphism. -/
lemma isIso_toBaseChangePushforward_baseChangePushforward [Mono f] (F : Sheaf (J.over Y) A) :
    IsIso ((F.baseChangePushforward f).toBaseChangePushforward f) := by
  have : ∀ V : (Over Y)ᵒᵖ,
      IsIso (((F.baseChangePushforward f).toBaseChangePushforward f).hom.app V) := fun V => by
    rw [toBaseChangePushforward_hom_app]
    change IsIso (F.obj.map ((Over.map f).map ((Over.pullback f).map
      (baseChangeFst f V.unop))).op)
    rw [map_pullback_map_baseChangeFst]
    have := isIso_baseChangeFst f (T := (Over.map f).obj ((Over.pullback f).obj V.unop))
      (pullback.snd _ _) rfl
    infer_instance
  have h : IsIso ((F.baseChangePushforward f).toBaseChangePushforward f).hom :=
    NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf (J.over Y) A).map
      ((F.baseChangePushforward f).toBaseChangePushforward f)) := h
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

end Functor

section Sections

variable {X Y : C} (f : X ⟶ Y)

/-- The restriction maps of `(baseChangePushforwardFunctor f _).obj P`, on sections. -/
lemma baseChangePushforwardFunctor_obj_obj_map_apply (P : Sheaf (J.over Y) AddCommGrpCat.{v})
    {T T' : Over Y} (g : T ⟶ T')
    (x : ((baseChangePushforwardFunctor f AddCommGrpCat.{v}).obj P).obj.obj (op T')) :
    ((baseChangePushforwardFunctor f AddCommGrpCat.{v}).obj P).obj.map g.op x =
      P.obj.map ((Over.map f).map ((Over.pullback f).map g)).op x :=
  rfl

/-- The component of `toBaseChangePushforward` at `T`, on sections. -/
lemma toBaseChangePushforward_hom_app_apply (P : Sheaf (J.over Y) AddCommGrpCat.{v})
    (T : Over Y) (x : P.obj.obj (op T)) :
    (P.toBaseChangePushforward f).hom.app (op T) x = P.obj.map (baseChangeFst f T).op x :=
  rfl

end Sections

section FirstCohomology

open OverObjectCohomology

variable {X Y : C} (f : X ⟶ Y) [Mono f] [HasSheafify (J.over Y) AddCommGrpCat.{v}]

/-- A morphism `s` from the free abelian sheaf on `U` to `P.baseChangePushforward f`
corresponding to the same section as a morphism `q` from the free abelian sheaf on
`U ×_Y X` to `P` restricts along the first projection to `q` followed by
`P ⟶ P.baseChangePushforward f`, when `f` is a monomorphism. -/
lemma freeYonedaSheafMap_baseChangeFst_comp_eq {P : Sheaf (J.over Y) AddCommGrpCat.{v}}
    {U : Over Y}
    (q : freeYonedaSheaf (J.over Y) ((Over.map f).obj ((Over.pullback f).obj U)) ⟶ P)
    (s : freeYonedaSheaf (J.over Y) U ⟶ (baseChangePushforwardFunctor f _).obj P)
    (hs : freeYonedaSheafHomEquiv _ U _ s = freeYonedaSheafHomEquiv _ _ P q) :
    (presheafToSheaf (J.over Y) AddCommGrpCat.{v}).map
        (Functor.whiskerRight (yoneda.map (baseChangeFst f U)) AddCommGrpCat.free) ≫ s =
      q ≫ P.toBaseChangePushforward f := by
  apply (freeYonedaSheafHomEquiv (J.over Y) ((Over.map f).obj ((Over.pullback f).obj U))
    ((baseChangePushforwardFunctor f AddCommGrpCat.{v}).obj P)).injective
  rewrite [freeYonedaSheafHomEquiv_naturality_left, freeYonedaSheafHomEquiv_comp,
    baseChangePushforwardFunctor_obj_obj_map_apply, toBaseChangePushforward_hom_app_apply, hs,
    map_pullback_map_baseChangeFst]
  rfl

/-- **A first cohomology class over a base change that vanishes locally on the base comes from
the base.** Let `f : X ⟶ Y` be a monomorphism, `F` an abelian sheaf on `(Over Y, J.over Y)`
and `𝒢 = F.baseChangePushforward f`, the direct image of the restriction of `F` to the objects
over `X`. If a class `c ∈ H¹(U ×_Y X, 𝒢)` restricts to zero on `T ×_Y X` for every `T ⟶ U` in
a covering sieve of `U`, then `c` is the restriction along the first projection
`U ×_Y X ⟶ U` of a class in `H¹(U, 𝒢)`. This is the exactness of
`0 → H¹(U, π_* M) → H¹(π U, M) → H⁰(U, R¹π_* M)` at the middle term in the Leray spectral
sequence of `π = Over.pullback f`, with `M` the restriction of `F`. -/
theorem exists_baseChangeFst_cohomologyPresheaf_map_eq
    [EnoughInjectives (Sheaf (J.over Y) AddCommGrpCat.{v})]
    [HasExt.{w} (Sheaf (J.over Y) AddCommGrpCat.{v})]
    (F : Sheaf (J.over Y) AddCommGrpCat.{v}) (U : Over Y)
    (c : Sheaf.H' (F.baseChangePushforward f) 1 ((Over.map f).obj ((Over.pullback f).obj U)))
    (hc : ∃ R ∈ J.over Y U, ∀ ⦃T : Over Y⦄ (t : T ⟶ U), R t →
      ((F.baseChangePushforward f).cohomologyPresheaf 1).map
        ((Over.map f).map ((Over.pullback f).map t)).op c = 0) :
    ∃ d : Sheaf.H' (F.baseChangePushforward f) 1 U,
      ((F.baseChangePushforward f).cohomologyPresheaf 1).map (baseChangeFst f U).op d = c := by
  let K := J.over Y
  let Φ := baseChangePushforwardFunctor (J := J) f AddCommGrpCat.{v}
  let 𝒢 := F.baseChangePushforward f
  let W := (Over.map f).obj ((Over.pullback f).obj U)
  -- an injective embedding of `𝒢`, and its image under `Φ`
  let ι := Injective.ι 𝒢
  let S : ShortComplex (Sheaf K AddCommGrpCat.{v}) :=
    ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact := { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel ι) }
  have hSΦ : (S.map Φ).Exact :=
    hS.exact.map_of_mono_of_preservesKernel Φ hS.mono_f inferInstance
  let m := cokernel.desc (Φ.map ι) (Φ.map (cokernel.π ι)) (S.map Φ).zero
  have : Mono m := hSΦ.mono_cokernelDesc
  let S'' : ShortComplex (Sheaf K AddCommGrpCat.{v}) :=
    ShortComplex.mk (Φ.map ι) (cokernel.π (Φ.map ι)) (cokernel.condition _)
  have hS'' : S''.ShortExact :=
    { exact := S''.exact_of_g_is_cokernel (cokernelIsCokernel _) }
  let τ₃ : cokernel ι ⟶ cokernel (Φ.map ι) :=
    cokernel.desc ι ((Injective.under 𝒢).toBaseChangePushforward f ≫ cokernel.π (Φ.map ι))
      (by rw [← Category.assoc, ← toBaseChangePushforward_naturality, Category.assoc,
        cokernel.condition, comp_zero])
  let φ : S ⟶ S'' :=
    { τ₁ := 𝒢.toBaseChangePushforward f
      τ₂ := (Injective.under 𝒢).toBaseChangePushforward f
      τ₃ := τ₃
      comm₁₂ := toBaseChangePushforward_naturality f ι
      comm₂₃ := (cokernel.π_desc _ _ _).symm }
  have hnat : hS.extClass.comp (Ext.mk₀ (𝒢.toBaseChangePushforward f)) (add_zero 1) =
      (Ext.mk₀ τ₃).comp hS''.extClass (zero_add 1) :=
    hS.extClass_naturality hS'' φ
  have hτ₃m : τ₃ ≫ m = (cokernel ι).toBaseChangePushforward f := by
    apply coequalizer.hom_ext
    rw [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc,
      toBaseChangePushforward_naturality]
  -- `c` is the boundary of a section `q` of the cokernel over `U ×_Y X`
  obtain ⟨q, rfl⟩ := Torsors.ext_one_boundary_surjective S hS _ c
  -- the corresponding section of `Φ Q` over `U`
  obtain ⟨s, hs₀⟩ := (freeYonedaSheafHomEquiv K U (Φ.obj (cokernel ι))).surjective
    (freeYonedaSheafHomEquiv K W (cokernel ι) q)
  have hs : s ≫ cokernel.π m = 0 := by
    obtain ⟨R, hR, hRc⟩ := hc
    refine eq_zero_of_forall_freeYonedaSheaf_map_comp_eq_zero K _ R hR fun T t ht => ?_
    let t' := (Over.map f).map ((Over.pullback f).map t)
    obtain ⟨r, hr⟩ := (Torsors.ext_one_boundary_eq_zero_iff_lift S hS _
      ((presheafToSheaf K AddCommGrpCat.{v}).map
        (Functor.whiskerRight (yoneda.map t') AddCommGrpCat.free) ≫ q)).1 (by
      have h := (Torsors.cohomologyPresheaf_map_apply 𝒢 t'
        ((Ext.mk₀ q).comp hS.extClass (zero_add 1))).symm.trans (hRc t ht)
      rwa [Ext.mk₀_comp_mk₀_assoc] at h)
    obtain ⟨β, hβ₀⟩ := (freeYonedaSheafHomEquiv K T (Φ.obj (Injective.under 𝒢))).surjective
      (freeYonedaSheafHomEquiv K ((Over.map f).obj ((Over.pullback f).obj T)) _ r)
    have hβ : (presheafToSheaf K AddCommGrpCat.{v}).map
          (Functor.whiskerRight (yoneda.map t) AddCommGrpCat.free) ≫ s =
        β ≫ Φ.map (cokernel.π ι) := by
      apply (freeYonedaSheafHomEquiv K T _).injective
      rw [freeYonedaSheafHomEquiv_naturality_left, freeYonedaSheafHomEquiv_comp]
      rw [hs₀, hβ₀]
      rw [baseChangePushforwardFunctor_obj_obj_map, baseChangePushforwardFunctor_map_hom_app]
      have e₁ := freeYonedaSheafHomEquiv_naturality_left K t' (cokernel ι) q
      have e₂ := freeYonedaSheafHomEquiv_comp K _ r (cokernel.π ι)
      rw [hr] at e₂
      exact e₁.symm.trans e₂
    have hm0 : Φ.map (cokernel.π ι) ≫ cokernel.π m = 0 := by
      have : Φ.map (cokernel.π ι) = cokernel.π (Φ.map ι) ≫ m := (cokernel.π_desc _ _ _).symm
      rw [this, Category.assoc, cokernel.condition, comp_zero]
    rw [reassoc_of% hβ, hm0, comp_zero]
  let s'' := monoLift m s hs
  have hfst : (presheafToSheaf K AddCommGrpCat.{v}).map
      (Functor.whiskerRight (yoneda.map (baseChangeFst f U)) AddCommGrpCat.free) ≫ s'' =
        q ≫ τ₃ := by
    rw [← cancel_mono m, Category.assoc, monoLift_comp, Category.assoc, hτ₃m]
    exact freeYonedaSheafMap_baseChangeFst_comp_eq f q s hs₀
  have := isIso_toBaseChangePushforward_baseChangePushforward f F
  refine ⟨((Ext.mk₀ s'').comp hS''.extClass (zero_add 1)).comp
    (Ext.mk₀ (inv (𝒢.toBaseChangePushforward f))) (add_zero 1), ?_⟩
  exact (Torsors.cohomologyPresheaf_map_apply 𝒢 _ _).trans
    (Ext.mk₀_comp_comp_mk₀_inv_eq_of_comp_eq _ _ _ _ _ _ _ hfst hnat)

end FirstCohomology

end CategoryTheory.Sheaf
