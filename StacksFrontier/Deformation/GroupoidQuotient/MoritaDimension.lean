module

public import StacksFrontier.Deformation.Completed.PowerSeriesPoints
public import StacksFrontier.Deformation.GroupoidQuotient.ArrowCalculus
public import StacksFrontier.Deformation.Smooth.PowerSeries
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# The invariant `2 dim A - dim B` of a smooth prorepresentable groupoid in functors

Let `(U, R, s, t, c)` be a smooth groupoid in functors on `𝒞_Λ` whose functors of objects and of
arrows are prorepresented by Noetherian complete local `Λ`-algebras `A` and `B`. This file
proves that the integer `2 dim A - dim B` depends only on the quotient category `[U/R]`: if a
morphism of two such groupoids in functors induces an equivalence of quotients, the two
integers agree. This is the invariance under change of presentation in the proof of Stacks
0DSB.

## Main results

* `Deformation.GroupoidInFunctors.twoMul_ringKrullDim_sub_eq_of_quotientMap`: the invariance.

## Implementation notes

Let `F : G ⟶ H` be the morphism, with `G` presented by `(A, B)` and `H` by `(A', B')`, and let
`φ : A' ⟶ A`, `s', t' : A' ⟶ B'` and `s, t : A ⟶ B` be the morphisms inducing `F` on objects and
the source and target maps (Yoneda for `𝒞_Λ`, Stacks 06HD). Smoothness of `H` makes `s'` a power
series map in `n'` variables (Stacks 06HL). Put `Q = A[[x_1, …, x_{n'}]]`: its points are pairs of
a point `x` of `U` and an arrow of `H` with source the image of `x`, and the target of that arrow
is the morphism `ψ : A' ⟶ Q`. The map `ψ` is smooth — this is where fullness and essential
surjectivity of the induced functor on quotients and smoothness of both groupoids enter — so it
is a power series map in `m` variables, and `dim A + n' = dim Q = dim A' + m`. Finally fullness
and faithfulness identify the arrows of `G` with pairs of an object of `U` and a point of `Q`
with matching images in `H`, which makes `B` a power series ring over `A` in `m` variables. So
`2 dim A - dim B = dim A - m = dim A' - n' = 2 dim A' - dim B'`.

## References

* [Stacks Project, Tag 0DSB](https://stacks.math.columbia.edu/tag/0DSB)
* [Stacks Project, Tag 06HD](https://stacks.math.columbia.edu/tag/06HD)
* [Stacks Project, Tag 06HL](https://stacks.math.columbia.edu/tag/06HL)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Smoothness of a morphism of functors is invariant under conjugation by isomorphisms. -/
public theorem isSmooth_elementsBasedFunctor_conj
    {P P' Q Q' : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v} (α : P ⟶ Q) (eP : P ≅ P')
    (eQ : Q ≅ Q') (hα : IsSmooth (elementsBasedFunctor α)) :
    IsSmooth (elementsBasedFunctor (eP.inv ≫ α ≫ eQ.hom)) := by
  apply (isSmooth_elementsBasedFunctor_iff _).2
  intro B₀ A₀ f hf xA yB hxy
  have h' : α.app A₀ (eP.inv.app A₀ xA) = Q.map f (eQ.inv.app B₀ yB) := by
    have := congrArg (eQ.inv.app A₀) hxy
    simp only [NatTrans.comp_app, types_comp_apply] at this
    rw [Iso.hom_inv_id_app_apply] at this
    rw [this]
    exact NatTrans.naturality_apply eQ.inv f yB
  obtain ⟨xB, hxB, hαxB⟩ := (isSmooth_elementsBasedFunctor_iff α).1 hα f hf _ _ h'
  refine ⟨eP.hom.app B₀ xB, ?_, ?_⟩
  · rw [← NatTrans.naturality_apply eP.hom f xB, hxB, Iso.inv_hom_id_app_apply]
  · simp only [NatTrans.comp_app, types_comp_apply, Iso.hom_inv_id_app_apply, hαxB,
      Iso.inv_hom_id_app_apply]

/-- A natural transformation between prorepresented functors induced by a morphism `f`, read
through the representing isomorphisms, is precomposition with `f` on points. -/
public theorem comp_hom_app_eq_of_restrictedCoyonedaMap
    {X Y : CompleteLocalAlgCat.{u, v, w} Λ k}
    {P Q : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v}
    (eX : Q ≅ restrictedCoyoneda X) (eY : P ≅ restrictedCoyoneda Y) (α : P ⟶ Q) (f : X ⟶ Y)
    (hf : restrictedCoyonedaMap f = eY.inv ≫ α ≫ eX.hom) (T : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (p : P.obj T) : f ≫ eY.hom.app T p = eX.hom.app T (α.app T p) := by
  have h := congrArg (fun β => β.app T (eY.hom.app T p)) hf
  simp only [NatTrans.comp_app, types_comp_apply, Iso.hom_inv_id_app_apply] at h
  exact h

/-- A morphism of complete local algebras maps the maximal ideal into the maximal ideal. -/
public theorem CompleteLocalAlgCat.Hom.hom_mem_maximalIdeal
    {X T : CompleteLocalAlgCat.{u, v, w} Λ k} (b : X ⟶ T) {x : X}
    (hx : x ∈ maximalIdeal X) : b.hom x ∈ maximalIdeal T := by
  have : IsLocalHom b.hom.toRingHom := b.isLocal
  exact map_nonunit b.hom.toRingHom x hx

/-- The component of an isomorphism of functors to types is injective. -/
public theorem iso_hom_app_injective {C : Type*} [Category C] {P Q : C ⥤ Type v} (e : P ≅ Q)
    (T : C) : Function.Injective (e.hom.app T) := fun a b h => by
  simpa using congrArg (e.inv.app T) h

/-- The component of an isomorphism of functors to types is surjective. -/
private theorem iso_hom_app_surjective {C : Type*} [Category C] {P Q : C ⥤ Type v} (e : P ≅ Q)
    (T : C) (q : Q.obj T) : ∃ p, e.hom.app T p = q :=
  ⟨e.inv.app T q, Iso.inv_hom_id_app_apply e T q⟩

/-- A point `p` whose image under `P.map f` is the preimage of `y` maps to `y` along `f`. -/
private theorem hom_app_comp_map_eq {X : CompleteLocalAlgCat.{u, v, w} Λ k}
    {P : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v} (e : P ≅ restrictedCoyoneda X)
    {T₁ T : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : T₁ ⟶ T) (p : P.obj T₁)
    (y : X ⟶ artinianToComplete.obj T) (h : P.map f p = e.inv.app T y) :
    e.hom.app T₁ p ≫ artinianToComplete.map f = y := by
  change (restrictedCoyoneda X).map f (e.hom.app T₁ p) = y
  rw [← NatTrans.naturality_apply e.hom f p, h, Iso.inv_hom_id_app_apply]

/-- If `b` and `x` agree after restriction along `s` and `φ`, their preimages are matched by
`α` and `γ`. -/
private theorem app_inv_eq_of_comp_eq {X Y Z : CompleteLocalAlgCat.{u, v, w} Λ k}
    {P Q R : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v} (eX : Q ≅ restrictedCoyoneda X)
    (eY : P ≅ restrictedCoyoneda Y) (eZ : R ≅ restrictedCoyoneda Z) (α : P ⟶ Q) (γ : R ⟶ Q)
    (s : X ⟶ Y) (φ : X ⟶ Z) (hα : ∀ T p, s ≫ eY.hom.app T p = eX.hom.app T (α.app T p))
    (hγ : ∀ T p, φ ≫ eZ.hom.app T p = eX.hom.app T (γ.app T p))
    (T : ArtinianLocalAlgCat.{u, v, w} Λ k) (b : Y ⟶ artinianToComplete.obj T)
    (x : Z ⟶ artinianToComplete.obj T) (h : s ≫ b = φ ≫ x) :
    α.app T (eY.inv.app T b) = γ.app T (eZ.inv.app T x) := by
  apply iso_hom_app_injective eX T
  rw [← hα, ← hγ]
  simp only [Iso.inv_hom_id_app_apply, h]

namespace GroupoidInFunctors

/-- **The target-of-arrow map out of `A[[x_1, …, x_{n'}]]` is smooth.** In the situation of the
implementation notes, with `c` coordinates for the power series map `s' : A' ⟶ B'` and
`ρ : B' ⟶ Q` the morphism restricting to `φ` along `s'` and sending the coordinates to the
variables, the composite `ψ = t' ≫ ρ` induces a smooth morphism of restricted representable
functors. -/
public theorem isSmooth_restrictedRepresentableMap_targetPoint
    (G H : GroupoidInFunctors.{_, v, v} (ArtinianLocalAlgCat.{u, v, w} Λ k))
    (hG : GroupoidInFunctors.IsSmooth G) (hH : GroupoidInFunctors.IsSmooth H)
    {A A' B' : CompleteLocalAlgCat.{u, v, w} Λ k}
    (eA : G.objects ≅ restrictedCoyoneda A)
    (eA' : H.objects ≅ restrictedCoyoneda A') (eB' : H.arrows ≅ restrictedCoyoneda B')
    (F : G ⟶ H) [(quotientMap F).Full] [(quotientMap F).EssSurj]
    (sH tH : A' ⟶ B') (hsH : restrictedCoyonedaMap sH = eB'.inv ≫ H.source ≫ eA'.hom)
    (htH : restrictedCoyonedaMap tH = eB'.inv ≫ H.target ≫ eA'.hom)
    (φ : A' ⟶ A) (hφ : restrictedCoyonedaMap φ = eA.inv ≫ F.mapObjects ≫ eA'.hom)
    {n : ℕ} (c : Fin n → B') (hc : ∀ i, c i ∈ maximalIdeal B')
    (huniq : ∀ {T : CompleteLocalAlgCat.{u, v, w} Λ k} (b b' : B' ⟶ T), sH ≫ b = sH ≫ b' →
      (∀ i, b.hom (c i) = b'.hom (c i)) → b = b')
    (ρ : B' ⟶ mvPowerSeriesObject A n) (hρs : sH ≫ ρ = φ ≫ mvPowerSeriesCoeffMap A n)
    (hρc : ∀ i, ρ.hom (c i) = MvPowerSeries.X i) :
    Deformation.IsSmooth (restrictedRepresentableMap (tH ≫ ρ)) := by
  have : ∀ T, (F.evaluation T).Full := fun T => Hom.evaluation_full F T
  have hS := comp_hom_app_eq_of_restrictedCoyonedaMap eA' eB' H.source sH hsH
  have hT := comp_hom_app_eq_of_restrictedCoyonedaMap eA' eB' H.target tH htH
  have hΦ := comp_hom_app_eq_of_restrictedCoyonedaMap eA' eA F.mapObjects φ hφ
  show Deformation.IsSmooth (elementsBasedFunctor (restrictedCoyonedaMap (tH ≫ ρ)))
  apply (isSmooth_elementsBasedFunctor_iff _).2
  intro T₁ T f hf q a₁ hqa
  let x : A ⟶ artinianToComplete.obj T := mvPowerSeriesCoeffMap A n ≫ q
  let b : B' ⟶ artinianToComplete.obj T := ρ ≫ q
  let xh := eA.inv.app T x
  let bh := eB'.inv.app T b
  let y₁ := eA'.inv.app T₁ a₁
  have hbs : H.source.app T bh = F.mapObjects.app T xh :=
    app_inv_eq_of_comp_eq eA' eB' eA H.source F.mapObjects sH φ hS hΦ T b x
      (by simp only [b, x, ← Category.assoc, hρs])
  have hbt : H.target.app T bh = H.objects.map f y₁ := by
    apply iso_hom_app_injective eA' T
    rw [← hT, NatTrans.naturality_apply eA'.hom f y₁]
    simp only [bh, b, y₁, Iso.inv_hom_id_app_apply]
    rwa [← Category.assoc]
  obtain ⟨bh₁, hbh₁, hbh₁t⟩ := (isSmooth_elementsBasedFunctor_iff H.target).1 hH.2 f hf bh y₁ hbt
  let z := H.source.app T₁ bh₁
  have hz : H.objects.map f z = F.mapObjects.app T xh := by
    rw [← NatTrans.naturality_apply H.source f bh₁, hbh₁, hbs]
  obtain ⟨x₃, cc, hccs, hcct⟩ := Hom.exists_arrow_of_essSurj F T₁ z
  let cr := H.arrows.map f cc
  have hcrs : H.source.app T cr = F.mapObjects.app T (G.objects.map f x₃) := by
    rw [NatTrans.naturality_apply H.source f cc, hccs, NatTrans.naturality_apply F.mapObjects f x₃]
  have hcrt : H.target.app T cr = F.mapObjects.app T xh := by
    rw [NatTrans.naturality_apply H.target f cc, hcct, hz]
  obtain ⟨a, has, hat, hFa⟩ := Hom.exists_arrow_of_full F T _ xh cr hcrs hcrt
  obtain ⟨ah, hah, hahs⟩ := (isSmooth_elementsBasedFunctor_iff G.source).1 hG.1 f hf a x₃ has
  let x₁ := G.target.app T₁ ah
  have hx₁ : G.objects.map f x₁ = xh := by
    rw [← NatTrans.naturality_apply G.target f ah, hah, hat]
  let Fah := F.mapArrows.app T₁ ah
  have hFahs : H.source.app T₁ Fah = F.mapObjects.app T₁ x₃ := by
    rw [F.map_source, hahs]
  have hFaht : H.target.app T₁ Fah = F.mapObjects.app T₁ x₁ := F.map_target T₁ ah
  let ih := inverseArrow H T₁ Fah
  have hc₂ : H.source.app T₁ cc = H.target.app T₁ ih := by
    rw [hccs, inverseArrow_target, hFahs]
  let c₂ := H.compose T₁ cc ih hc₂
  have hb₂ : H.source.app T₁ bh₁ = H.target.app T₁ c₂ := by
    rw [compose_target_eq, hcct]
  let b₂ := H.compose T₁ bh₁ c₂ hb₂
  have hb₂s : H.source.app T₁ b₂ = F.mapObjects.app T₁ x₁ := by
    rw [compose_source_eq, compose_source_eq, inverseArrow_source, hFaht]
  have hb₂t : H.target.app T₁ b₂ = y₁ := by
    rw [compose_target_eq, hbh₁t]
  have hmapFah : H.arrows.map f Fah = cr := by
    rw [← NatTrans.naturality_apply F.mapArrows f ah, hah, hFa]
  have hb₂map : H.arrows.map f b₂ = bh := by
    have hc₂' : H.source.app T (H.arrows.map f cc) =
        H.target.app T (H.arrows.map f ih) := by
      rw [NatTrans.naturality_apply H.source f, NatTrans.naturality_apply H.target f, hc₂]
    have hb₂' : H.source.app T (H.arrows.map f bh₁) =
        H.target.app T (H.arrows.map f c₂) := by
      rw [NatTrans.naturality_apply H.source f, NatTrans.naturality_apply H.target f, hb₂]
    have hih : H.arrows.map f ih = inverseArrow H T cr := by
      rw [inverseArrow_natural, hmapFah]
    have hinv : H.compose T (H.arrows.map f cc) (H.arrows.map f ih) hc₂' =
        H.identity T (H.source.app T bh) := by
      rw [compose_congr' H T rfl hih hc₂' (by rw [inverseArrow_target]),
        compose_inverseArrow, hcrt, hbs]
    have hc₂map : H.arrows.map f c₂ = H.identity T (H.source.app T bh) :=
      (arrows_map_compose H f _ _ hc₂ hc₂').trans hinv
    rw [arrows_map_compose H f _ _ hb₂ hb₂',
      compose_congr' H T hbh₁ hc₂map hb₂' (by rw [identity_target_eq]), compose_identity_eq]
  let q₁ : mvPowerSeriesObject A n ⟶ artinianToComplete.obj T₁ :=
    mvPowerSeriesLift (eA.hom.app T₁ x₁) (fun i => (eB'.hom.app T₁ b₂).hom (c i))
      (fun i => CompleteLocalAlgCat.Hom.hom_mem_maximalIdeal _ (hc i))
  have hρq₁ : ρ ≫ q₁ = eB'.hom.app T₁ b₂ := by
    apply huniq
    · rw [← Category.assoc, hρs, Category.assoc, mvPowerSeriesCoeffMap_comp_lift, hΦ, hS, hb₂s]
    · intro i
      rw [CompleteLocalAlgCat.comp_hom, AlgHom.comp_apply, hρc, mvPowerSeriesLift_hom_X]
  refine ⟨q₁, ?_, ?_⟩
  · apply mvPowerSeriesObject_hom_ext
    · show mvPowerSeriesCoeffMap A n ≫ q₁ ≫ artinianToComplete.map f = x
      rw [← Category.assoc, mvPowerSeriesCoeffMap_comp_lift]
      exact hom_app_comp_map_eq eA f x₁ x hx₁
    · intro i
      show (artinianToComplete.map f).hom (q₁.hom (MvPowerSeries.X i)) = q.hom (MvPowerSeries.X i)
      rw [mvPowerSeriesLift_hom_X]
      have h1 := hom_app_comp_map_eq eB' f b₂ b hb₂map
      have h2 := congrArg (fun g : B' ⟶ artinianToComplete.obj T => g.hom (c i)) h1
      simp only [CompleteLocalAlgCat.comp_hom, AlgHom.comp_apply] at h2
      rw [h2]
      show (ρ ≫ q).hom (c i) = _
      rw [CompleteLocalAlgCat.comp_hom, AlgHom.comp_apply, hρc]
  · show (tH ≫ ρ) ≫ q₁ = a₁
    rw [Category.assoc, hρq₁, hT, hb₂t, Iso.inv_hom_id_app_apply]

/-- **The arrows of `G` form a power series ring over `A`.** In the situation of the
implementation notes, with `ψ = t' ≫ ρ` a power series map with coordinates `d`, and
`θ : Q ⟶ B` the morphism restricting to `s` and sending the variables to the images of the
coordinates of `s'`, the morphism `A[[x_1, …, x_m]] ⟶ B` restricting to `t` and sending the
variables to `θ(d_j)` is an isomorphism. -/
public theorem isIso_arrowsPowerSeriesMap
    (G H : GroupoidInFunctors.{_, v, v} (ArtinianLocalAlgCat.{u, v, w} Λ k))
    {A B A' B' : CompleteLocalAlgCat.{u, v, w} Λ k}
    (eA : G.objects ≅ restrictedCoyoneda A) (eB : G.arrows ≅ restrictedCoyoneda B)
    (eA' : H.objects ≅ restrictedCoyoneda A') (eB' : H.arrows ≅ restrictedCoyoneda B')
    (F : G ⟶ H) [(quotientMap F).Full] [(quotientMap F).Faithful]
    (sG tG : A ⟶ B) (hsG : restrictedCoyonedaMap sG = eB.inv ≫ G.source ≫ eA.hom)
    (htG : restrictedCoyonedaMap tG = eB.inv ≫ G.target ≫ eA.hom)
    (sH tH : A' ⟶ B') (hsH : restrictedCoyonedaMap sH = eB'.inv ≫ H.source ≫ eA'.hom)
    (htH : restrictedCoyonedaMap tH = eB'.inv ≫ H.target ≫ eA'.hom)
    (φ : A' ⟶ A) (hφ : restrictedCoyonedaMap φ = eA.inv ≫ F.mapObjects ≫ eA'.hom)
    (χ : B' ⟶ B) (hχ : restrictedCoyonedaMap χ = eB.inv ≫ F.mapArrows ≫ eB'.hom)
    {n : ℕ} (c : Fin n → B') (hc : ∀ i, c i ∈ maximalIdeal B')
    (huniq : ∀ {T : CompleteLocalAlgCat.{u, v, w} Λ k} (b b' : B' ⟶ T), sH ≫ b = sH ≫ b' →
      (∀ i, b.hom (c i) = b'.hom (c i)) → b = b')
    (ρ : B' ⟶ mvPowerSeriesObject A n) (hρs : sH ≫ ρ = φ ≫ mvPowerSeriesCoeffMap A n)
    (hρc : ∀ i, ρ.hom (c i) = MvPowerSeries.X i)
    {m : ℕ} (d : Fin m → mvPowerSeriesObject A n)
    (hd : ∀ j, d j ∈ maximalIdeal (mvPowerSeriesObject A n))
    (huniqψ : ∀ {T : CompleteLocalAlgCat.{u, v, w} Λ k} (b b' : mvPowerSeriesObject A n ⟶ T),
      (tH ≫ ρ) ≫ b = (tH ≫ ρ) ≫ b' → (∀ j, b.hom (d j) = b'.hom (d j)) → b = b')
    (hexistψ : ∀ {T : CompleteLocalAlgCat.{u, v, w} Λ k} (g : A' ⟶ T) (x : Fin m → T),
      (∀ j, x j ∈ maximalIdeal T) → ∃ b : mvPowerSeriesObject A n ⟶ T,
        (tH ≫ ρ) ≫ b = g ∧ ∀ j, b.hom (d j) = x j)
    (θ : mvPowerSeriesObject A n ⟶ B) (hθC : mvPowerSeriesCoeffMap A n ≫ θ = sG)
    (hθX : ∀ i, θ.hom (MvPowerSeries.X i) = χ.hom (c i)) :
    IsIso (mvPowerSeriesLift tG (fun j => θ.hom (d j))
      (fun j => CompleteLocalAlgCat.Hom.hom_mem_maximalIdeal θ (hd j))) := by
  have : ∀ T, (F.evaluation T).Full := fun T => Hom.evaluation_full F T
  have : ∀ T, (F.evaluation T).Faithful := fun T => Hom.evaluation_faithful F T
  have hSG := comp_hom_app_eq_of_restrictedCoyonedaMap eA eB G.source sG hsG
  have hTG := comp_hom_app_eq_of_restrictedCoyonedaMap eA eB G.target tG htG
  have hSH := comp_hom_app_eq_of_restrictedCoyonedaMap eA' eB' H.source sH hsH
  have hTH := comp_hom_app_eq_of_restrictedCoyonedaMap eA' eB' H.target tH htH
  have hΦ := comp_hom_app_eq_of_restrictedCoyonedaMap eA' eA F.mapObjects φ hφ
  have hX := comp_hom_app_eq_of_restrictedCoyonedaMap eB' eB F.mapArrows χ hχ
  -- the morphism `F` commutes with sources and targets
  have hsχ : sH ≫ χ = φ ≫ sG := by
    apply (restrictedCoyonedaMap_bijective A' B).1
    ext T g
    obtain ⟨p, rfl⟩ := iso_hom_app_surjective eB T g
    show (sH ≫ χ) ≫ eB.hom.app T p = (φ ≫ sG) ≫ eB.hom.app T p
    rw [Category.assoc, Category.assoc, hX, hSH, hSG, hΦ, F.map_source]
  have htχ : tH ≫ χ = φ ≫ tG := by
    apply (restrictedCoyonedaMap_bijective A' B).1
    ext T g
    obtain ⟨p, rfl⟩ := iso_hom_app_surjective eB T g
    show (tH ≫ χ) ≫ eB.hom.app T p = (φ ≫ tG) ≫ eB.hom.app T p
    rw [Category.assoc, Category.assoc, hX, hTH, hTG, hΦ, F.map_target]
  -- `θ` restricts to `χ` along `ρ`
  have hρθ : ρ ≫ θ = χ := by
    apply huniq
    · rw [← Category.assoc, hρs, Category.assoc, hθC, hsχ]
    · intro i
      rw [CompleteLocalAlgCat.comp_hom, AlgHom.comp_apply, hρc, hθX]
  have hψθ : (tH ≫ ρ) ≫ θ = φ ≫ tG := by rw [Category.assoc, hρθ, htχ]
  let L := mvPowerSeriesLift tG (fun j => θ.hom (d j))
    (fun j => CompleteLocalAlgCat.Hom.hom_mem_maximalIdeal θ (hd j))
  -- `θ ≫ g` is determined by `g` restricted along `s` and along `χ`
  have hθext : ∀ {T : CompleteLocalAlgCat.{u, v, w} Λ k} (g : B ⟶ T)
      (q : mvPowerSeriesObject A n ⟶ T), sG ≫ g = mvPowerSeriesCoeffMap A n ≫ q →
      χ ≫ g = ρ ≫ q → θ ≫ g = q := by
    intro T g q h1 h2
    apply mvPowerSeriesObject_hom_ext
    · rw [← Category.assoc, hθC, h1]
    · intro i
      show g.hom (θ.hom (MvPowerSeries.X i)) = q.hom (MvPowerSeries.X i)
      rw [hθX]
      simpa only [CompleteLocalAlgCat.comp_hom, AlgHom.comp_apply, hρc] using
        congrArg (fun φ : B' ⟶ T => φ.hom (c i)) h2
  apply isIso_of_restrictedCoyonedaMap_app_bijective
  intro T
  constructor
  · intro g g' hgg
    change L ≫ g = L ≫ g' at hgg
    have h1 : tG ≫ g = tG ≫ g' := by
      simpa only [← Category.assoc, L, mvPowerSeriesCoeffMap_comp_lift] using
        congrArg (fun φ => mvPowerSeriesCoeffMap A m ≫ φ) hgg
    have h2 : θ ≫ g = θ ≫ g' := by
      apply huniqψ
      · rw [← Category.assoc, ← Category.assoc, hψθ, Category.assoc, Category.assoc, h1]
      · intro j
        have := congrArg (fun φ : mvPowerSeriesObject A m ⟶ _ => φ.hom (MvPowerSeries.X j)) hgg
        change g.hom (L.hom (MvPowerSeries.X j)) = g'.hom (L.hom (MvPowerSeries.X j)) at this
        rwa [mvPowerSeriesLift_hom_X] at this
    have h3 : sG ≫ g = sG ≫ g' := by rw [← hθC, Category.assoc, Category.assoc, h2]
    have h4 : χ ≫ g = χ ≫ g' := by rw [← hρθ, Category.assoc, Category.assoc, h2]
    obtain ⟨p, rfl⟩ := iso_hom_app_surjective eB T g
    obtain ⟨p', rfl⟩ := iso_hom_app_surjective eB T g'
    congr 1
    refine Hom.eq_of_faithful F T p p' ?_ ?_ ?_
    · apply iso_hom_app_injective eA T
      rw [← hSG, ← hSG, h3]
    · apply iso_hom_app_injective eA T
      rw [← hTG, ← hTG, h1]
    · apply iso_hom_app_injective eB' T
      rw [← hX, ← hX, h4]
  · intro a
    let xt : A ⟶ artinianToComplete.obj T := mvPowerSeriesCoeffMap A m ≫ a
    obtain ⟨q, hq, hqd⟩ := hexistψ (φ ≫ xt) (fun j => a.hom (MvPowerSeries.X j))
      (fun j => CompleteLocalAlgCat.Hom.hom_mem_maximalIdeal a
        (mvPowerSeries_X_mem_maximalIdeal j))
    let xs : A ⟶ artinianToComplete.obj T := mvPowerSeriesCoeffMap A n ≫ q
    let bb : B' ⟶ artinianToComplete.obj T := ρ ≫ q
    have hbs : H.source.app T (eB'.inv.app T bb) = F.mapObjects.app T (eA.inv.app T xs) :=
      app_inv_eq_of_comp_eq eA' eB' eA H.source F.mapObjects sH φ hSH hΦ T bb xs
        (by simp only [bb, xs, ← Category.assoc, hρs])
    have hbt : H.target.app T (eB'.inv.app T bb) = F.mapObjects.app T (eA.inv.app T xt) :=
      app_inv_eq_of_comp_eq eA' eB' eA H.target F.mapObjects tH φ hTH hΦ T bb xt
        (by simp only [bb, ← Category.assoc, hq])
    obtain ⟨p, hps, hpt, hFp⟩ := Hom.exists_arrow_of_full F T _ _ _ hbs hbt
    refine ⟨eB.hom.app T p, ?_⟩
    show L ≫ eB.hom.app T p = a
    have hθq : θ ≫ eB.hom.app T p = q := by
      apply hθext
      · rw [hSG, hps, Iso.inv_hom_id_app_apply]
      · rw [hX, hFp, Iso.inv_hom_id_app_apply]
    apply mvPowerSeriesObject_hom_ext
    · rw [← Category.assoc, mvPowerSeriesCoeffMap_comp_lift, hTG, hpt, Iso.inv_hom_id_app_apply]
    · intro j
      show (eB.hom.app T p).hom (L.hom (MvPowerSeries.X j)) = a.hom (MvPowerSeries.X j)
      rw [mvPowerSeriesLift_hom_X, ← hqd j, ← hθq]
      rfl

/-- **Stacks 0DSB, invariance under change of presentation.** Let `G` and `H` be smooth groupoids
in functors on `𝒞_Λ` whose functors of objects and of arrows are prorepresented by `A, B` and by
`A', B'`, and let `F : G ⟶ H` induce an equivalence of quotient categories (full, faithful and
essentially surjective). Then `2 dim A - dim B = 2 dim A' - dim B'`, all four dimensions being
finite. -/
public theorem twoMul_ringKrullDim_sub_eq_of_quotientMap
    (G H : GroupoidInFunctors.{_, v, v} (ArtinianLocalAlgCat.{u, v, w} Λ k))
    (hG : GroupoidInFunctors.IsSmooth G) (hH : GroupoidInFunctors.IsSmooth H)
    {A B A' B' : CompleteLocalAlgCat.{u, v, w} Λ k}
    (eA : G.objects ≅ restrictedCoyoneda A) (eB : G.arrows ≅ restrictedCoyoneda B)
    (eA' : H.objects ≅ restrictedCoyoneda A') (eB' : H.arrows ≅ restrictedCoyoneda B')
    (F : G ⟶ H) [(quotientMap F).Full] [(quotientMap F).Faithful] [(quotientMap F).EssSurj] :
    ∃ a b a' b' : ℕ, ringKrullDim A = a ∧ ringKrullDim B = b ∧ ringKrullDim A' = a' ∧
      ringKrullDim B' = b' ∧ 2 * a + b' = 2 * a' + b := by
  obtain ⟨sG, hsG⟩ := (restrictedCoyonedaMap_bijective A B).2 (eB.inv ≫ G.source ≫ eA.hom)
  obtain ⟨tG, htG⟩ := (restrictedCoyonedaMap_bijective A B).2 (eB.inv ≫ G.target ≫ eA.hom)
  obtain ⟨sH, hsH⟩ := (restrictedCoyonedaMap_bijective A' B').2 (eB'.inv ≫ H.source ≫ eA'.hom)
  obtain ⟨tH, htH⟩ := (restrictedCoyonedaMap_bijective A' B').2 (eB'.inv ≫ H.target ≫ eA'.hom)
  obtain ⟨φ, hφ⟩ := (restrictedCoyonedaMap_bijective A' A).2 (eA.inv ≫ F.mapObjects ≫ eA'.hom)
  obtain ⟨χ, hχ⟩ := (restrictedCoyonedaMap_bijective B' B).2 (eB.inv ≫ F.mapArrows ≫ eB'.hom)
  have hsHsmooth : Deformation.IsSmooth (restrictedRepresentableMap sH) := by
    have h := isSmooth_elementsBasedFunctor_conj H.source eB' eA' hH.1
    rwa [← hsH] at h
  obtain ⟨n, c, hc, hdimB', huniq, hexist⟩ :=
    ((restrictedRepresentableMap_isSmooth_iff_isPowerSeriesOver sH).mp hsHsmooth).exists_coordinates
  obtain ⟨ρ, hρs, hρc⟩ := hexist (φ ≫ mvPowerSeriesCoeffMap A n) (fun i => MvPowerSeries.X i)
    (fun i => mvPowerSeries_X_mem_maximalIdeal i)
  have hψ := isSmooth_restrictedRepresentableMap_targetPoint G H hG hH eA eA' eB' F sH tH hsH htH
    φ hφ c hc huniq ρ hρs hρc
  obtain ⟨m, d, hd, hdimQ, huniqψ, hexistψ⟩ :=
    ((restrictedRepresentableMap_isSmooth_iff_isPowerSeriesOver (tH ≫ ρ)).mp hψ).exists_coordinates
  let θ : mvPowerSeriesObject A n ⟶ B := mvPowerSeriesLift sG (fun i => χ.hom (c i))
    (fun i => CompleteLocalAlgCat.Hom.hom_mem_maximalIdeal χ (hc i))
  have hL := isIso_arrowsPowerSeriesMap G H eA eB eA' eB' F sG tG hsG htG sH tH hsH htH φ hφ χ hχ
    c hc huniq ρ hρs hρc d hd huniqψ hexistψ θ (mvPowerSeriesCoeffMap_comp_lift _ _ _)
    (fun i => mvPowerSeriesLift_hom_X _ _ _ i)
  have hdimB : ringKrullDim B = ringKrullDim A + m :=
    (ringKrullDim_eq_of_isIso (mvPowerSeriesLift tG (fun j => θ.hom (d j))
      (fun j => CompleteLocalAlgCat.Hom.hom_mem_maximalIdeal θ (hd j)))).symm.trans
      (MvPowerSeries.ringKrullDim_fin_eq_add A m)
  have hdimQ' : ringKrullDim (mvPowerSeriesObject A n) = ringKrullDim A + n :=
    MvPowerSeries.ringKrullDim_fin_eq_add A n
  obtain ⟨a, ha⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim A
  obtain ⟨a', ha'⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim A'
  refine ⟨a, a + m, a', a' + n, ha, ?_, ha', ?_, ?_⟩
  · rw [hdimB, ha]; push_cast; rfl
  · rw [hdimB', ha']; push_cast; rfl
  · have key : ((a + n : ℕ) : WithBot ℕ∞) = ((a' + m : ℕ) : WithBot ℕ∞) := by
      push_cast
      rw [← ha, ← ha', ← hdimQ', hdimQ]
    have key' : a + n = a' + m := mod_cast key
    omega

end GroupoidInFunctors

end Deformation

end
