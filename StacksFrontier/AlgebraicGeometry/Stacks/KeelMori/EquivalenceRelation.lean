module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.Relation
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# `∐ N i j ⇉ ∐ M i` is an étale equivalence relation (the claim in the proof of Stacks 0DUT)

For a small Keel–Mori cover `C`, the pair `sR, tR : R = ∐ N i j ⇉ U = ∐ M i` is an étale
equivalence relation: `R ⟶ U ×_S U` is a monomorphism, being unramified and injective on
geometric points (Stacks 0DT7, first half, with the geometric points computed by
`AlgebraicGeometry.Stack.KeelMoriCover.eq_of_comp_s_eq_of_comp_t_eq`), and the relation it
induces on `T`-points is an equivalence relation, its identity, inverse and composition being the
morphisms `e`, `inv`, `comp` glued over the pieces.

## Main definitions

* `AlgebraicGeometry.Stack.KeelMoriCover.eR`, `.invR`, `.compR`
* `AlgebraicGeometry.Stack.KeelMoriCover.rel`: the pre-relation `R ⟶ U ×_S U` of Stacks 02WW.

## Main results

* `AlgebraicGeometry.Stack.KeelMoriCover.isEtaleEquivalenceRelation_rel`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

namespace AlgebraicGeometry.Stack.KeelMoriCover

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {C : KeelMoriCover B S hS 𝒳} (hC : C.IsSmall)

/-! ### Geometric points of `U` and `R` -/

/-- Equal composites in the site have equal images on points. -/
private theorem map_apply_eq_of_comp_eq {W X X' Y : BigFppfOver B S hS} {a : W ⟶ X} {b : X ⟶ Y}
    {a' : W ⟶ X'} {b' : X' ⟶ Y} (h : a ≫ b = a' ≫ b')
    (w : (BigFppfOver.toScheme B S hS).obj W) :
    (BigFppfOver.toScheme B S hS).map b ((BigFppfOver.toScheme B S hS).map a w) =
      (BigFppfOver.toScheme B S hS).map b' ((BigFppfOver.toScheme B S hS).map a' w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Functor.map_comp, h]

/-- An object of the site whose underlying scheme is a field spectrum has a single point. -/
theorem eq_of_isSpec {V : BigFppfOver B S hS} {k : Type u} [Field k]
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (y y' : (BigFppfOver.toScheme B S hS).obj V) : y = y' := by
  have h : e.hom y = e.hom y' := Subsingleton.elim _ _
  have hy (y) : e.inv (e.hom y) = y := by rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl
  rw [← hy y, ← hy y', h]

/-- The inclusion of a piece `M i` into `U` is a monomorphism. -/
theorem mono_ιU (i : C.ι) : Mono (ιU hC i) :=
  (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance

/-- The inclusion of a piece `N i j` into `R` is a monomorphism. -/
theorem mono_ιR (p : C.ι × C.ι) : Mono (ιR hC p) :=
  (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance

/-- A morphism to `R` out of a field spectrum factors through one of the pieces `N i j`. -/
theorem exists_factor_ιR {V : BigFppfOver B S hS} {k : Type u} [Field k]
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) (g : V ⟶ R hC) :
    ∃ (p : C.ι × C.ι) (n : V ⟶ C.N p.1 p.2), n ≫ ιR hC p = g := by
  obtain ⟨y₀⟩ : Nonempty ((BigFppfOver.toScheme B S hS).obj V) := ⟨e.inv default⟩
  obtain ⟨p, hp⟩ := cover_ιR hC ((BigFppfOver.toScheme B S hS).map g y₀)
  exact ⟨p, BigFppfOver.exists_factor_of_range_le (ιR hC p) inferInstance g (by
    rintro _ ⟨y, rfl⟩
    rw [eq_of_isSpec e y y₀]
    exact hp)⟩

/-- Two morphisms out of a field spectrum into two pieces `M i`, `M i'` of `U` with the same
composite to `U` lie in the same piece. -/
theorem eq_of_comp_ιU_eq {V : BigFppfOver B S hS} {k : Type u} [Field k]
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) {i i' : C.ι} (n : V ⟶ C.M i)
    (n' : V ⟶ C.M i') (h : n ≫ ιU hC i = n' ≫ ιU hC i') : i = i' := by
  by_contra hne
  obtain ⟨y₀⟩ : Nonempty ((BigFppfOver.toScheme B S hS).obj V) := ⟨e.inv default⟩
  refine disjoint_ιU hC hne ((BigFppfOver.toScheme B S hS).map n y₀)
    ((BigFppfOver.toScheme B S hS).map n' y₀) (map_apply_eq_of_comp_eq h y₀)

/-- **`R (k) ⟶ U (k) × U (k)` is injective** for an algebraically closed field `k`. -/
theorem eq_of_comp_sR_eq_of_comp_tR_eq (k : Type u) [Field k] [IsAlgClosed k]
    (V : BigFppfOver B S hS) (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (g₁ g₂ : V ⟶ R hC) (hs : g₁ ≫ sR hC = g₂ ≫ sR hC) (ht : g₁ ≫ tR hC = g₂ ≫ tR hC) :
    g₁ = g₂ := by
  obtain ⟨p, n₁, rfl⟩ := exists_factor_ιR hC e g₁
  obtain ⟨p', n₂, rfl⟩ := exists_factor_ιR hC e g₂
  rw [Category.assoc, Category.assoc, ιR_sR, ιR_sR, ← Category.assoc, ← Category.assoc] at hs
  rw [Category.assoc, Category.assoc, ιR_tR, ιR_tR, ← Category.assoc, ← Category.assoc] at ht
  have h₁ := eq_of_comp_ιU_eq hC e _ _ hs
  have h₂ := eq_of_comp_ιU_eq hC e _ _ ht
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := p'
  dsimp only at h₁ h₂ n₁ n₂ hs ht ⊢
  subst h₁ h₂
  rw [C.eq_of_comp_s_eq_of_comp_t_eq k V e n₁ n₂ ((mono_ιU hC a).right_cancellation _ _ hs)
    ((mono_ιU hC b).right_cancellation _ _ ht)]

/-! ### The pre-relation -/

/-- **The pre-relation `R ⟶ U ×_S U`** of the étale equivalence relation, with target `sR` and
source `tR`, in the form of Stacks 02WW. -/
noncomputable abbrev rel := Space.relation B S hS (tR hC) (sR hC)

/-- The target of the pre-relation is `sR`. -/
theorem rel_target : (rel hC).target = (Over.post B.inclusion).map (sR hC) := prod.lift_fst _ _

/-- The source of the pre-relation is `tR`. -/
theorem rel_source : (rel hC).source = (Over.post B.inclusion).map (tR hC) := prod.lift_snd _ _

/-- The underlying morphism of schemes of `R ⟶ U ×_S U` is unramified, its composite with the
first projection being the étale morphism `sR`. -/
instance unramified_rel_left : Unramified (rel hC).left := by
  have : Unramified ((rel hC).left ≫ (prod.fst : (Over.post B.inclusion).obj (U hC) ⨯
      (Over.post B.inclusion).obj (U hC) ⟶ _).left) := by
    rw [← Over.comp_left]
    change Unramified (rel hC).target.left
    rw [rel_target]
    exact unramified_of_etale ((BigFppfOver.toScheme B S hS).map (sR hC))
  exact unramified_of_comp (rel hC).left (prod.fst : (Over.post B.inclusion).obj (U hC) ⨯
      (Over.post B.inclusion).obj (U hC) ⟶ _).left

/-- **`R ⟶ U ×_S U` is a monomorphism.** -/
theorem mono_rel : Mono (rel hC) := by
  let ρ : (BigFppfOver.toScheme B S hS).obj (R hC) ⟶
      ((Over.post B.inclusion).obj (U hC) ⨯ (Over.post B.inclusion).obj (U hC)).left :=
    (rel hC).left
  let fstL : ((Over.post B.inclusion).obj (U hC) ⨯ (Over.post B.inclusion).obj (U hC)).left ⟶
      (BigFppfOver.toScheme B S hS).obj (U hC) :=
    (prod.fst : _ ⟶ (Over.post B.inclusion).obj (U hC)).left
  let sndL : ((Over.post B.inclusion).obj (U hC) ⨯ (Over.post B.inclusion).obj (U hC)).left ⟶
      (BigFppfOver.toScheme B S hS).obj (U hC) :=
    (prod.snd : _ ⟶ (Over.post B.inclusion).obj (U hC)).left
  have hρs : ρ ≫ fstL = (BigFppfOver.toScheme B S hS).map (sR hC) :=
    congrArg Over.Hom.left (rel_target hC)
  have hρt : ρ ≫ sndL = (BigFppfOver.toScheme B S hS).map (tR hC) :=
    congrArg Over.Hom.left (rel_source hC)
  have : Unramified ρ := unramified_rel_left hC
  have hmono : Mono ρ := by
    refine mono_of_unramified_of_injective_geometricPoints ρ B.aleph0_lt_cutoff
      (Scheme.size_pullback_lt _ _ (R hC).left.2 (R hC).left.2) ?_
    intro k _ _ hk a b hab
    have hs : a ≫ (BigFppfOver.toScheme B S hS).map (sR hC) =
        b ≫ (BigFppfOver.toScheme B S hS).map (sR hC) := by
      rw [← hρs, reassoc_of% hab]
    have ht : a ≫ (BigFppfOver.toScheme B S hS).map (tR hC) =
        b ≫ (BigFppfOver.toScheme B S hS).map (tR hC) := by
      rw [← hρt, reassoc_of% hab]
    have hab' : a ≫ B.inclusion.map (R hC).hom = b ≫ B.inclusion.map (R hC).hom :=
      calc a ≫ B.inclusion.map (R hC).hom
          = (a ≫ (BigFppfOver.toScheme B S hS).map (sR hC)) ≫ B.inclusion.map (U hC).hom := by
            rw [Category.assoc, BigFppfOver.toScheme_map_comp_hom]
        _ = (b ≫ (BigFppfOver.toScheme B S hS).map (sR hC)) ≫ B.inclusion.map (U hC).hom := by
            rw [hs]
        _ = b ≫ B.inclusion.map (R hC).hom := by
            rw [Category.assoc, BigFppfOver.toScheme_map_comp_hom]
    obtain ⟨V, e, ah, bh, hah, hbh⟩ := BigFppfOver.exists_homs_of_spec hk a b hab'
    have key := eq_of_comp_sR_eq_of_comp_tR_eq hC k V e ah bh
      ((BigFppfOver.toScheme B S hS).map_injective (by
        rw [Functor.map_comp, Functor.map_comp, hah, hbh, Category.assoc, Category.assoc, hs]))
      ((BigFppfOver.toScheme B S hS).map_injective (by
        rw [Functor.map_comp, Functor.map_comp, hah, hbh, Category.assoc, Category.assoc, ht]))
    exact (cancel_epi e.hom).1 (by rw [← hah, ← hbh, key])
  exact @Over.mono_of_mono_left _ _ _ _ _ (rel hC) hmono

/-! ### Identity and inverse -/

/-- **The identity `eR : U ⟶ R`**, equal to `e i` on `M i`. -/
noncomputable def eR : U hC ⟶ R hC := (exists_desc_U hC fun i => C.e i ≫ ιR hC (i, i)).choose

/-- On the piece `M i`, `eR` is `e i` followed by the inclusion of `N i i`. -/
theorem ιU_eR (i : C.ι) : ιU hC i ≫ eR hC = C.e i ≫ ιR hC (i, i) :=
  (exists_desc_U hC fun i => C.e i ≫ ιR hC (i, i)).choose_spec i

/-- `eR` is a section of `sR`. -/
theorem eR_sR : eR hC ≫ sR hC = 𝟙 _ := hom_ext_U hC fun i => by
  rw [reassoc_of% (ιU_eR hC i), ιR_sR, Category.comp_id]
  exact (reassoc_of% (C.e_comp_s i)) _

/-- `eR` is a section of `tR`. -/
theorem eR_tR : eR hC ≫ tR hC = 𝟙 _ := hom_ext_U hC fun i => by
  rw [reassoc_of% (ιU_eR hC i), ιR_tR, Category.comp_id]
  exact (reassoc_of% (C.e_comp_t i)) _

/-- **The inverse `invR : R ⟶ R`**, equal to `inv i j` on `N i j`. -/
noncomputable def invR : R hC ⟶ R hC :=
  (exists_desc_R hC fun p => C.inv p.1 p.2 ≫ ιR hC (p.2, p.1)).choose

/-- On the piece `N i j`, `invR` is `inv i j` followed by the inclusion of `N j i`. -/
theorem ιR_invR (p : C.ι × C.ι) : ιR hC p ≫ invR hC = C.inv p.1 p.2 ≫ ιR hC (p.2, p.1) :=
  (exists_desc_R hC fun p => C.inv p.1 p.2 ≫ ιR hC (p.2, p.1)).choose_spec p

/-- `invR` exchanges `sR` and `tR`: `invR ≫ sR = tR`. -/
theorem invR_sR : invR hC ≫ sR hC = tR hC := hom_ext_R hC fun p => by
  rw [reassoc_of% (ιR_invR hC p), ιR_sR, ιR_tR]
  exact (reassoc_of% (C.inv_comp_s p.1 p.2)) _

/-- `invR` exchanges `sR` and `tR`: `invR ≫ tR = sR`. -/
theorem invR_tR : invR hC ≫ tR hC = sR hC := hom_ext_R hC fun p => by
  rw [reassoc_of% (ιR_invR hC p), ιR_tR, ιR_sR]
  exact (reassoc_of% (C.inv_comp_t p.1 p.2)) _

/-! ### Composition -/

/-- The scheme `R ×_{tR, U, sR} R` of composable pairs. -/
noncomputable abbrev Q : BigFppfOver B S hS := pullback (tR hC) (sR hC)

/-- The first projection of `R ×_U R`. -/
noncomputable abbrev q₁ : Q hC ⟶ R hC := pullback.fst _ _

/-- The second projection of `R ×_U R`. -/
noncomputable abbrev q₂ : Q hC ⟶ R hC := pullback.snd _ _

/-- The first projection of a pullback in the site is an open immersion of schemes when the second
morphism is. -/
theorem isOpenImmersion_toScheme_pullback_fst {X Y Z : BigFppfOver B S hS} (f : X ⟶ Z)
    (g : Y ⟶ Z) [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g)] :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (pullback.fst f g)) :=
  MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsOpenImmersion)
    ((IsPullback.of_hasPullback f g).map (BigFppfOver.toScheme B S hS)).flip inferInstance

/-- Two points of `X` and `Y` with the same image in `Z` come from a point of the pullback in the
site. -/
theorem exists_preimage_pullback_site {X Y Z : BigFppfOver B S hS} (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : (BigFppfOver.toScheme B S hS).obj X) (y : (BigFppfOver.toScheme B S hS).obj Y)
    (h : (BigFppfOver.toScheme B S hS).map f x = (BigFppfOver.toScheme B S hS).map g y) :
    ∃ z, (BigFppfOver.toScheme B S hS).map (pullback.fst f g) z = x ∧
      (BigFppfOver.toScheme B S hS).map (pullback.snd f g) z = y := by
  have hP := (IsPullback.of_hasPullback f g).map (BigFppfOver.toScheme B S hS)
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  refine ⟨hP.isoPullback.inv w, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst, hw₁]
  · rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_snd, hw₂]

/-- The piece of `R ×_U R` where the first factor lies in `N i j`. -/
noncomputable abbrev A₁ (τ : C.ι × C.ι × C.ι) : BigFppfOver B S hS :=
  pullback (q₁ hC) (ιR hC (τ.1, τ.2.1))

/-- The piece of `R ×_U R` where the factors lie in `N i j` and `N j k`. -/
noncomputable abbrev A₂ (τ : C.ι × C.ι × C.ι) : BigFppfOver B S hS :=
  pullback (pullback.fst (q₁ hC) (ιR hC (τ.1, τ.2.1)) ≫ q₂ hC) (ιR hC (τ.2.1, τ.2.2))

/-- The inclusion of a piece into `R ×_U R`. -/
noncomputable def inclA (τ : C.ι × C.ι × C.ι) : A₂ hC τ ⟶ Q hC :=
  pullback.fst _ _ ≫ pullback.fst _ _

/-- The first factor of a piece, in `N i j`. -/
noncomputable def r₁ (τ : C.ι × C.ι × C.ι) : A₂ hC τ ⟶ C.N τ.1 τ.2.1 :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- The second factor of a piece, in `N j k`. -/
noncomputable def r₂ (τ : C.ι × C.ι × C.ι) : A₂ hC τ ⟶ C.N τ.2.1 τ.2.2 := pullback.snd _ _

/-- The first factor of a piece, followed by the inclusion of `N i j`, is the first projection. -/
theorem r₁_ιR (τ : C.ι × C.ι × C.ι) : r₁ hC τ ≫ ιR hC (τ.1, τ.2.1) = inclA hC τ ≫ q₁ hC := by
  simp only [r₁, inclA, Category.assoc, pullback.condition]

/-- The second factor of a piece, followed by the inclusion of `N j k`, is the second
projection. -/
theorem r₂_ιR (τ : C.ι × C.ι × C.ι) : r₂ hC τ ≫ ιR hC (τ.2.1, τ.2.2) = inclA hC τ ≫ q₂ hC := by
  simp only [r₂, inclA, Category.assoc, ← pullback.condition]

/-- The two factors of a piece are composable: `r₁ ≫ t = r₂ ≫ s`. -/
theorem r₁_t_eq_r₂_s (τ : C.ι × C.ι × C.ι) :
    r₁ hC τ ≫ C.t τ.1 τ.2.1 = r₂ hC τ ≫ C.s τ.2.1 τ.2.2 := by
  refine (mono_ιU hC τ.2.1).right_cancellation _ _ ?_
  calc (r₁ hC τ ≫ C.t τ.1 τ.2.1) ≫ ιU hC τ.2.1
      = (r₁ hC τ ≫ ιR hC (τ.1, τ.2.1)) ≫ tR hC := by rw [Category.assoc, Category.assoc, ιR_tR]
    _ = inclA hC τ ≫ (q₁ hC ≫ tR hC) := by rw [r₁_ιR, Category.assoc]
    _ = inclA hC τ ≫ (q₂ hC ≫ sR hC) := by rw [pullback.condition]
    _ = (r₂ hC τ ≫ ιR hC (τ.2.1, τ.2.2)) ≫ sR hC := by rw [r₂_ιR, Category.assoc]
    _ = (r₂ hC τ ≫ C.s τ.2.1 τ.2.2) ≫ ιU hC τ.2.1 := by rw [Category.assoc, Category.assoc, ιR_sR]

/-- The inclusion of a piece into `R ×_U R` is an open immersion. -/
instance isOpenImmersion_inclA (τ : C.ι × C.ι × C.ι) :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (inclA hC τ)) := by
  have := isOpenImmersion_toScheme_pullback_fst (pullback.fst (q₁ hC) (ιR hC (τ.1, τ.2.1)) ≫ q₂ hC)
    (ιR hC (τ.2.1, τ.2.2))
  have := isOpenImmersion_toScheme_pullback_fst (q₁ hC) (ιR hC (τ.1, τ.2.1))
  rw [inclA, Functor.map_comp]
  infer_instance

/-- The pieces cover `R ×_U R`. -/
theorem cover_inclA (z : (BigFppfOver.toScheme B S hS).obj (Q hC)) :
    ∃ τ, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (inclA hC τ)) := by
  obtain ⟨p, y₁, hy₁⟩ := cover_ιR hC ((BigFppfOver.toScheme B S hS).map (q₁ hC) z)
  obtain ⟨p', y₂, hy₂⟩ := cover_ιR hC ((BigFppfOver.toScheme B S hS).map (q₂ hC) z)
  have hz : (BigFppfOver.toScheme B S hS).map (tR hC)
        ((BigFppfOver.toScheme B S hS).map (q₁ hC) z) =
      (BigFppfOver.toScheme B S hS).map (sR hC)
        ((BigFppfOver.toScheme B S hS).map (q₂ hC) z) := by
    exact map_apply_eq_of_comp_eq pullback.condition z
  have hj : p.2 = p'.1 := by
    by_contra hne
    refine disjoint_ιU hC hne ((BigFppfOver.toScheme B S hS).map (C.t p.1 p.2) y₁)
      ((BigFppfOver.toScheme B S hS).map (C.s p'.1 p'.2) y₂) ?_
    rw [← map_apply_eq_of_comp_eq (ιR_tR hC _), ← map_apply_eq_of_comp_eq (ιR_sR hC _), hy₁,
      hy₂, hz]
  obtain ⟨a, b⟩ := p
  obtain ⟨b', c⟩ := p'
  dsimp only at hj y₁ y₂ hy₁ hy₂
  subst hj
  obtain ⟨z₁, hz₁, hz₁'⟩ := exists_preimage_pullback_site (q₁ hC) (ιR hC (a, b)) z y₁ hy₁.symm
  obtain ⟨z₂, hz₂, -⟩ := exists_preimage_pullback_site
    (pullback.fst (q₁ hC) (ιR hC (a, b)) ≫ q₂ hC) (ιR hC (b, c)) z₁ y₂
    (by rw [Functor.map_comp, Scheme.Hom.comp_apply, hz₁, hy₂])
  exact ⟨(a, b, c), z₂, by rw [inclA, Functor.map_comp, Scheme.Hom.comp_apply, hz₂, hz₁]⟩

/-- Distinct pieces of `R ×_U R` have disjoint images. -/
theorem disjoint_inclA {τ τ' : C.ι × C.ι × C.ι} (h : τ ≠ τ')
    (y : (BigFppfOver.toScheme B S hS).obj (A₂ hC τ))
    (y' : (BigFppfOver.toScheme B S hS).obj (A₂ hC τ')) :
    (BigFppfOver.toScheme B S hS).map (inclA hC τ) y ≠
      (BigFppfOver.toScheme B S hS).map (inclA hC τ') y' := by
  intro hyy
  have h₁ : (τ.1, τ.2.1) = (τ'.1, τ'.2.1) := by
    by_contra hne
    refine disjoint_ιR hC hne ((BigFppfOver.toScheme B S hS).map (r₁ hC τ) y)
      ((BigFppfOver.toScheme B S hS).map (r₁ hC τ') y') ?_
    rw [map_apply_eq_of_comp_eq (r₁_ιR hC τ), map_apply_eq_of_comp_eq (r₁_ιR hC τ'), hyy]
  have h₂ : (τ.2.1, τ.2.2) = (τ'.2.1, τ'.2.2) := by
    by_contra hne
    refine disjoint_ιR hC hne ((BigFppfOver.toScheme B S hS).map (r₂ hC τ) y)
      ((BigFppfOver.toScheme B S hS).map (r₂ hC τ') y') ?_
    rw [map_apply_eq_of_comp_eq (r₂_ιR hC τ), map_apply_eq_of_comp_eq (r₂_ιR hC τ'), hyy]
  obtain ⟨i, j, k⟩ := τ
  obtain ⟨i', j', k'⟩ := τ'
  simp only [Prod.mk.injEq] at h₁ h₂
  exact h (by rw [h₁.1, h₁.2, h₂.2])

/-- The composition on a piece. -/
noncomputable def compPiece (τ : C.ι × C.ι × C.ι) : A₂ hC τ ⟶ R hC :=
  pullback.lift (r₁ hC τ) (r₂ hC τ) (r₁_t_eq_r₂_s hC τ) ≫ C.comp τ.1 τ.2.1 τ.2.2 ≫
    ιR hC (τ.1, τ.2.2)

/-- **The composition `compR : R ×_U R ⟶ R`**, equal to `comp i j k` on the pieces. -/
noncomputable def compR : Q hC ⟶ R hC :=
  (BigFppfOver.exists_desc_of_disjoint_openCover (inclA hC) (isOpenImmersion_inclA hC)
    (fun _ _ h => disjoint_inclA hC h) (cover_inclA hC) (compPiece hC)).choose

/-- On a piece, `compR` is the composition `compPiece` of that piece. -/
theorem inclA_compR (τ : C.ι × C.ι × C.ι) : inclA hC τ ≫ compR hC = compPiece hC τ :=
  (BigFppfOver.exists_desc_of_disjoint_openCover (inclA hC) (isOpenImmersion_inclA hC)
    (fun _ _ h => disjoint_inclA hC h) (cover_inclA hC) (compPiece hC)).choose_spec τ

/-- Two morphisms out of `R ×_U R` agreeing on every piece are equal. -/
theorem hom_ext_Q {X : BigFppfOver B S hS} {h₁ h₂ : Q hC ⟶ X}
    (h : ∀ τ, inclA hC τ ≫ h₁ = inclA hC τ ≫ h₂) : h₁ = h₂ :=
  BigFppfOver.hom_ext_of_openCover (inclA hC) (isOpenImmersion_inclA hC) (cover_inclA hC) h

/-- A composite has the `sR` of its first factor: `compR ≫ sR = q₁ ≫ sR`. -/
theorem compR_sR : compR hC ≫ sR hC = q₁ hC ≫ sR hC := hom_ext_Q hC fun τ => by
  have hij : ιR hC (τ.1, τ.2.1) ≫ sR hC = C.s τ.1 τ.2.1 ≫ ιU hC τ.1 := ιR_sR hC _
  calc inclA hC τ ≫ compR hC ≫ sR hC = compPiece hC τ ≫ sR hC := by
        rw [← Category.assoc, inclA_compR]
    _ = pullback.lift (r₁ hC τ) (r₂ hC τ) (r₁_t_eq_r₂_s hC τ) ≫ C.comp τ.1 τ.2.1 τ.2.2 ≫
          C.s τ.1 τ.2.2 ≫ ιU hC τ.1 := by rw [compPiece, Category.assoc, Category.assoc, ιR_sR]
    _ = r₁ hC τ ≫ C.s τ.1 τ.2.1 ≫ ιU hC τ.1 := by
        rw [reassoc_of% (C.comp_comp_s τ.1 τ.2.1 τ.2.2), pullback.lift_fst_assoc]
    _ = inclA hC τ ≫ q₁ hC ≫ sR hC := by rw [← hij, reassoc_of% (r₁_ιR hC τ)]

/-- A composite has the `tR` of its second factor: `compR ≫ tR = q₂ ≫ tR`. -/
theorem compR_tR : compR hC ≫ tR hC = q₂ hC ≫ tR hC := hom_ext_Q hC fun τ => by
  have hjk : ιR hC (τ.2.1, τ.2.2) ≫ tR hC = C.t τ.2.1 τ.2.2 ≫ ιU hC τ.2.2 := ιR_tR hC _
  calc inclA hC τ ≫ compR hC ≫ tR hC = compPiece hC τ ≫ tR hC := by
        rw [← Category.assoc, inclA_compR]
    _ = pullback.lift (r₁ hC τ) (r₂ hC τ) (r₁_t_eq_r₂_s hC τ) ≫ C.comp τ.1 τ.2.1 τ.2.2 ≫
          C.t τ.1 τ.2.2 ≫ ιU hC τ.2.2 := by rw [compPiece, Category.assoc, Category.assoc, ιR_tR]
    _ = r₂ hC τ ≫ C.t τ.2.1 τ.2.2 ≫ ιU hC τ.2.2 := by
        rw [reassoc_of% (C.comp_comp_t τ.1 τ.2.1 τ.2.2), pullback.lift_snd_assoc]
    _ = inclA hC τ ≫ q₂ hC ≫ tR hC := by rw [← hjk, reassoc_of% (r₂_ιR hC τ)]

/-! ### The étale equivalence relation -/

/-- **The relation induced on `T`-points is an equivalence relation.** -/
theorem isPreEquivalenceRelation_rel : IsPreEquivalenceRelation (rel hC) := by
  intro T
  let F := Over.post (X := B.obj hS) B.inclusion
  have ht : (rel hC).target = F.map (sR hC) := rel_target hC
  have hs : (rel hC).source = F.map (tR hC) := rel_source hC
  refine ⟨fun x => ⟨x ≫ F.map (eR hC), ?_, ?_⟩,
    fun {x y} ⟨r, h₁, h₂⟩ => ⟨r ≫ F.map (invR hC), ?_, ?_⟩,
    fun {x y z} ⟨r, h₁, h₂⟩ ⟨r', h₁', h₂'⟩ => ?_⟩
  · rw [ht, Category.assoc, ← F.map_comp, eR_sR, CategoryTheory.Functor.map_id, Category.comp_id]
  · rw [hs, Category.assoc, ← F.map_comp, eR_tR, CategoryTheory.Functor.map_id, Category.comp_id]
  · rw [ht, Category.assoc, ← F.map_comp, invR_sR, ← hs, h₂]
  · rw [hs, Category.assoc, ← F.map_comp, invR_tR, ← ht, h₁]
  · rw [ht] at h₁ h₁'
    rw [hs] at h₂ h₂'
    have hQ := (IsPullback.of_hasPullback (tR hC) (sR hC)).map (BigFppfOver.toScheme B S hS)
    have hw : r.left ≫ (BigFppfOver.toScheme B S hS).map (tR hC) =
        r'.left ≫ (BigFppfOver.toScheme B S hS).map (sR hC) :=
      (congrArg Over.Hom.left h₂).trans (congrArg Over.Hom.left h₁'.symm)
    let l := hQ.lift r.left r'.left hw
    have hl₁ : l ≫ (BigFppfOver.toScheme B S hS).map (q₁ hC) =
        (r.left : T.left ⟶ (BigFppfOver.toScheme B S hS).obj (R hC)) := hQ.lift_fst _ _ _
    have hl₂ : l ≫ (BigFppfOver.toScheme B S hS).map (q₂ hC) =
        (r'.left : T.left ⟶ (BigFppfOver.toScheme B S hS).obj (R hC)) := hQ.lift_snd _ _ _
    refine ⟨Over.homMk (l ≫ (BigFppfOver.toScheme B S hS).map (compR hC)) ?_, ?_, ?_⟩
    · show (l ≫ (BigFppfOver.toScheme B S hS).map (compR hC)) ≫ B.inclusion.map (R hC).hom = _
      calc (l ≫ (BigFppfOver.toScheme B S hS).map (compR hC)) ≫ B.inclusion.map (R hC).hom
          = l ≫ B.inclusion.map (Q hC).hom := by
            rw [Category.assoc, BigFppfOver.toScheme_map_comp_hom]
        _ = (l ≫ (BigFppfOver.toScheme B S hS).map (q₁ hC)) ≫ B.inclusion.map (R hC).hom := by
            rw [Category.assoc, BigFppfOver.toScheme_map_comp_hom]
        _ = (r.left : T.left ⟶ (BigFppfOver.toScheme B S hS).obj (R hC)) ≫
            B.inclusion.map (R hC).hom := by rw [hl₁]
        _ = T.hom := Over.w r
    · rw [ht, ← h₁]
      apply Over.OverMorphism.ext
      show (l ≫ (BigFppfOver.toScheme B S hS).map (compR hC)) ≫
        (BigFppfOver.toScheme B S hS).map (sR hC) = (r.left : T.left ⟶
          (BigFppfOver.toScheme B S hS).obj (R hC)) ≫ (BigFppfOver.toScheme B S hS).map (sR hC)
      rw [Category.assoc, ← Functor.map_comp, compR_sR, Functor.map_comp, ← Category.assoc, hl₁]
    · rw [hs, ← h₂']
      apply Over.OverMorphism.ext
      show (l ≫ (BigFppfOver.toScheme B S hS).map (compR hC)) ≫
        (BigFppfOver.toScheme B S hS).map (tR hC) = (r'.left : T.left ⟶
          (BigFppfOver.toScheme B S hS).obj (R hC)) ≫ (BigFppfOver.toScheme B S hS).map (tR hC)
      rw [Category.assoc, ← Functor.map_comp, compR_tR, Functor.map_comp, ← Category.assoc, hl₂]

/-- **`∐ N i j ⇉ ∐ M i` is an étale equivalence relation** (the claim in the proof of
Stacks 0DUT). -/
instance isEtaleEquivalenceRelation_rel : IsEtaleEquivalenceRelation (rel hC) where
  isEquivalenceRelation := (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation _).2
    ⟨mono_rel hC, isPreEquivalenceRelation_rel hC⟩
  etale_source := by
    rw [rel_source]
    exact etale_tR hC
  etale_target := by
    rw [rel_target]
    exact etale_sR hC

end AlgebraicGeometry.Stack.KeelMoriCover

end
