module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Types.Images
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.LocalStructure.InfinitesimalSections
public import StacksFrontier.Deformation.Artin.Versality.DiagonalFibreDescent
public import StacksFrontier.Deformation.Artin.Versality.SetoidOpenness
public import StacksFrontier.SetTheory.Cardinal.SizeBound

/-!
# Effectivity of towers of thickenings in the fibres of the diagonal

Let `S` be a scheme and `𝒳` a category fibred in groupoids over the big fppf site of `S`.
Condition (4) of Stacks 0CXV asks that for every inverse system `(Rₙ)` of algebras over an
affine open `Spec Λ ⊆ S`, with surjective transition maps whose kernels are square-zero ideals,
the restriction functor `𝒳_{Spec lim Rₙ} ⟶ lim 𝒳_{Spec Rₙ}` be fully faithful
(`Deformation.Artin.IsFullyFaithfulOnSquareZeroTowers`). Under this condition, towers of
first-order thickenings in the fibres `𝒲 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` of the diagonal are
effective: an object of `𝒲` over `T` is an isomorphism `y₁|_T ⟶ y₂|_T`, and a compatible
system of such isomorphisms over the `Spec Rₙ` is the image of one over `Spec lim Rₙ` by fullness.

## Main definitions

* `Deformation.Artin.IsFullyFaithfulOnSquareZeroTowers`: condition (4) of Stacks 0CXV.

## Main results

* `Deformation.Artin.hasEffectiveThickeningTowers_diagonalFibre`: towers of first-order
  thickenings in the fibres of the diagonal are effective.

## Implementation notes

The inverse system of Stacks 0CXT is given by its spectra: a tower `Tₙ` of affine objects of the
site and a cocone `Tₙ ⟶ T` with `T` affine whose rings of global sections form a limit cone, all
lying over an affine open `G` of `S`. Up to isomorphism these are exactly the systems
`Spec Rₙ ⟶ Spec (lim Rₙ)` of the source, with `Λ = Γ(G)`. The limit category
`lim 𝒳_{Spec Rₙ}` is not formed: a functor `ℕ ⥤ 𝒳` with a cocone over the given one is a system
of restrictions of the object at its apex, and fullness and faithfulness of the comparison are
stated on vertical natural transformations between two such systems.

## References

* [Stacks Project, Tag 0CXV](https://stacks.math.columbia.edu/tag/0CXV)
* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.TwoFibreProductOver CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] _root_.CategoryTheory.TwoFibreProductOver.fst
  _root_.CategoryTheory.TwoFibreProductOver.snd
  _root_.CategoryTheory.TwoFibreProductOver.diagonal

/-- **Condition (4) of Stacks 0CXV.** For every tower `Tₙ` of affine schemes of the site over an
affine open `G` of `S`, whose transition maps are surjective with square-zero kernels on global
sections, and every cocone `Tₙ ⟶ T` with `T` affine and `Γ(T) = lim Γ(Tₙ)`, the restriction
functor from objects over `T` to compatible systems of objects over the `Tₙ` is fully faithful:
a vertical morphism between two such systems of restrictions comes from a unique vertical
morphism between their apexes. -/
abbrev IsFullyFaithfulOnSquareZeroTowers (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X : Type v} [Category.{w} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) : Prop :=
  ∀ (G : S.Opens), IsAffineOpen G →
    ∀ (Tn : ℕ ⥤ AlgebraicGeometry.BigFppfOver B S hS) (cT : Cocone Tn),
      (∀ n, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (Tn.obj n))) →
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj cT.pt) →
      Set.range (B.inclusion.map cT.pt.hom).base ⊆ (G : Set S) →
      (∀ {i j : ℕ} (f : i ⟶ j), Function.Surjective
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Tn.map f)).appTop) →
      (∀ {i j : ℕ} (f : i ⟶ j), RingHom.ker
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Tn.map f)).appTop.hom ^ 2 = ⊥) →
      IsLimit (((AlgebraicGeometry.BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ).mapCone cT.op) →
      ∀ (ξa ξb : ℕ ⥤ X) (da : Cocone ξa) (db : Cocone ξb),
        (∀ n, p.IsHomLift (cT.ι.app n) (da.ι.app n)) →
        (∀ n, p.IsHomLift (cT.ι.app n) (db.ι.app n)) →
        (∀ η : ξa ⟶ ξb, (∀ n, p.IsHomLift (𝟙 (Tn.obj n)) (η.app n)) →
          ∃ h : da.pt ⟶ db.pt, p.IsHomLift (𝟙 cT.pt) h ∧
            ∀ n, da.ι.app n ≫ h = η.app n ≫ db.ι.app n) ∧
        (∀ h h' : da.pt ⟶ db.pt, p.IsHomLift (𝟙 cT.pt) h → p.IsHomLift (𝟙 cT.pt) h' →
          (∀ n, da.ι.app n ≫ h = da.ι.app n ≫ h') → h = h')

/-- **Countable limits of rings stay in the site.** The spectrum of the limit of an inverse
system of rings indexed by `ℕ`, each of whose spectra lies in the site, lies in the site. -/
theorem contains_spec_limit (B : AlgebraicGeometry.BigFppfSite.{u}) (F : ℕᵒᵖ ⥤ CommRingCat.{u})
    (hF : ∀ n, B.Contains (Spec (F.obj n))) : B.Contains (Spec (limit F)) := by
  have hc : ∀ n, Cardinal.mk (F.obj n) < B.cutoff := fun n => by
    have h : Scheme.size (Spec (F.obj n)) < B.cutoff := hF n
    rw [Scheme.size_Spec] at h
    exact (le_max_right _ _).trans_lt h
  let κ := ⨆ n, Cardinal.mk (F.obj n)
  have hN : Cardinal.lift.{u, 0} (Cardinal.mk ℕᵒᵖ) = Cardinal.aleph0 := by
    rw [Cardinal.mk_congr (Opposite.equivToOpposite (α := ℕ)).symm]
    simp
  have hκ : κ < B.cutoff := by
    refine Cardinal.lift_iSup_lt_of_lt_cof_ord ?_ hc
    rw [hN, Cardinal.lift_uzero]
    exact B.aleph0_lt_cutoff_cof
  have hinj : Function.Injective
      (fun (z : ToType (limit F)) (n : ℕᵒᵖ) => (limit.π F n).hom z) := by
    intro a b h
    exact Concrete.limit_ext F a b (fun n => congrFun h n)
  have hle : Cardinal.mk (ToType (limit F)) ≤ κ ^ Cardinal.aleph0 := by
    refine (Cardinal.mk_le_of_injective hinj).trans ?_
    rw [Cardinal.mk_pi]
    calc Cardinal.prod (fun n : ℕᵒᵖ => Cardinal.mk (F.obj n))
        ≤ Cardinal.prod (fun _ : ℕᵒᵖ => κ) :=
          Cardinal.prod_le_prod _ _ (fun n => le_ciSup Cardinal.bddAbove_of_small n)
      _ = κ ^ Cardinal.aleph0 := by
          rw [Cardinal.prod_const, hN, Cardinal.lift_uzero]
  change Scheme.size (Spec (limit F)) < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (hle.trans_lt (Cardinal.power_lt_of_isStrongPrelimit
    B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hκ B.aleph0_lt_cutoff))

/-- The ring of global sections of the spectrum of a limit of rings, with its projections, is a
limit cone. -/
noncomputable def isLimitΓSpecLimitCone {J : Type*} [Category J] (F : J ⥤ CommRingCat.{u})
    [HasLimit F] :
    IsLimit (Cone.mk (Γ(Spec (limit F), ⊤)) ((Functor.const J).map (Scheme.ΓSpecIso _).hom ≫
      (limit.cone F).π)) :=
  IsLimit.ofIsoLimit (limit.isLimit F) (Cone.ext (Scheme.ΓSpecIso (limit F)).symm (by simp))

/-- Precomposing with an injective ring map keeps a kernel of square zero of square zero. -/
theorem ker_comp_sq_eq_bot {A B C : CommRingCat.{u}} (e : A ⟶ B) (he : Function.Injective e)
    (f : B ⟶ C) (hf : RingHom.ker f.hom ^ 2 = ⊥) : RingHom.ker (e ≫ f).hom ^ 2 = ⊥ := by
  rw [eq_bot_iff, sq, Ideal.mul_le]
  intro a ha b hb
  rw [RingHom.mem_ker, CommRingCat.hom_comp, RingHom.comp_apply] at ha hb
  rw [Ideal.mem_bot]
  apply he
  rw [map_mul, map_zero]
  exact Stacks.Groupoids.mul_eq_zero_of_sq_eq_bot hf ha hb

/-- **Square-zero kernels pass to the limit of a tower.** For a tower of rings `Fₙ` with maps
`φₙ : Fₙ ⟶ A` compatible with the transition maps and with square-zero kernels, the kernel of
`lim Fₙ ⟶ F₀ ⟶ A` has square zero. -/
theorem ker_limit_π_comp_sq_eq_bot (F : ℕᵒᵖ ⥤ CommRingCat.{u}) {A : CommRingCat.{u}}
    (φ : ∀ n, F.obj (Opposite.op n) ⟶ A)
    (hφ : ∀ {i j : ℕ} (f : i ⟶ j), φ j = F.map f.op ≫ φ i)
    (hker : ∀ n, RingHom.ker (φ n).hom ^ 2 = ⊥) :
    RingHom.ker (limit.π F (Opposite.op 0) ≫ φ 0).hom ^ 2 = ⊥ := by
  rw [eq_bot_iff, sq, Ideal.mul_le]
  intro a ha b hb
  rw [RingHom.mem_ker] at ha hb
  rw [Ideal.mem_bot]
  have hmem : ∀ (v : ToType (limit F)), (limit.π F (Opposite.op 0) ≫ φ 0).hom v = 0 →
      ∀ n, (φ n).hom ((limit.π F (Opposite.op n)).hom v) = 0 := by
    intro v hv n
    have e : limit.π F (Opposite.op n) ≫ φ n = limit.π F (Opposite.op 0) ≫ φ 0 := by
      rw [hφ (homOfLE (Nat.zero_le n)), ← Category.assoc, limit.w]
    rw [← CommRingCat.comp_apply, e]
    exact hv
  refine Concrete.limit_ext F _ _ (fun n => ?_)
  change (limit.π F n).hom (a * b) = (limit.π F n).hom 0
  rw [map_mul, map_zero]
  exact Stacks.Groupoids.mul_eq_zero_of_sq_eq_bot (hker n.unop) (hmem a ha n.unop)
    (hmem b hb n.unop)

/-- Global sections of `X ⟶ Spec Γ(X) ⟶ Spec R` for an affine `X` and `π : R ⟶ Γ(X)`. -/
theorem appTop_isoSpec_hom_comp_specMap {X : Scheme.{u}} [IsAffine X] {R : CommRingCat.{u}}
    (π : R ⟶ Γ(X, ⊤)) : (X.isoSpec.hom ≫ Spec.map π).appTop = (Scheme.ΓSpecIso R).hom ≫ π := by
  rw [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality]

/-- A morphism of affine schemes which is surjective on global sections with square-zero kernel
is a first-order thickening. -/
theorem isFirstOrderThickening_of_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (hs : Function.Surjective f.appTop)
    (hk : RingHom.ker f.appTop.hom ^ 2 = ⊥) : Stacks.Thickenings.IsFirstOrderThickening f := by
  have : IsClosedImmersion f := IsClosedImmersion.of_surjective_of_isAffine f hs
  exact ⟨inferInstance, (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine f 2).mpr hk⟩

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (AlgebraicGeometry.BigFppfOver B S hS))
  (V : AlgebraicGeometry.BigFppfOver B S hS)
  (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
  (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)

/-- The affine opens of `V` whose image in `S` lies in an affine open of `S`. -/
abbrev IsAffineOpenOverAffineOpen (W : V.left.1.Opens) : Prop :=
  IsAffineOpen W ∧ ∃ G : S.Opens, IsAffineOpen G ∧
    Set.range (W.ι ≫ B.inclusion.map V.hom).base ⊆ (G : Set S)

/-- A property of the morphisms of `ℕ` holding for identities and stable under postcomposition
with successor morphisms holds for all morphisms. -/
private theorem hom_induction_of_succ (P : ∀ {i j : ℕ}, (i ⟶ j) → Prop)
    (hid : ∀ i, P (𝟙 i))
    (hsucc : ∀ {i j : ℕ} (f : i ⟶ j), P f → P (f ≫ homOfLE (Nat.le_succ j)))
    {i j : ℕ} (f : i ⟶ j) : P f := by
  suffices ∀ (j : ℕ) (h : i ≤ j), P (homOfLE h) from this j (leOfHom f)
  intro j h
  induction j, h using Nat.le_induction with
  | base => exact hid i
  | succ j h ih => exact hsucc _ ih

/-- A family of arrows `x ⟶ F n` compatible with the successor maps of a functor `F : ℕ ⥤ C` is
compatible with all its maps. -/
theorem comp_map_of_succ {C : Type*} [Category C] {x : C} (F : ℕ ⥤ C)
    (g : ∀ n, x ⟶ F.obj n) (h : ∀ n, g (n + 1) = g n ≫ F.map (homOfLE (Nat.le_succ n)))
    {i j : ℕ} (f : i ⟶ j) : g i ≫ F.map f = g j :=
  hom_induction_of_succ (fun {i j} f => g i ≫ F.map f = g j)
    (fun i => by rw [F.map_id, Category.comp_id]) (fun {i j} f ih => by
      rw [F.map_comp, ← Category.assoc, ih, ← h]) f

/-- A property of the morphisms of a functor out of `ℕ` stable under composition and holding for
identities holds for all its morphisms as soon as it holds for the successor morphisms. -/
theorem isClosedImmersion_map_of_succ {C : Type*} [Category C] (Φ : C ⥤ Scheme.{u})
    (F : ℕ ⥤ C) (hF : ∀ n, IsClosedImmersion (Φ.map (F.map (homOfLE (Nat.le_succ n)))))
    {i j : ℕ} (f : i ⟶ j) : IsClosedImmersion (Φ.map (F.map f)) :=
  hom_induction_of_succ (fun {i j} f => IsClosedImmersion (Φ.map (F.map f)))
    (fun i => by rw [F.map_id, Φ.map_id]; infer_instance) (fun {i j} f ih => by
      have := hF j
      rw [F.map_comp, Φ.map_comp]
      infer_instance) f

include hy in
/-- **Effective towers in the fibres of the diagonal.** If `𝒳` satisfies condition (4) of
Stacks 0CXV, then towers of first-order thickenings in the 2-fibre product
`(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` over affine opens of `V` lying over affine opens of `S` are
effective, in the sense of `Deformation.Artin.HasEffectiveThickeningTowers`. -/
theorem hasEffectiveThickeningTowers_diagonalFibre
    (h4 : IsFullyFaithfulOnSquareZeroTowers B S hS 𝒳.val.p) :
    HasEffectiveThickeningTowers B V.left.1 V.left.2
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor)
      (IsAffineOpenOverAffineOpen B S hS V) := by
  classical
  intro x xs step fromX hfromS hxaff _ ⟨W, ⟨hWaff, G, hGaff, hWG⟩, hxW⟩ hthick hstep
  have hp : 𝒳.val.p.IsFiberedInGroupoids := 𝒳.isFiberedInGroupoids
  let : 𝒳.val.p.IsFibered := hp.isFibered
  let q := TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
    (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor
  have : q.Faithful := faithful_fst
  let VV := AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2
  let VS := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hY₁ : Y₁' y ⋙ 𝒳.val.p = Over.map V.hom := h1' hy
  have hY₂ : Y₂' y ⋙ 𝒳.val.p = Over.map V.hom := h2' hy
  have : IsAffine W := hWaff
  -- the tower as a functor out of `ℕ`
  let Xs := Functor.ofSequence (fun n => step (n + 1))
  let Tn := Xs ⋙ q
  have : IsAffine (VV.obj (q.obj x)) := hxaff
  have hTaff : ∀ n, IsAffine (VV.obj (Tn.obj n)) := fun n =>
    Stacks.Thickenings.isAffine_of_isThickening (hthick n).isThickening
  have hXs : ∀ n, Xs.map (homOfLE (Nat.le_succ n)) = step (n + 1) := fun n =>
    Functor.ofSequence_map_homOfLE_succ _ n
  let g : ∀ n, x ⟶ Xs.obj n := fun n => fromX (n + 1)
  have hfromX : ∀ {i j : ℕ} (f : i ⟶ j), g i ≫ Xs.map f = g j := fun f =>
    comp_map_of_succ Xs g (fun n => by
      change fromX (n + 1 + 1) = fromX (n + 1) ≫ Xs.map (homOfLE (Nat.le_succ n))
      rw [hXs]
      exact hfromS (n + 1)) f
  have hclosed : ∀ {i j : ℕ} (f : i ⟶ j), IsClosedImmersion (VV.map (Tn.map f)) := fun f =>
    isClosedImmersion_map_of_succ (q ⋙ VV) Xs (fun n => by
      rw [Functor.comp_map, hXs]
      exact hstep n) f
  -- every stage lies over `W`
  let fx : VV.obj (q.obj x) ⟶ V.left.1 := B.inclusion.map (q.obj x).hom
  have hfT : ∀ n, VV.map (q.map (g n)) ≫ B.inclusion.map (Tn.obj n).hom = fx := fun n =>
    (B.inclusion.map_comp (q.map (g n)).left (Tn.obj n).hom).symm.trans
      (congrArg B.inclusion.map (Over.w (q.map (g n))))
  have hTW : ∀ n, Set.range (B.inclusion.map (Tn.obj n).hom).base ⊆
      Set.range W.ι.base := by
    intro n
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    obtain ⟨u, rfl⟩ := (hthick n).isThickening.2 t
    have e : (VV.map (q.map (g n)) ≫ B.inclusion.map (Tn.obj n).hom).base u = fx.base u := by
      rw [hfT n]
    rw [Scheme.Hom.comp_apply] at e
    change (B.inclusion.map (Tn.obj n).hom).base ((VV.map (q.map (g n))).base u) ∈ W
    rw [e]
    exact hxW ⟨u, rfl⟩
  let τ : ∀ n, VV.obj (Tn.obj n) ⟶ W := fun n =>
    IsOpenImmersion.lift W.ι (B.inclusion.map (Tn.obj n).hom) (hTW n)
  have hτ : ∀ n, τ n ≫ W.ι = B.inclusion.map (Tn.obj n).hom := fun n =>
    IsOpenImmersion.lift_fac _ _ _
  have hτmap : ∀ {i j : ℕ} (f : i ⟶ j), VV.map (Tn.map f) ≫ τ j = τ i := by
    intro i j f
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, hτ, hτ]
    exact (B.inclusion.map_comp (Tn.map f).left (Tn.obj j).hom).symm.trans
      (congrArg B.inclusion.map (Over.w (Tn.map f)))
  -- the limit ring
  let F : ℕᵒᵖ ⥤ CommRingCat.{u} := Tn.op ⋙ VV.op ⋙ Scheme.Γ
  let R : CommRingCat.{u} := limit F
  have hFc : ∀ n : ℕᵒᵖ, B.Contains (Spec (F.obj n)) := by
    intro n
    have : IsAffine (VV.obj (Tn.obj n.unop)) := hTaff n.unop
    have h : Scheme.size (VV.obj (Tn.obj n.unop)) < B.cutoff := (Tn.obj n.unop).left.2
    rw [Scheme.size_of_isAffine] at h
    change Scheme.size (Spec (F.obj n)) < B.cutoff
    rw [Scheme.size_Spec]
    exact h
  have hRc : B.Contains (Spec R) := contains_spec_limit B F hFc
  let lam : Γ(W, ⊤) ⟶ R := limit.lift F
    { pt := Γ(W, ⊤)
      π := { app := fun n => (τ n.unop).appTop
             naturality := fun a b f => by
               change 𝟙 _ ≫ (τ b.unop).appTop =
                 (τ a.unop).appTop ≫ (VV.map (Tn.map f.unop)).appTop
               rw [Category.id_comp, ← Scheme.Hom.comp_appTop, hτmap] } }
  let toV : Spec R ⟶ V.left.1 := Spec.map lam ≫ (W : Scheme.{u}).isoSpec.inv ≫ W.ι
  let Tlim : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 :=
    Over.mk (ObjectProperty.homMk (X := B.obj hRc) (Y := B.obj V.left.2) toV)
  let πn : ∀ n, R ⟶ Γ(VV.obj (Tn.obj n), ⊤) := fun n => limit.π F (Opposite.op n)
  have hπlam : ∀ n, lam ≫ πn n = (τ n).appTop := fun n => limit.lift_π _ _
  have hπw : ∀ {i j : ℕ} (f : i ⟶ j), πn j ≫ (VV.map (Tn.map f)).appTop = πn i := fun f =>
    limit.w F f.op
  let legS : ∀ n, VV.obj (Tn.obj n) ⟶ Spec R := fun n =>
    have := hTaff n
    (VV.obj (Tn.obj n)).isoSpec.hom ≫ Spec.map (πn n)
  have hlegS : ∀ n, legS n ≫ toV = B.inclusion.map (Tn.obj n).hom := by
    intro n
    have := hTaff n
    calc legS n ≫ toV = (VV.obj (Tn.obj n)).isoSpec.hom ≫ (Spec.map (πn n) ≫ Spec.map lam) ≫
          (W : Scheme.{u}).isoSpec.inv ≫ W.ι := by simp only [legS, toV, Category.assoc]
      _ = (VV.obj (Tn.obj n)).isoSpec.hom ≫ Spec.map (τ n).appTop ≫
          (W : Scheme.{u}).isoSpec.inv ≫ W.ι := by rw [← Spec.map_comp, hπlam]
      _ = τ n ≫ W.ι := by rw [Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id_assoc]
      _ = _ := hτ n
  let leg : ∀ n, Tn.obj n ⟶ Tlim := fun n =>
    Over.homMk (ObjectProperty.homMk (legS n)) (ObjectProperty.hom_ext _ (hlegS n))
  have hlegnat : ∀ {i j : ℕ} (f : i ⟶ j), Tn.map f ≫ leg j = leg i := by
    intro i j f
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    have := hTaff i
    have := hTaff j
    change VV.map (Tn.map f) ≫ (VV.obj (Tn.obj j)).isoSpec.hom ≫ Spec.map (πn j) =
      (VV.obj (Tn.obj i)).isoSpec.hom ≫ Spec.map (πn i)
    rw [← Scheme.isoSpec_hom_naturality_assoc, ← Spec.map_comp, hπw]
  let c : Cocone Tn :=
    { pt := Tlim
      ι := { app := leg
             naturality := fun i j f => (hlegnat f).trans (Category.comp_id _).symm } }
  let cS := (Over.map V.hom).mapCocone c
  have hΓ : IsLimit ((VS.op ⋙ Scheme.Γ).mapCone cS.op) :=
    IsLimit.ofIsoLimit (isLimitΓSpecLimitCone F) (Cone.ext (Iso.refl _) (fun n => by
      have := hTaff n.unop
      exact (appTop_isoSpec_hom_comp_specMap (πn n.unop)).symm.trans (Category.id_comp _).symm))
  have hsurjΓ : ∀ {i j : ℕ} (f : i ⟶ j), Function.Surjective (VV.map (Tn.map f)).appTop := by
    intro i j f
    have := hTaff j
    have := hclosed f
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (VV.map (Tn.map f))).2
  have hqfac : ∀ {i j : ℕ} (f : i ⟶ j), (VV.map (q.map (g j))).appTop =
      (VV.map (Tn.map f)).appTop ≫ (VV.map (q.map (g i))).appTop := by
    intro i j f
    have e : q.map (g i) ≫ Tn.map f = q.map (g j) :=
      (q.map_comp _ _).symm.trans (congrArg q.map (hfromX f))
    rw [← Scheme.Hom.comp_appTop, ← VV.map_comp, e]
  have hkerΓ : ∀ {i j : ℕ} (f : i ⟶ j),
      RingHom.ker (VV.map (Tn.map f)).appTop.hom ^ 2 = ⊥ := by
    intro i j f
    have hk := @ker_appTop_sq_of_isFirstOrderThickening _ _ (hTaff j) _ (hthick j)
    refine le_bot_iff.mp ((Ideal.pow_right_mono ?_ 2).trans hk.le)
    intro z hz
    have hz' : (VV.map (Tn.map f)).appTop.hom z = 0 := hz
    change (VV.map (q.map (g j))).appTop.hom z = 0
    rw [hqfac f, CommRingCat.comp_apply, hz', map_zero]
  have hrange : Set.range (B.inclusion.map cS.pt.hom).base ⊆ (G : Set S) := by
    rintro _ ⟨t, rfl⟩
    change (toV ≫ B.inclusion.map V.hom).base t ∈ G
    have e : toV ≫ B.inclusion.map V.hom =
        (Spec.map lam ≫ (W : Scheme.{u}).isoSpec.inv) ≫ W.ι ≫ B.inclusion.map V.hom := by
      simp only [toV, Category.assoc]
    rw [e, Scheme.Hom.comp_apply]
    exact hWG ⟨_, rfl⟩
  obtain ⟨hfull, -⟩ := h4 G hGaff (Tn ⋙ Over.map V.hom) cS (fun n => hTaff n)
    (inferInstanceAs (IsAffine (Spec R))) hrange (fun f => hsurjΓ f) (fun f => hkerΓ f) hΓ
    (Tn ⋙ Y₁' y) (Tn ⋙ Y₂' y) ((Y₁' y).mapCocone c) ((Y₂' y).mapCocone c)
    (fun n => VertHom.isHomLift_map hY₁ (c.ι.app n))
    (fun n => VertHom.isHomLift_map hY₂ (c.ι.app n))
  let η : Tn ⋙ Y₁' y ⟶ Tn ⋙ Y₂' y :=
    { app := fun n => sectOf (Y := y) (hF := Functor.comp_id 𝒳.val.p)
        (Xs.obj n)
      naturality := by
        intro i j f
        exact (sectOf_naturality (Y := y) (hF := Functor.comp_id 𝒳.val.p)
          (Xs.map f)).symm }
  obtain ⟨h, hh, hhc⟩ := hfull η (fun n => isHomLift_sectOf hy (Xs.obj n))
  let ξ := objOf hy Tlim ⟨h, hh⟩ hp
  have hι : ∀ n, ∃ ι : Xs.obj n ⟶ ξ, ι.a = leg n := fun n =>
    exists_hom_of_sectOf hp hy (A := Xs.obj n) (B := ξ) (leg n)
      ((hhc n).symm.trans (congrArg _ (sectOf_objOf hy Tlim ⟨h, hh⟩ hp).symm))
  choose ι hιa using hι
  refine ⟨ξ, ι, fun n => ?_, ?_⟩
  · apply q.map_injective
    have e₁ : q.map (step (n + 1)) = Tn.map (homOfLE (Nat.le_succ n)) :=
      congrArg q.map (hXs n).symm
    refine (q.map_comp _ _).trans ?_
    rw [e₁]
    exact (congrArg (Tn.map (homOfLE (Nat.le_succ n)) ≫ ·) (hιa (n + 1))).trans
      ((hlegnat _).trans (hιa n).symm)
  · have := hTaff 0
    have hι0 : VV.map (q.map (fromX 1 ≫ ι 0)) = VV.map (q.map (g 0)) ≫ legS 0 := by
      refine (congrArg VV.map (q.map_comp _ _)).trans ((VV.map_comp _ _).trans ?_)
      exact congrArg (VV.map (q.map (g 0)) ≫ ·) (congrArg VV.map (hιa 0))
    rw [hι0]
    have : IsAffine (VV.obj (q.obj (Xs.obj 0))) := hTaff 0
    have : IsClosedImmersion (VV.map (q.map (g 0))) := (hthick 0).1
    have : IsAffine (VV.obj (q.obj ξ)) := inferInstanceAs (IsAffine (Spec R))
    have happ : (VV.map (q.map (g 0)) ≫ legS 0).appTop =
        (Scheme.ΓSpecIso R).hom ≫ πn 0 ≫ (VV.map (q.map (g 0))).appTop := by
      rw [Scheme.Hom.comp_appTop, appTop_isoSpec_hom_comp_specMap, Category.assoc]
    have hq₀ : Function.Surjective (VV.map (q.map (g 0))).appTop :=
      (IsClosedImmersion.isAffine_surjective_of_isAffine _).2
    have hπ₀ : Function.Surjective (πn 0) :=
      Types.surjective_π_app_zero_of_surjective_map
        (isLimitOfPreserves (forget CommRingCat) (limit.isLimit F))
        fun n => hsurjΓ (homOfLE (Nat.le_succ n))
    refine isFirstOrderThickening_of_appTop _ ?_ ?_
    · exact (congrArg (fun φ => Function.Surjective (ConcreteCategory.hom φ)) happ).mpr
        ((hq₀.comp hπ₀).comp (ConcreteCategory.bijective_of_isIso _).2)
    · refine (congrArg (fun φ => RingHom.ker (CommRingCat.Hom.hom φ) ^ 2 = ⊥) happ).mpr ?_
      refine ker_comp_sq_eq_bot _ (ConcreteCategory.bijective_of_isIso _).1 _ ?_
      exact ker_limit_π_comp_sq_eq_bot F (fun n => (VV.map (q.map (g n))).appTop)
        (fun f => hqfac f)
        (fun n => @ker_appTop_sq_of_isFirstOrderThickening _ _ (hTaff n) _ (hthick n))

end Deformation.Artin

end
