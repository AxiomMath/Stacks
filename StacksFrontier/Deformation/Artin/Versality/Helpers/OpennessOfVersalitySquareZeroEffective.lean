module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteTypeSupplement
public import StacksFrontier.Deformation.Artin.FormalObject.Effectiveness
public import StacksFrontier.Deformation.Artin.Versality.DiagonalFibreEffective
public import StacksFrontier.Deformation.Artin.Versality.OpennessCriterion
public import StacksFrontier.Deformation.ArtinCriteria.VersalSmoothness

/-!
# Openness of versality from effectivity of square-zero towers

Let `S` be a locally Noetherian scheme and `𝒳` a category fibred in groupoids over the big fppf
site of `S`. Assume that
1. the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces,
2. `𝒳` has (RS*),
3. `𝒳` is limit preserving,
4. systems `(ξₙ)` as in Stacks 0CXT whose transition kernels `Ker(Rₘ ⟶ Rₙ)` are ideals of square
   zero are effective.

Then `𝒳` satisfies openness of versality. This is the statement of Stacks 0CXU; the proof is the
source's, assembled from the base criterion
`Deformation.Artin.isOpenVersality_of_hasLocalRetractions`:

* the local retraction at a versal point (the step through `Z = (Sch/U) ×_𝒳 (Sch/U')`, Stacks
  0CXM and 04AM) is `Deformation.Artin.hasLocalRetractions_of_hasRepresentableDiagonal`, which
  needs (RS), implied by (RS*), and the diagonal locally of finite type, implied by limit
  preservation (Stacks 0CXI);
* descent of an object over a first-order thickening to a first-order thickening of finite type
  is `Deformation.Artin.hasThickeningDescent_of_isLimitPreserving`;
* a tower `x ⟶ x₁ ⟶ x₂ ⟶ …` over first-order thickenings `U ⟶ Uₙ` is a system of Stacks 0CXT
  over `Spec Rₙ` with square-zero transition kernels, over an affine open of `S`, so it is
  effective by condition (4)
  (`Deformation.Artin.hasEffectiveThickeningTowers_of_isEffectiveOnSquareZeroTowers`).

This module is a helper and carries no `@[stacks]` attribute: the tag is registered elsewhere.

## Main definitions

* `Deformation.Artin.IsEffectiveOnSquareZeroTowers`: condition (4) of Stacks 0CXU.

## Main results

* `Deformation.Artin.hasEffectiveThickeningTowers_of_isEffectiveOnSquareZeroTowers`: towers of
  first-order thickenings over affine opens of `S` are effective under condition (4).
* `Deformation.Artin.isOpenVersality_of_isEffectiveOnSquareZeroTowers`: openness of versality,
  in the form of the hypothesis `hopen` of
  `AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms_succ`.

## Implementation notes

The inverse system of Stacks 0CXT is given, as in
`Deformation.Artin.IsFullyFaithfulOnSquareZeroTowers`, by its spectra: a functor `ξ : ℕ ⥤ 𝒳`
lying over a tower `Tₙ` of affine objects of the site, and a cocone `Tₙ ⟶ T` with `T` affine whose
rings of global sections form a limit cone, lying over an affine open `G = Spec Λ` of `S`; the
transition maps are surjective on global sections with square-zero kernels. Effectivity is
`Deformation.Artin.IsEffectiveSystem`: the cocone is the image of a cocone `ξₙ ⟶ ξ` of `𝒳`, whose
legs, being arrows of a category fibred in groupoids, exhibit `ξₙ` as the restriction of `ξ`.

## References

* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
* [Stacks Project, Tag 0CXI](https://stacks.math.columbia.edu/tag/0CXI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u v w

/-- **Condition (4) of Stacks 0CXU.** For every affine open `G` of `S`, every system `ξ : ℕ ⥤ 𝒳`
lying over a tower `Tₙ` of affine schemes of the site, whose transition maps are surjective on
global sections with square-zero kernels, and every cocone `Tₙ ⟶ T` lying over `G`, with `T` affine
and `Γ(T) = lim Γ(Tₙ)`, is effective: the cocone is the image of a cocone `ξₙ ⟶ ξ` of `𝒳`. -/
abbrev IsEffectiveOnSquareZeroTowers (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X : Type v} [Category.{w} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) : Prop :=
  ∀ (G : S.Opens), IsAffineOpen G →
    ∀ (ξ : ℕ ⥤ X) (c : Cocone (ξ ⋙ p)),
      (∀ n, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj ((ξ ⋙ p).obj n))) →
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj c.pt) →
      Set.range (B.inclusion.map c.pt.hom).base ⊆ (G : Set S) →
      (∀ {i j : ℕ} (f : i ⟶ j), Function.Surjective
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map ((ξ ⋙ p).map f)).appTop) →
      (∀ {i j : ℕ} (f : i ⟶ j), RingHom.ker
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
          ((ξ ⋙ p).map f)).appTop.hom ^ 2 = ⊥) →
      IsLimit (((AlgebraicGeometry.BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ).mapCone c.op) →
      IsEffectiveSystem p ξ c

/-- The legs of a cocone of objects whose image is a given cocone of the base are, up to the
identification of the apexes, the legs of the given cocone. -/
theorem map_ι_app_of_mapCocone_eq {J X C : Type*} [Category J] [Category X] [Category C]
    {p : X ⥤ C} {ξ : J ⥤ X} {d : Cocone ξ} {c : Cocone (ξ ⋙ p)} (h : p.mapCocone d = c)
    (j : J) : p.map (d.ι.app j) = c.ι.app j ≫ eqToHom (congrArg Cocone.pt h).symm := by
  subst h
  simp

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)

/-- **Effective towers of first-order thickenings from condition (4) of Stacks 0CXU.** A tower
`x ⟶ x₁ ⟶ x₂ ⟶ …` of `𝒳` over first-order thickenings `U ⟶ Uₙ` of an affine scheme `U` lying
over an affine open `W = Spec Λ` of `S`, with closed immersions `Uₙ ⟶ Uₙ₊₁`, is a system of
Stacks 0CXT over `Spec Rₙ`, `Rₙ = Γ(Uₙ)`, whose transition kernels are of square zero (they lie
in the square-zero kernel of `Rₙ ⟶ Γ(U)`). By condition (4) it is the restriction of an object
`ξ` over `Spec (lim Rₙ)`, and `U ⟶ Spec (lim Rₙ)` is again a first-order thickening. -/
theorem hasEffectiveThickeningTowers_of_isEffectiveOnSquareZeroTowers
    (h4 : IsEffectiveOnSquareZeroTowers B S hS p) :
    HasEffectiveThickeningTowers B S hS p (fun W => IsAffineOpen W) := by
  classical
  intro x xs step fromX hfromS hxaff _ ⟨W, hWaff, hxW⟩ hthick hstep
  let VV := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have : IsAffine W := hWaff
  -- the tower as a functor out of `ℕ`
  let Xs := Functor.ofSequence (fun n => step (n + 1))
  let Tn := Xs ⋙ p
  have : IsAffine (VV.obj (p.obj x)) := hxaff
  have hTaff : ∀ n, IsAffine (VV.obj (Tn.obj n)) := fun n =>
    Stacks.Thickenings.isAffine_of_isThickening (hthick n).isThickening
  have hXs : ∀ n, Xs.map (homOfLE (Nat.le_succ n)) = step (n + 1) := fun n =>
    Functor.ofSequence_map_homOfLE_succ _ n
  let g : ∀ n, x ⟶ Xs.obj n := fun n => fromX (n + 1)
  have hfromX : ∀ {i j : ℕ} (f : i ⟶ j), g i ≫ Xs.map f = g j := fun f =>
    comp_map_of_succ Xs g (fun n => by
      show fromX (n + 1 + 1) = fromX (n + 1) ≫ Xs.map (homOfLE (Nat.le_succ n))
      rw [hXs]
      exact hfromS (n + 1)) f
  have hclosed : ∀ {i j : ℕ} (f : i ⟶ j), IsClosedImmersion (VV.map (Tn.map f)) := fun f =>
    isClosedImmersion_map_of_succ (p ⋙ VV) Xs (fun n => by
      rw [Functor.comp_map, hXs]
      exact hstep n) f
  -- every stage lies over `W`
  have hover : ∀ {a b : AlgebraicGeometry.BigFppfOver B S hS} (f : a ⟶ b),
      VV.map f ≫ B.inclusion.map b.hom = B.inclusion.map a.hom := fun f =>
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w f))
  have hTW : ∀ n, Set.range (B.inclusion.map (Tn.obj n).hom).base ⊆
      Set.range W.ι.base := by
    intro n
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    obtain ⟨u, rfl⟩ := (hthick n).isThickening.2 t
    have e : (B.inclusion.map (Tn.obj n).hom).base ((VV.map (p.map (g n))).base u) =
        (B.inclusion.map (p.obj x).hom).base u :=
      congrArg (fun φ => φ.base u) (hover (p.map (g n)))
    show (B.inclusion.map (Tn.obj n).hom).base ((VV.map (p.map (g n))).base u) ∈ W
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
    exact hover _
  -- the limit ring
  let F : ℕᵒᵖ ⥤ CommRingCat.{u} := Tn.op ⋙ VV.op ⋙ Scheme.Γ
  let R : CommRingCat.{u} := limit F
  have hFc : ∀ n : ℕᵒᵖ, B.Contains (Spec (F.obj n)) := by
    intro n
    have : IsAffine (VV.obj (Tn.obj n.unop)) := hTaff n.unop
    have h : Scheme.size (VV.obj (Tn.obj n.unop)) < B.cutoff := (Tn.obj n.unop).left.2
    rw [Scheme.size_of_isAffine] at h
    show Scheme.size (Spec (F.obj n)) < B.cutoff
    rw [Scheme.size_Spec]
    exact h
  have hRc : B.Contains (Spec R) := contains_spec_limit B F hFc
  let lam : Γ(W, ⊤) ⟶ R := limit.lift F
    { pt := Γ(W, ⊤)
      π := { app := fun n => (τ n.unop).appTop
             naturality := fun a b f => by
               show 𝟙 _ ≫ (τ b.unop).appTop =
                 (τ a.unop).appTop ≫ (VV.map (Tn.map f.unop)).appTop
               rw [Category.id_comp, ← Scheme.Hom.comp_appTop, hτmap] } }
  let toS : Spec R ⟶ S := Spec.map lam ≫ (W : Scheme.{u}).isoSpec.inv ≫ W.ι
  let Tlim : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (X := B.obj hRc) (Y := B.obj hS) toS)
  let πn : ∀ n, R ⟶ Γ(VV.obj (Tn.obj n), ⊤) := fun n => limit.π F (Opposite.op n)
  have hπlam : ∀ n, lam ≫ πn n = (τ n).appTop := fun n => limit.lift_π _ _
  have hπw : ∀ {i j : ℕ} (f : i ⟶ j), πn j ≫ (VV.map (Tn.map f)).appTop = πn i := fun f =>
    limit.w F f.op
  let legS : ∀ n, VV.obj (Tn.obj n) ⟶ Spec R := fun n =>
    have := hTaff n
    (VV.obj (Tn.obj n)).isoSpec.hom ≫ Spec.map (πn n)
  have hlegS : ∀ n, legS n ≫ toS = B.inclusion.map (Tn.obj n).hom := by
    intro n
    have := hTaff n
    calc legS n ≫ toS = (VV.obj (Tn.obj n)).isoSpec.hom ≫ (Spec.map (πn n) ≫ Spec.map lam) ≫
          (W : Scheme.{u}).isoSpec.inv ≫ W.ι := by simp only [legS, toS, Category.assoc]
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
    show VV.map (Tn.map f) ≫ (VV.obj (Tn.obj j)).isoSpec.hom ≫ Spec.map (πn j) =
      (VV.obj (Tn.obj i)).isoSpec.hom ≫ Spec.map (πn i)
    rw [← Scheme.isoSpec_hom_naturality_assoc, ← Spec.map_comp, hπw]
  let c : Cocone Tn :=
    { pt := Tlim
      ι := { app := leg
             naturality := fun i j f => (hlegnat f).trans (Category.comp_id _).symm } }
  have hΓ : IsLimit ((VV.op ⋙ Scheme.Γ).mapCone c.op) :=
    IsLimit.ofIsoLimit (isLimitΓSpecLimitCone F) (Cone.ext (Iso.refl _) (fun n => by
      have := hTaff n.unop
      exact (appTop_isoSpec_hom_comp_specMap (πn n.unop)).symm.trans (Category.id_comp _).symm))
  have hsurjΓ : ∀ {i j : ℕ} (f : i ⟶ j), Function.Surjective (VV.map (Tn.map f)).appTop := by
    intro i j f
    have := hTaff j
    have := hclosed f
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (VV.map (Tn.map f))).2
  have hpfac : ∀ {i j : ℕ} (f : i ⟶ j), (VV.map (p.map (g j))).appTop =
      (VV.map (Tn.map f)).appTop ≫ (VV.map (p.map (g i))).appTop := by
    intro i j f
    have e : p.map (g i) ≫ Tn.map f = p.map (g j) :=
      (p.map_comp _ _).symm.trans (congrArg p.map (hfromX f))
    rw [← Scheme.Hom.comp_appTop, ← VV.map_comp, e]
  have hkerg : ∀ n, RingHom.ker (VV.map (p.map (g n))).appTop.hom ^ 2 = ⊥ := fun n =>
    @ker_appTop_sq_of_isFirstOrderThickening _ _ (hTaff n) _ (hthick n)
  have hkerΓ : ∀ {i j : ℕ} (f : i ⟶ j),
      RingHom.ker (VV.map (Tn.map f)).appTop.hom ^ 2 = ⊥ := by
    intro i j f
    refine le_bot_iff.mp ((Ideal.pow_right_mono ?_ 2).trans (hkerg j).le)
    intro z hz
    have hz' : (VV.map (Tn.map f)).appTop.hom z = 0 := hz
    show (VV.map (p.map (g j))).appTop.hom z = 0
    rw [hpfac f, CommRingCat.comp_apply, hz', map_zero]
  have hrange : Set.range (B.inclusion.map c.pt.hom).base ⊆ (W : Set S) := by
    rintro _ ⟨t, rfl⟩
    show toS.base t ∈ W
    have e : toS = (Spec.map lam ≫ (W : Scheme.{u}).isoSpec.inv) ≫ W.ι := by
      simp only [toS, Category.assoc]
    rw [e, Scheme.Hom.comp_apply]
    exact (Scheme.Opens.range_ι W).subset ⟨_, rfl⟩
  -- condition (4)
  obtain ⟨d, hd⟩ := h4 W hWaff Xs c (fun n => hTaff n)
    (inferInstanceAs (IsAffine (Spec R))) hrange hsurjΓ hkerΓ hΓ
  refine ⟨d.pt, fun n => d.ι.app n, fun n => ?_, ?_⟩
  · rw [← hXs n]
    exact d.w _
  · have hι0 : VV.map (p.map (fromX 1 ≫ d.ι.app 0)) =
        (VV.map (p.map (g 0)) ≫ legS 0) ≫ eqToHom (congrArg VV.obj
          (congrArg Cocone.pt hd).symm) := by
      have h0 := congrArg VV.map (map_ι_app_of_mapCocone_eq hd 0)
      rw [VV.map_comp, eqToHom_map] at h0
      refine (congrArg VV.map (p.map_comp _ _)).trans ((VV.map_comp _ _).trans ?_)
      exact (congrArg (VV.map (p.map (fromX 1)) ≫ ·) h0).trans (Category.assoc _ _ _).symm
    rw [hι0]
    refine isFirstOrderThickening_comp_eqToHom _ _ ?_
    have := hTaff 0
    have : IsAffine (VV.obj (p.obj (Xs.obj 0))) := hTaff 0
    have : IsClosedImmersion (VV.map (p.map (g 0))) := (hthick 0).1
    have : IsAffine (Spec R) := inferInstance
    have happ : (VV.map (p.map (g 0)) ≫ legS 0).appTop =
        (Scheme.ΓSpecIso R).hom ≫ πn 0 ≫ (VV.map (p.map (g 0))).appTop := by
      rw [Scheme.Hom.comp_appTop, appTop_isoSpec_hom_comp_specMap, Category.assoc]
    have hp₀ : Function.Surjective (VV.map (p.map (g 0))).appTop :=
      (IsClosedImmersion.isAffine_surjective_of_isAffine _).2
    have hπ₀ : Function.Surjective (πn 0) := by
      have hl := isLimitOfPreserves (forget CommRingCat) (limit.isLimit F)
      refine Types.surjective_π_app_zero_of_surjective_map hl (fun n => ?_)
      exact hsurjΓ (homOfLE (Nat.le_succ n))
    refine isFirstOrderThickening_of_appTop _ ?_ ?_
    · refine (congrArg (fun φ => Function.Surjective (ConcreteCategory.hom φ)) happ).mpr ?_
      exact (hp₀.comp hπ₀).comp (ConcreteCategory.bijective_of_isIso _).2
    · refine (congrArg (fun φ => RingHom.ker (CommRingCat.Hom.hom φ) ^ 2 = ⊥) happ).mpr ?_
      refine ker_comp_sq_eq_bot _ (ConcreteCategory.bijective_of_isIso _).1 _ ?_
      exact ker_limit_π_comp_sq_eq_bot F (fun n => (VV.map (p.map (g n))).appTop) hpfac hkerg

/-- **Openness of versality from effectivity of square-zero towers.** Let `S` be locally
Noetherian and `𝒳` a category fibred in groupoids over the big fppf site of `S` whose diagonal is
representable by algebraic spaces, which has (RS*), is limit preserving, and on which systems of
Stacks 0CXT with square-zero transition kernels are effective. Then `𝒳` satisfies openness of
versality: if `x` over a scheme `U` locally of finite type over `S` is versal at a finite type
point `u₀`, it is versal at every finite type point of an open neighbourhood of `u₀`. This is the
statement of Stacks 0CXU. -/
theorem isOpenVersality_of_isEffectiveOnSquareZeroTowers [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : IsLimitPreserving.{u, u, u, max (u + 1) v w, max u v} B S hS 𝒳)
    (h4 : IsEffectiveOnSquareZeroTowers B S hS 𝒳.val.p) :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : 𝒳.val.obj) (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ →
        IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
          ∀ u ∈ W.1, IsFiniteTypePoint u →
            IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u x hx :=
  isOpenVersality_of_hasLocalRetractions B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids hRS
    (hasLocalRetractions_of_hasRepresentableDiagonal B S hS 𝒳 hΔ
      (AlgebraicGeometry.Stack.isLocallyOfFiniteType_terminal_of_isLocallyOfFiniteType_diagonal
        B S hS 𝒳 hΔ
        (AlgebraicGeometry.Stack.isLocallyOfFiniteType_diagonal_univ B S hS 𝒳 hΔ hlim))
      (satisfiesRS_of_satisfiesRSStar B S hS _ _ hRS))
    (hasThickeningDescent_of_isLimitPreserving B S hS 𝒳 hlim)
    (fun W => IsAffineOpen W)
    (fun s => by
      obtain ⟨G, hG, hsG, -⟩ :=
        exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top s)
      exact ⟨G, hG, hG, hsG⟩)
    (hasEffectiveThickeningTowers_of_isEffectiveOnSquareZeroTowers B S hS 𝒳.val.p
      h4).weaklyEffective

end Deformation.Artin

end
