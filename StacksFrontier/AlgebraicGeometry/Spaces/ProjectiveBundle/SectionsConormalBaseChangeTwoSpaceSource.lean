module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalBaseChangeTwoSpace

/-!
# The source square of the conormal isomorphism of Stacks 0B4I over two spaces

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `u : T ⟶ X` and `v : T' ⟶ X'` scheme points
and `h : T' ⟶ T` with `v ≫ g = u ∘ h`.  The comparison of the source readings in
`AlgebraicGeometry.Space.ConormalChartSourceCompat` is the comparison `v^*g^* ≅ (u ∘ h)^*` of
Stacks 03LU followed by the base change of the Zariski reading at `u`.  This file proves that
identification and reduces the source square of `ConormalChartSourceCompat` over two spaces to
the source square along `h` at `u` and the comparison at `T'` of the reading at `v` on `X'` with
the reading at `u ∘ h` on `X`.

## Main results

* `AlgebraicGeometry.Space.conormalGlueComparison_eq_pointPullbackCompIso`: the comparison of
  the source readings is `R_{T'}(v^*g^* ≅ (u ∘ h)^*)` followed by
  `AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso`.
* `AlgebraicGeometry.Space.conormalSource_twoSpace_of`: the source square over two spaces from
  the source square along `h` and the comparison at `T'`.
* `Stacks.Divisors.conormalSourceBaseChange_inv_comp_hom`: two base changes of the conormal
  source along one morphism differ by the tensor product of the kernel and inverse-line
  comparisons.
* `AlgebraicGeometry.Space.kernelPointReadingHom_twoSpace`: the kernel factors of the source
  readings at `u ∘ h` on `X` and at `v` on `X'`.
* `AlgebraicGeometry.Space.pointPullbackCompIso_hom_app_tensor`: `v^*g^* ≅ (u ∘ h)^*` is
  monoidal.
* `AlgebraicGeometry.Space.pointPullbackCompIso_sectionConormalSource_baseChange`: the tensor
  square of the source readings on the represented space `T'`.
* `AlgebraicGeometry.Space.conormalSourceTensorReading_twoSpace`: the tensor square of the source
  readings at `u ∘ h` on `X` and at `v` on `X'`, after the Zariski reading.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

/-- The inverse of `α ≪≫ eqToIso e ≪≫ β.symm` at `K` is `β ≪≫ eqToIso e₂` followed by the
inverse of `α`, through the identification of the two targets. -/
theorem CategoryTheory.NatIso.trans_eqToIso_symm_inv_app {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] {F₁ F₂ G₁ G₂ H : 𝒞 ⥤ 𝒟} (α : H ≅ G₁) (e : G₁ = F₂) (β : F₁ ≅ F₂)
    (e₂ : F₂ = G₂) (K : 𝒞) (e₃ : G₂.obj K = G₁.obj K) :
    (α ≪≫ eqToIso e ≪≫ β.symm).inv.app K =
      (β ≪≫ eqToIso e₂).hom.app K ≫ eqToHom e₃ ≫ α.inv.app K := by
  subst e e₂
  simp

/-- A square `p ≫ sP ≫ ch = t` and an identity `a ≫ t ≫ ch⁻¹ ≫ c = r`, pasted along
`x = a ≫ p`. -/
theorem CategoryTheory.comp_twoSpaceSource_paste {𝒞 : Type*} [Category 𝒞]
    {A M Pa P₁ N Z : 𝒞} (x : A ⟶ Pa) (sP : Pa ⟶ P₁) (c : P₁ ⟶ Z) (a : A ⟶ M) (p : M ⟶ Pa)
    (ch : P₁ ⟶ N) (t : M ⟶ N) (chi : N ⟶ P₁) (r : A ⟶ Z) (hx : x = a ≫ p)
    (hsq : p ≫ sP ≫ ch = t) (hinv : ch ≫ chi = 𝟙 _) (hg : a ≫ t ≫ chi ≫ c = r) :
    x ≫ sP ≫ c = r := by
  rw [← hg, ← hsq, hx]
  simp only [Category.assoc, reassoc_of% hinv]

/-- **A comparison of `μ ≫ F(k, i)` and `μ' ≫ F(k', i')`**: if `c₁ ≫ c₂ = F(δK, δΛ)`,
`a ≫ μ ≫ F(d₁, d₂) = w ≫ μ'`, `k ≫ δK = d₁ ≫ k'` and `i ≫ δΛ = d₂ ≫ i'`, then
`a ≫ μ ≫ F(k, i) ≫ c₁ ≫ c₂ = w ≫ μ' ≫ F(k', i')`. -/
theorem CategoryTheory.Functor.compBifunctorMap_comp_eq_of_squares {ℬ : Type*} [iℬ : Category ℬ]
    (F : ℬ ⥤ ℬ ⥤ ℬ) {S₀ S S' A₁ A₂ K Λ A₁' A₂' K' Λ' Z₁ : ℬ}
    (a : S₀ ⟶ S) (μ : S ⟶ (F.obj A₁).obj A₂) (k : A₁ ⟶ K) (i : A₂ ⟶ Λ)
    (c₁ : (F.obj K).obj Λ ⟶ Z₁) (c₂ : Z₁ ⟶ (F.obj K').obj Λ')
    (w : S₀ ⟶ S') (μ' : S' ⟶ (F.obj A₁').obj A₂') (k' : A₁' ⟶ K') (i' : A₂' ⟶ Λ')
    (δK : K ⟶ K') (δΛ : Λ ⟶ Λ') (d₁ : A₁ ⟶ A₁') (d₂ : A₂ ⟶ A₂')
    (hc : c₁ ≫ c₂ = (F.map δK).app Λ ≫ (F.obj K').map δΛ)
    (hT : a ≫ μ ≫ (F.map d₁).app A₂ ≫ (F.obj A₁').map d₂ = w ≫ μ')
    (hK : k ≫ δK = d₁ ≫ k') (hΛ : i ≫ δΛ = d₂ ≫ i') :
    a ≫ compBifunctorMap F μ k i ≫ c₁ ≫ c₂ = w ≫ compBifunctorMap F μ' k' i' := by
  rw [hc]
  calc a ≫ (μ ≫ (F.map k).app A₂ ≫ (F.obj K).map i) ≫ (F.map δK).app Λ ≫ (F.obj K').map δΛ
      = a ≫ μ ≫ (F.map (k ≫ δK)).app A₂ ≫ (F.obj K').map (i ≫ δΛ) := by
        rw [← bifunctor_map_app_comp_obj_map]
        simp only [Category.assoc]
    _ = a ≫ μ ≫ (F.map (d₁ ≫ k')).app A₂ ≫ (F.obj K').map (d₂ ≫ i') := by rw [hK, hΛ]
    _ = (a ≫ μ ≫ (F.map d₁).app A₂ ≫ (F.obj A₁').map d₂) ≫ (F.map k').app A₂' ≫
          (F.obj K').map i' := by
        rw [← bifunctor_map_app_comp_obj_map]
        simp only [Category.assoc]
    _ = w ≫ μ' ≫ (F.map k').app A₂' ≫ (F.obj K').map i' := by
        rw [hT]
        simp only [Category.assoc]

/-- Two kernel comparisons `a`, `b` out of a common object `P`, compatible with the inclusions
through `eh`, `e₂`: `k ≫ a⁻¹ ≫ b = d ≫ k'` follows from the equation after the inclusion `ι'`. -/
theorem CategoryTheory.comp_inv_comp_hom_eq_of_comp_ι {𝒞 : Type*} [Category 𝒞]
    {A Av Kx K' P Ex Ev PE : 𝒞} (k : A ⟶ Kx) (ιx : Kx ⟶ Ex) (a : P ≅ Kx) (b : P ≅ K')
    (ι' : K' ⟶ Ev) [Mono ι'] (j : P ⟶ PE) (eh : Ex ≅ PE) (e₂ : Ev ≅ PE)
    (ha : a.hom ≫ ιx = j ≫ eh.inv) (hb : b.hom ≫ ι' = j ≫ e₂.inv) (d : A ⟶ Av) (k' : Av ⟶ K')
    (hmain : k ≫ ιx ≫ eh.hom ≫ e₂.inv = d ≫ k' ≫ ι') :
    k ≫ a.inv ≫ b.hom = d ≫ k' := by
  refine (cancel_mono ι').mp ?_
  have hj : a.inv ≫ j = ιx ≫ eh.hom := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ha, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Category.assoc, hb, reassoc_of% hj, hmain]

/-- Replace the first factor of a composite by an equal morphism. -/
theorem CategoryTheory.comp_eq_of_eq_of_comp_eq {𝒞 : Type*} [Category 𝒞] {X Y Z : 𝒞}
    {f f' : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (e : f = f') (h : f' ≫ g = k) : f ≫ g = k := by
  rw [e, h]

/-- **A reading square through a tensor comparison**: from the square `α ≫ m ≫ d = sB ≫ m'`
upstairs and the naturality `hnat` of the reading comparisons `Z`, `Z'` of tensor products,
`R(α) ≫ (R(m) ≫ Z) ≫ F(a, b) = R(sB) ≫ R(m') ≫ Z'`. -/
theorem CategoryTheory.Functor.map_comp_reading_square {𝒜 ℬ : Type*} [Category 𝒜]
    [iℬ : Category ℬ] (R : 𝒜 ⥤ ℬ) (F : ℬ ⥤ ℬ ⥤ ℬ) {S₀ S S' P P' : 𝒜} {W₁ W₂ V₁ V₂ : ℬ}
    (α : S₀ ⟶ S) (m : S ⟶ P) (Z : R.obj P ⟶ (F.obj W₁).obj W₂) (d : P ⟶ P') (a : W₁ ⟶ V₁)
    (b : W₂ ⟶ V₂) (sB : S₀ ⟶ S') (m' : S' ⟶ P') (Z' : R.obj P' ⟶ (F.obj V₁).obj V₂)
    (hnat : CategoryTheory.Functor.BifunctorNaturalitySquare R F d Z a b Z')
    (hsp : α ≫ m ≫ d = sB ≫ m') :
    R.map α ≫ (R.map m ≫ Z) ≫ (F.map a).app W₂ ≫ (F.obj V₁).map b =
      R.map sB ≫ (R.map m' ≫ Z') := by
  unfold CategoryTheory.Functor.BifunctorNaturalitySquare at hnat
  simp only [Category.assoc]
  rw [← hnat]
  simp only [← R.map_comp_assoc]
  rw [hsp]

/-- A square through a monoidality `h₁` of a comparison `η : F G ≅ Φ`, the naturality `h₂` of a
tensor comparison of `F` and a factorization `h₃` of a base change map. -/
theorem CategoryTheory.Functor.comp_tensorHom_comp_map_eq_of_tensor {𝒞₀ 𝒞 𝒟 : Type*}
    [Category 𝒞₀] [Category 𝒞] [MonoidalCategory 𝒞] [Category 𝒟] [MonoidalCategory 𝒟]
    (G : 𝒞₀ ⥤ 𝒞) (F : 𝒞 ⥤ 𝒟) {S₀ K₁ K₂ : 𝒞₀} {A₁' A₂' : 𝒞} {Y Y₁ Y₂ : 𝒟}
    (η : (G ⋙ F).obj S₀ ⟶ Y) (m : Y ⟶ Y₁ ⊗ Y₂) (e₁ : Y₁ ⟶ (G ⋙ F).obj K₁)
    (e₂ : Y₂ ⟶ (G ⋙ F).obj K₂) (mg : G.obj S₀ ⟶ G.obj K₁ ⊗ G.obj K₂)
    (mv : F.obj (G.obj K₁ ⊗ G.obj K₂) ⟶ F.obj (G.obj K₁) ⊗ F.obj (G.obj K₂))
    (a : G.obj K₁ ⟶ A₁') (b : G.obj K₂ ⟶ A₂') (mv' : F.obj (A₁' ⊗ A₂') ⟶ F.obj A₁' ⊗ F.obj A₂')
    (sB : G.obj S₀ ⟶ A₁' ⊗ A₂')
    (h₁ : η ≫ m ≫ (e₁ ⊗ₘ e₂) = F.map mg ≫ mv)
    (h₂ : F.map (a ⊗ₘ b) ≫ mv' = mv ≫ (F.map a ⊗ₘ F.map b)) (h₃ : sB = mg ≫ (a ⊗ₘ b)) :
    η ≫ m ≫ ((e₁ ≫ F.map a) ⊗ₘ (e₂ ≫ F.map b)) = F.map sB ≫ mv' := by
  rw [h₃, F.map_comp, Category.assoc, h₂, ← MonoidalCategory.tensorHom_comp_tensorHom,
    ← reassoc_of% h₁]

/-- `(m ≫ (x ⊗ y)) ≫ (z ⊗ 𝟙) = m ≫ ((x ≫ z) ⊗ y)`. -/
theorem CategoryTheory.MonoidalCategory.comp_tensorHom_comp_tensorHom_id {𝒞 : Type*}
    [Category 𝒞] [MonoidalCategory 𝒞] {P A₁ A₂ B₁ B₂ C₁ : 𝒞} (m : P ⟶ A₁ ⊗ A₂) (x : A₁ ⟶ B₁)
    (y : A₂ ⟶ B₂) (z : B₁ ⟶ C₁) :
    (m ≫ (x ⊗ₘ y)) ≫ (z ⊗ₘ 𝟙 B₂) = m ≫ ((x ≫ z) ⊗ₘ y) := by
  rw [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

section Divisors

open AlgebraicGeometry Stacks.SheafOfModules.Invertible

namespace Stacks.Divisors

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- **Two base-change comparisons of the conormal source along the same morphism**: the inverse
of the first followed by the second is the tensor product of the comparisons of the kernels and
of the inverse lines. -/
theorem conormalSourceBaseChange_inv_comp_hom
    (E : X.Modules) (E₁ E₂ : X'.Modules)
    (hE₁ : E₁ ≅ (Scheme.Modules.pullback g).obj E) (hE₂ : E₂ ≅ (Scheme.Modules.pullback g).obj E)
    (Q : InvertibleQuotient X E) (Q₁ : InvertibleQuotient X' E₁) (Q₂ : InvertibleQuotient X' E₂)
    (hL₁ : Q₁.L ≅ (Scheme.Modules.pullback g).obj Q.L)
    (hL₂ : Q₂.L ≅ (Scheme.Modules.pullback g).obj Q.L)
    (hq₁ : Q₁.q ≫ hL₁.hom = hE₁.hom ≫ (Scheme.Modules.pullback g).map Q.q)
    (hq₂ : Q₂.q ≫ hL₂.hom = hE₂.hom ≫ (Scheme.Modules.pullback g).map Q.q) :
    letI := Q₁.invertible
    letI := Q₂.invertible
    (conormalSourceBaseChange g E E₁ hE₁ Q Q₁ hL₁ hq₁).inv ≫
        (conormalSourceBaseChange g E E₂ hE₂ Q Q₂ hL₂ hq₂).hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X'.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X'.presheaf) (forget₂ CommRingCat RingCat)
            (X'.ringCatSheaf.2)⟩).map
          ((quotientKernelBaseChange g E E₁ hE₁ Q Q₁ hL₁ hq₁).1.inv ≫
            (quotientKernelBaseChange g E E₂ hE₂ Q Q₂ hL₂ hq₂).1.hom)).app
          (tensorPower X'.presheaf X'.ringCatSheaf.2 Q₁.L (-1)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X'.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X'.presheaf) (forget₂ CommRingCat RingCat)
            (X'.ringCatSheaf.2)⟩).obj
          (kernel Q₂.q)).map
          ((inverseQuotientBaseChange g E E₁ Q Q₁ hL₁).inv ≫
            (inverseQuotientBaseChange g E E₂ Q Q₂ hL₂).hom) := by
  let := Q.invertible
  let := Q₁.invertible
  let := Q₂.invertible
  refine (congrArg₂ (· ≫ ·) (conormalSourceBaseChange_inv g E E₁ hE₁ Q Q₁ hL₁ hq₁)
    (conormalSourceBaseChange_hom g E E₂ hE₂ Q Q₂ hL₂ hq₂)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _)).trans ?_
  refine (congrArg₂ (· ≫ ·) (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ _ _).symm
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ _ _).symm).trans ?_
  refine ((Functor.uncurry.obj _).map_comp _ _).symm.trans ?_
  exact (Functor.uncurry_obj_map _ _).trans rfl

end Stacks.Divisors

end Divisors

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite)
  {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
  {T T' : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1) (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T)
  (hvh : v ≫ g.hom = yoneda.map h ≫ u)

/-- The inverse of the composition comparison of Stacks 03LU at a morphism of represented
algebraic spaces and a scheme point, in the two spellings of the morphism of represented
spaces. -/
theorem modulePullbackCompIso_inv_app_representedSpaceMap_pointHom {T T' : BigFppfOver B S hS}
    (h : T' ⟶ T) (x : yoneda.obj T ⟶ X.1) (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).inv.app M =
      eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj M)
          (rfl : pointHom (yoneda.map h ≫ x) = yonedaSpaceMap h ≫ pointHom x)) ≫
        (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).inv.app M := by
  refine (eq_of_heq ?_).trans (Category.id_comp _).symm
  refine modulePullbackCompIso_app_inv_heq ?_ ?_ _ _ ?_ _ _ ?_ ?_
  · exact rfl
  · exact rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact rfl

/-- **The base change of the Zariski reading at a scheme point, in the spelling of the
morphism of represented spaces of `ConormalChartSourceCompat`.** -/
theorem pointZariskiModuleBaseChangeIso_hom_eq_yonedaSpaceMap {T T' : BigFppfOver B S hS}
    (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    (pointZariskiModuleBaseChangeIso X M hM x h).hom =
      CategoryTheory.Functor.conormalGlueComparison
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
        (zariskiReadingFunctor T') (Ku := ((modulePullback B S hS (pointHom x)).obj M))
        (Kx := (modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj M)
        (N := ((modulePullback B S hS (yonedaSpaceMap h)).obj
          ((modulePullback B S hS (pointHom x)).obj M)))
        (eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj M)
          (rfl : pointHom (yoneda.map h ≫ x) = yonedaSpaceMap h ≫ pointHom x)) ≫
        (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).inv.app M)
        (zariskiReadingPullbackIso h ((modulePullback B S hS (pointHom x)).obj M)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) M
            hM)).inv :=
  congrArg (fun f => (zariskiReadingFunctor T').map f ≫
      (zariskiReadingPullbackIso h ((modulePullback B S hS (pointHom x)).obj M)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) M
          hM)).inv)
    (modulePullbackCompIso_inv_app_representedSpaceMap_pointHom X h x M)

/-- The comparison `v^*g^* ≅ (u ∘ h)^*`, unfolded. -/
theorem pointPullbackCompIso_eq :
    pointPullbackCompIso X g u v h hvh = (modulePullbackCompIso B S hS (pointHom v) g ≪≫
    eqToIso (congrArg (modulePullback B S hS)
      (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g = pointHom (X := X) (yoneda.map h ≫ u)))) :=
  rfl

/-- The comparison `v^*g^* ≅ (u ∘ h)^*` at a module, unfolded. -/
theorem pointPullbackCompIso_hom_app (K : Modules.{u, u} B S hS X.1 X.2) :
    (pointPullbackCompIso X g u v h hvh).hom.app K =
      (modulePullbackCompIso B S hS (pointHom v) g ≪≫
    eqToIso (congrArg (modulePullback B S hS)
      (ObjectProperty.hom_ext _ hvh :
        pointHom v ≫ g = pointHom (X := X) (yoneda.map h ≫ u)))).hom.app K :=
  congrArg (fun i => i.hom.app K) (pointPullbackCompIso_eq X g u v h hvh)

/-- The comparison of `ConormalChartSourceCompat` at a module, through the unfolded comparison
`v^*g^* ≅ (u ∘ h)^*`. -/
theorem pointPullbackCompIso_glue_inv_app_aux (K : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫
        eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh :
          pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
        (modulePullbackCompIso B S hS (pointHom v) g).symm).inv.app K =
      (modulePullbackCompIso B S hS (pointHom v) g ≪≫
    eqToIso (congrArg (modulePullback B S hS)
      (ObjectProperty.hom_ext _ hvh :
        pointHom v ≫ g = pointHom (X := X) (yoneda.map h ≫ u)))).hom.app K ≫
        (eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj K)
          (rfl : pointHom (yoneda.map h ≫ u) = yonedaSpaceMap h ≫ pointHom u)) ≫
        (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u)).inv.app K) :=
  CategoryTheory.NatIso.trans_eqToIso_symm_inv_app _ _ _ _ K _

/-- **The comparison of `ConormalChartSourceCompat` at a module** is `v^*g^* ≅ (u ∘ h)^*`
followed by the inverse of Stacks 03LU for `h` and `u`. -/
theorem pointPullbackCompIso_glue_inv_app (K : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫
        eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh :
          pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
        (modulePullbackCompIso B S hS (pointHom v) g).symm).inv.app K =
      (pointPullbackCompIso X g u v h hvh).hom.app K ≫
        (eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj K)
          (rfl : pointHom (yoneda.map h ≫ u) = yonedaSpaceMap h ≫ pointHom u)) ≫
        (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u)).inv.app K) :=
  (pointPullbackCompIso_glue_inv_app_aux X g u v h hvh K).trans
    (congrArg (· ≫ _) (pointPullbackCompIso_hom_app X g u v h hvh K).symm)

/-- **The comparison of the source readings in `ConormalChartSourceCompat` is the comparison
`v^*g^* ≅ (u ∘ h)^*` followed by the base change of the Zariski reading at `u`.** -/
theorem conormalGlueComparison_eq_pointPullbackCompIso {K : Modules.{u, u} B S hS X.1 X.2}
    (hK : K.IsQuasicoherentOnSite) :
    CategoryTheory.Functor.conormalGlueComparison
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
        (zariskiReadingFunctor T') (Ku := ((modulePullback B S hS (pointHom u)).obj K))
        (Kx := ((modulePullback B S hS (pointHom v)).obj ((modulePullback B S hS g).obj K)))
        (N := ((modulePullback B S hS (yonedaSpaceMap h)).obj
          ((modulePullback B S hS (pointHom u)).obj K)))
        ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫
          eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh :
            pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
          (modulePullbackCompIso B S hS (pointHom v) g).symm).inv.app K)
        (zariskiReadingPullbackIso h ((modulePullback B S hS (pointHom u)).obj K)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom u) K
            hK)).inv =
      (zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).hom.app K) ≫
        (pointZariskiModuleBaseChangeIso X K hK u h).hom := by
  refine Eq.trans ?_ (congrArg (_ ≫ ·)
    (pointZariskiModuleBaseChangeIso_hom_eq_yonedaSpaceMap X u h K hK).symm)
  unfold CategoryTheory.Functor.conormalGlueComparison
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine congrArg (· ≫ _) ?_
  refine Eq.trans ?_ ((zariskiReadingFunctor T').map_comp _ _)
  exact congrArg (zariskiReadingFunctor T').map (pointPullbackCompIso_glue_inv_app X g u v h hvh K)

variable (Q : InvertibleQuotient X E)

/-- The base change of the Zariski reading at the conormal source, in the spelling of the
conormal source as a tensor product. -/
theorem pointZariskiModuleBaseChangeIso_sectionConormalSource :
    (pointZariskiModuleBaseChangeIso X (sectionConormalSource X E Q)
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q) u h) =
    (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      Q.L := Q.invertible.toAlgebraicGeometry
    pointZariskiModuleBaseChangeIso X
        (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)))
        (isQuasicoherentOnSite_sectionConormalSource X E hE Q) u h) := rfl

/-- **The source square over two spaces from the source square along `h` at `u`**: given the
compatibility `hsq` of the source readings at `u` and `u ∘ h` with the base change along `h`
(the square of `existsUnique_sectionConormalIso_of`) and the comparison `hg` at `T'` of the
reading at `v` on `X'` with the reading at `u ∘ h` on `X`, the source readings are compatible
with the base change of the conormal source along `pointZariskiModuleTwoSpaceIso`. -/
theorem conormalSource_twoSpace_of
    (s : (∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          Q.L := Q.invertible.toAlgebraicGeometry;
        (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))))) ⟶
      (letI := (sectionPointQuotient X E hE Q T x).invertible;
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
            (kernel (sectionPointQuotient X E hE Q T x).q)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower
            ((BigFppfOver.toScheme B S hS).obj T).presheaf
            ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1))))))
    (s' : (∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'.1),
      (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
        (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L :=
            (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry;
        (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X'.1 X'.2)
          (kernel (Q.baseChange g (Iso.refl _)).q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
            (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))))) ⟶
      (letI := (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T x).invertible;
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
            (kernel (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
              (Q.baseChange g (Iso.refl _)) T x).q)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower
            ((BigFppfOver.toScheme B S hS).obj T).presheaf
            ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
              (Q.baseChange g (Iso.refl _)) T x).L (-1))))))
    (hsq :
      haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        Q.L := Q.invertible.toAlgebraicGeometry
      (pointZariskiModuleBaseChangeIso X
        (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)))
        (isQuasicoherentOnSite_sectionConormalSource X E hE Q) u h).hom ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map (s T u) ≫
      (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X E T' (yoneda.map h ≫ u))
        (pointZariskiModuleBaseChangeIso X E hE u h) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ u))
        (sectionPointQuotientBaseChangeL X E hE Q u h)
        (sectionPointQuotient_baseChange_q X E hE Q u h)).hom =
      s T' (yoneda.map h ≫ u))
    (hg : (zariskiReadingFunctor T').map
        ((pointPullbackCompIso X g u v h hvh).hom.app (sectionConormalSource X E Q)) ≫
        s T' (yoneda.map h ≫ u) ≫
        (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X E T' (yoneda.map h ≫ u))
        (pointZariskiModuleBaseChangeIso X E hE u h) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ u))
        (sectionPointQuotientBaseChangeL X E hE Q u h)
        (sectionPointQuotient_baseChange_q X E hE Q u h)).inv ≫
        (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T' v)
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)
        (sectionPointQuotient_twoSpace_q X E hE g u v h hvh Q)).hom =
      (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map
        (sectionConormalSourceBaseChangeHom X E Q g)) ≫ s' T' v) :
    (CategoryTheory.Functor.conormalGlueComparison
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
        (zariskiReadingFunctor T')
        (Ku := ((modulePullback B S hS (pointHom u)).obj (sectionConormalSource X E Q)))
        (Kx := ((modulePullback B S hS (pointHom v)).obj
          ((modulePullback B S hS g).obj (sectionConormalSource X E Q))))
        (N := ((modulePullback B S hS (yonedaSpaceMap h)).obj
          ((modulePullback B S hS (pointHom u)).obj (sectionConormalSource X E Q))))
        ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫
          eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh :
            pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
          (modulePullbackCompIso B S hS (pointHom v) g).symm).inv.app
            (sectionConormalSource X E Q))
        (zariskiReadingPullbackIso h
          ((modulePullback B S hS (pointHom u)).obj (sectionConormalSource X E Q))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom u)
            (sectionConormalSource X E Q)
            (isQuasicoherentOnSite_sectionConormalSource X E hE Q))).inv) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map (s T u) ≫
        (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T' v)
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)
        (sectionPointQuotient_twoSpace_q X E hE g u v h hvh Q)).hom =
      (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map
        (sectionConormalSourceBaseChangeHom X E Q g)) ≫ s' T' v := by
  refine CategoryTheory.comp_twoSpaceSource_paste _ _ _ _ _ _ _ _ _ ?hx hsq ?hinv hg
  case hinv => exact Iso.hom_inv_id _
  case hx =>
    refine (conormalGlueComparison_eq_pointPullbackCompIso X g u v h hvh
      (K := sectionConormalSource X E Q)
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q)).trans ?_
    exact congrArg (_ ≫ ·) (congrArg Iso.hom
      (pointZariskiModuleBaseChangeIso_sectionConormalSource X E hE u h Q))

/-- The base change of the Zariski reading at `u` followed by the inverse of the two-space
identification is the reading of the comparison `(u ∘ h)^* ≅ v^*g^*`. -/
theorem pointZariskiModuleBaseChangeIso_hom_comp_twoSpaceIso_inv :
    (pointZariskiModuleBaseChangeIso X E hE u h).hom ≫
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh).inv =
      (zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).inv.app E) :=
  Iso.hom_inv_id_assoc _ _


/-- **The kernel inclusions under `(u ∘ h)^* ≅ v^*g^*`**: the comparison carries the inverse
image of `Ker(q) ⟶ ℰ` along `u ∘ h` to the inverse image along `v` of the comparison of kernels
along `g` followed by the inclusion of `Ker(g^*q)`. -/
theorem pointPullbackCompIso_inv_app_kernel_ι :
    haveI := preservesZeroMorphisms_modulePullback B S hS g
    (modulePullback B S hS (pointHom (X := X) (yoneda.map h ≫ u))).map (kernel.ι Q.q) ≫
        (pointPullbackCompIso X g u v h hvh).inv.app E =
      ((pointPullbackCompIso X g u v h hvh).inv.app (kernel Q.q) ≫
        (modulePullback B S hS (pointHom v)).map (kernelComparison Q.q (modulePullback B S hS g) ≫
          (kernelBaseChangeIso X E Q g).hom)) ≫
        (modulePullback B S hS (pointHom v)).map (kernel.ι (Q.baseChange g (Iso.refl _)).q) := by
  have := preservesZeroMorphisms_modulePullback B S hS g
  refine ((pointPullbackCompIso X g u v h hvh).inv.naturality (kernel.ι Q.q)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) ?_
  refine Eq.trans ?_ ((modulePullback B S hS (pointHom v)).map_comp _ _)
  refine congrArg (modulePullback B S hS (pointHom v)).map ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans (kernelComparison_comp_ι _ _).symm (congrArg (_ ≫ ·) ?_)
  exact (kernelIsoOfEq_hom_comp_ι _).symm

/-- **The kernel factors of the source readings at `u ∘ h` on `X` and at `v` on `X'` are
intertwined** by the comparison of the two kernel base changes of Stacks 0B3V along `h` and the
comparison `(u ∘ h)^* ≅ v^*g^*` followed by the comparison of kernels along `g`. -/
theorem kernelPointReadingHom_twoSpace :
    kernelPointReadingHom X E hE Q T' (yoneda.map h ≫ u) ≫
      ((Stacks.Divisors.quotientKernelBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X E T' (yoneda.map h ≫ u))
        (pointZariskiModuleBaseChangeIso X E hE u h) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ u))
        (sectionPointQuotientBaseChangeL X E hE Q u h)
        (sectionPointQuotient_baseChange_q X E hE Q u h)).1.inv ≫
       (Stacks.Divisors.quotientKernelBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T' v)
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)
        (sectionPointQuotient_twoSpace_q X E hE g u v h hvh Q)).1.hom) =
    (haveI := preservesZeroMorphisms_modulePullback B S hS g
     (zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).inv.app (kernel Q.q) ≫
        (modulePullback B S hS (pointHom v)).map (kernelComparison Q.q (modulePullback B S hS g) ≫
          (kernelBaseChangeIso X E Q g).hom))) ≫
      kernelPointReadingHom X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        (Q.baseChange g (Iso.refl _)) T' v := by
  have := preservesZeroMorphisms_modulePullback B S hS g
  refine CategoryTheory.comp_inv_comp_hom_eq_of_comp_ι _ _ _ _ _ _ _ _
    (Stacks.Divisors.quotientKernelBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X E T' (yoneda.map h ≫ u))
        (pointZariskiModuleBaseChangeIso X E hE u h) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ u))
        (sectionPointQuotientBaseChangeL X E hE Q u h)
        (sectionPointQuotient_baseChange_q X E hE Q u h)).2
    (Stacks.Divisors.quotientKernelBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T' v)
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)
        (sectionPointQuotient_twoSpace_q X E hE g u v h hvh Q)).2 _ _ ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg₂ (· ≫ ·) (kernelPointReadingHom_comp_ι X E hE Q T' (yoneda.map h ≫ u))
    (pointZariskiModuleBaseChangeIso_hom_comp_twoSpaceIso_inv X E hE g u v h hvh)).trans ?_
  refine ((zariskiReadingFunctor T').map_comp _ _).symm.trans ?_
  refine (congrArg (zariskiReadingFunctor T').map
    (pointPullbackCompIso_inv_app_kernel_ι X E g u v h hvh Q)).trans ?_
  refine ((zariskiReadingFunctor T').map_comp _ _).trans ?_
  exact congrArg (_ ≫ ·) (kernelPointReadingHom_comp_ι X' ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
    (Q.baseChange g (Iso.refl _)) T' v).symm

/-- **The comparison `v^*g^* ≅ (u ∘ h)^*` is monoidal** (Stacks 03EL and 03LU). -/
theorem pointPullbackCompIso_hom_app_tensor (K₁ K₂ : Modules.{u, u} B S hS X.1 X.2) :
    (pointPullbackCompIso X g u v h hvh).hom.app (K₁ ⊗ K₂) ≫
        (modulePullbackTensorIso B S hS (pointHom (X := X) (yoneda.map h ≫ u)) K₁ K₂).hom =
      (modulePullback B S hS (pointHom v)).map (modulePullbackTensorIso B S hS g K₁ K₂).hom ≫
        (modulePullbackTensorIso B S hS (pointHom v) _ _).hom ≫
          ((pointPullbackCompIso X g u v h hvh).hom.app K₁ ⊗ₘ
            (pointPullbackCompIso X g u v h hvh).hom.app K₂) := by
  rw [pointPullbackCompIso_eq]
  have key : ∀ (φ : yonedaSpace B S hS T' ⟶ X) (p : pointHom v ≫ g = φ),
      (modulePullbackCompIso B S hS (pointHom v) g ≪≫
          eqToIso (congrArg (modulePullback B S hS) p)).hom.app (K₁ ⊗ K₂) ≫
        (modulePullbackTensorIso B S hS φ K₁ K₂).hom =
      (modulePullback B S hS (pointHom v)).map (modulePullbackTensorIso B S hS g K₁ K₂).hom ≫
        (modulePullbackTensorIso B S hS (pointHom v) _ _).hom ≫
          ((modulePullbackCompIso B S hS (pointHom v) g ≪≫
              eqToIso (congrArg (modulePullback B S hS) p)).hom.app K₁ ⊗ₘ
            (modulePullbackCompIso B S hS (pointHom v) g ≪≫
              eqToIso (congrArg (modulePullback B S hS) p)).hom.app K₂) := by
    intro φ p
    subst p
    simp only [eqToIso_refl, Iso.trans_refl]
    exact modulePullbackCompIso_hom_app_tensor (f := pointHom v) (g := g) (F := K₁) (G := K₂)
  exact key (pointHom (X := X) (yoneda.map h ≫ u)) (ObjectProperty.hom_ext _ hvh)

/-- The monoidality of `v^*g^* ≅ (u ∘ h)^*`, with the inverse comparisons in the factors. -/
theorem pointPullbackCompIso_hom_app_tensor_inv (K₁ K₂ : Modules.{u, u} B S hS X.1 X.2) :
    (pointPullbackCompIso X g u v h hvh).hom.app (K₁ ⊗ K₂) ≫
        (modulePullbackTensorIso B S hS (pointHom (X := X) (yoneda.map h ≫ u)) K₁ K₂).hom ≫
          ((pointPullbackCompIso X g u v h hvh).inv.app K₁ ⊗ₘ
            (pointPullbackCompIso X g u v h hvh).inv.app K₂) =
      (modulePullback B S hS (pointHom v)).map (modulePullbackTensorIso B S hS g K₁ K₂).hom ≫
        (modulePullbackTensorIso B S hS (pointHom v) _ _).hom := by
  rw [← Category.assoc, pointPullbackCompIso_hom_app_tensor X g u v h hvh K₁ K₂]
  simp only [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app]
  exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) (MonoidalCategory.id_tensorHom_id _ _)).trans
    (Category.comp_id _))

/-- **The tensor square of the source readings at `u ∘ h` on `X` and at `v` on `X'`, on the
represented space**, with the conormal source spelled as a tensor product: the comparison
`v^*g^* ≅ (u ∘ h)^*`, Stacks 03EL along `u ∘ h` and the factorwise comparisons followed by the
base changes along `g` of the kernel and of the inverse line, is the base change along `g` of the
conormal source followed by Stacks 03EL along `v`. -/
theorem pointPullbackCompIso_kernelTensorInverse_baseChange :
    haveI hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      Q.L := Q.invertible.toAlgebraicGeometry
    haveI := isInvertible_modulePullback_obj B S hS g Q.L hQ
    haveI := preservesZeroMorphisms_modulePullback B S hS g
    haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
      (Q.baseChange g (Iso.refl _)).L :=
        (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry
    (pointPullbackCompIso X g u v h hvh).hom.app (kernel Q.q ⊗
          Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)) ≫
        (modulePullbackTensorIso B S hS (pointHom (X := X) (yoneda.map h ≫ u)) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫
        (((pointPullbackCompIso X g u v h hvh).inv.app (kernel Q.q) ≫
            (modulePullback B S hS (pointHom v)).map
              (kernelComparison Q.q (modulePullback B S hS g) ≫
                (kernelBaseChangeIso X E Q g).hom)) ⊗ₘ
          ((pointPullbackCompIso X g u v h hvh).inv.app
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                (structureRingSheaf B S hS X).property Q.L (-1)) ≫
            (modulePullback B S hS (pointHom v)).map
              (modulePullbackTensorPowerIso g Q.L (-1)).hom)) =
      (modulePullback B S hS (pointHom v)).map (sectionConormalSourceBaseChangeHom X E Q g) ≫
        (modulePullbackTensorIso B S hS (pointHom v) (kernel (Q.baseChange g (Iso.refl _)).q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
            (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))).hom := by
  refine CategoryTheory.Functor.comp_tensorHom_comp_map_eq_of_tensor
    (modulePullback B S hS g) (modulePullback B S hS (pointHom v)) _ _ _ _
    (modulePullbackTensorIso B S hS g (kernel Q.q)
      (haveI hQ : IsInvertible (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L := Q.invertible.toAlgebraicGeometry
       Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))).hom
    (modulePullbackTensorIso B S hS (pointHom v) _ _).hom _ _ _ _ ?h1 ?h2 ?h3
  case h1 => exact pointPullbackCompIso_hom_app_tensor_inv X g u v h hvh _ _
  case h2 => exact modulePullbackTensorIso_hom_naturality B S hS (pointHom v) _ _
  case h3 =>
    unfold sectionConormalSourceBaseChangeHom modulePullbackKernelTensorInverseHom
    exact CategoryTheory.MonoidalCategory.comp_tensorHom_comp_tensorHom_id _ _ _ _

/-- The comparison `v^*g^* ≅ (u ∘ h)^*` at the conormal source, in the spelling of the conormal
source as a tensor product. -/
theorem pointPullbackCompIso_hom_app_sectionConormalSource :
    (pointPullbackCompIso X g u v h hvh).hom.app (sectionConormalSource X E Q) =
      (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        Q.L := Q.invertible.toAlgebraicGeometry
      (pointPullbackCompIso X g u v h hvh).hom.app (kernel Q.q ⊗
          Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))) :=
  eq_of_heq (congr_arg_heq (fun P => (pointPullbackCompIso X g u v h hvh).hom.app P) rfl)

/-- **The tensor square of the source readings at `u ∘ h` on `X` and at `v` on `X'`, on the
represented space**: the comparison `v^*g^* ≅ (u ∘ h)^*` at the conormal source, Stacks 03EL
along `u ∘ h` and the factorwise comparisons followed by the base changes along `g` of the kernel
and of the inverse line, is the base change along `g` of the conormal source followed by
Stacks 03EL along `v`. -/
theorem pointPullbackCompIso_sectionConormalSource_baseChange :
    haveI hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      Q.L := Q.invertible.toAlgebraicGeometry
    haveI := isInvertible_modulePullback_obj B S hS g Q.L hQ
    haveI := preservesZeroMorphisms_modulePullback B S hS g
    haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
      (Q.baseChange g (Iso.refl _)).L :=
        (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry
    (pointPullbackCompIso X g u v h hvh).hom.app (sectionConormalSource X E Q) ≫
        (modulePullbackTensorIso B S hS (pointHom (X := X) (yoneda.map h ≫ u)) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫
        (((pointPullbackCompIso X g u v h hvh).inv.app (kernel Q.q) ≫
            (modulePullback B S hS (pointHom v)).map
              (kernelComparison Q.q (modulePullback B S hS g) ≫
                (kernelBaseChangeIso X E Q g).hom)) ⊗ₘ
          ((pointPullbackCompIso X g u v h hvh).inv.app
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                (structureRingSheaf B S hS X).property Q.L (-1)) ≫
            (modulePullback B S hS (pointHom v)).map
              (modulePullbackTensorPowerIso g Q.L (-1)).hom)) =
      (modulePullback B S hS (pointHom v)).map (sectionConormalSourceBaseChangeHom X E Q g) ≫
        (modulePullbackTensorIso B S hS (pointHom v) (kernel (Q.baseChange g (Iso.refl _)).q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
            (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))).hom :=
  CategoryTheory.comp_eq_of_eq_of_comp_eq
    (pointPullbackCompIso_hom_app_sectionConormalSource X E g u v h hvh Q)
    (pointPullbackCompIso_kernelTensorInverse_baseChange X E g u v h hvh Q)

/-- **The tensor square of the source readings at `u ∘ h` on `X` and at `v` on `X'`**: after
the Zariski reading at `T'`, the comparison `v^*g^* ≅ (u ∘ h)^*` at the conormal source followed
by the tensor comparison of the reading at `u ∘ h` and the tensor product of the readings of the
kernel and inverse-line comparisons is the reading of the base change of the conormal source
along `g` followed by the tensor comparison of the reading at `v`. -/
theorem conormalSourceTensorReading_twoSpace :
    haveI hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      Q.L := Q.invertible.toAlgebraicGeometry
    haveI := isInvertible_modulePullback_obj B S hS g Q.L hQ
    haveI := preservesZeroMorphisms_modulePullback B S hS g
    haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
      (Q.baseChange g (Iso.refl _)).L :=
        (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry
    (zariskiReadingFunctor T').map
        ((pointPullbackCompIso X g u v h hvh).hom.app (sectionConormalSource X E Q)) ≫
      ((zariskiReadingFunctor T').map
          (modulePullbackTensorIso B S hS (pointHom (X := X) (yoneda.map h ≫ u)) (kernel Q.q)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫
        ((zariskiReadingTensorObjIso T'
            ((modulePullback B S hS (pointHom (X := X) (yoneda.map h ≫ u))).obj (kernel Q.q))
            ((modulePullback B S hS (pointHom (X := X) (yoneda.map h ≫ u))).obj
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                (structureRingSheaf B S hS X).property Q.L (-1)))
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
              (pointHom (X := X) (yoneda.map h ≫ u)) (kernel Q.q)
              (isQuasicoherentOnSite_kernel_q X E hE Q))
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
              (pointHom (X := X) (yoneda.map h ≫ u))
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                (structureRingSheaf B S hS X).property Q.L (-1))
              (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
            ((zariskiReadingFunctor T').obj
              ((modulePullback B S hS (pointHom (X := X) (yoneda.map h ≫ u))).obj (kernel Q.q)))
            ((zariskiReadingFunctor T').obj
              ((modulePullback B S hS (pointHom (X := X) (yoneda.map h ≫ u))).obj
                (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                  (structureRingSheaf B S hS X).property Q.L (-1))))).hom)) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩).map
        ((zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).inv.app (kernel Q.q) ≫
            (modulePullback B S hS (pointHom v)).map
              (kernelComparison Q.q (modulePullback B S hS g) ≫
              (kernelBaseChangeIso X E Q g).hom)))).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat)
            ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩).obj _).map
        ((zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).inv.app
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                (structureRingSheaf B S hS X).property Q.L (-1)) ≫
            (modulePullback B S hS (pointHom v)).map
              (modulePullbackTensorPowerIso g Q.L (-1)).hom)) =
    (zariskiReadingFunctor T').map
        ((modulePullback B S hS (pointHom v)).map (sectionConormalSourceBaseChangeHom X E Q g)) ≫
      ((zariskiReadingFunctor T').map
          (modulePullbackTensorIso B S hS (pointHom v) (kernel (Q.baseChange g (Iso.refl _)).q)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
              (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))).hom ≫
        ((zariskiReadingTensorObjIso T'
            ((modulePullback B S hS (pointHom v)).obj (kernel (Q.baseChange g (Iso.refl _)).q))
            ((modulePullback B S hS (pointHom v)).obj
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
                (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1)))
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom v)
              (kernel (Q.baseChange g (Iso.refl _)).q)
              (isQuasicoherentOnSite_kernel_q X' ((modulePullback B S hS g).obj E)
                (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
                (Q.baseChange g (Iso.refl _))))
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom v)
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
                (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))
              (isQuasicoherentOnSite_invertibleTensorPower X' (Q.baseChange g (Iso.refl _)).L
                (-1)))).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
            ((zariskiReadingFunctor T').obj
              ((modulePullback B S hS (pointHom v)).obj (kernel (Q.baseChange g (Iso.refl _)).q)))
            ((zariskiReadingFunctor T').obj
              ((modulePullback B S hS (pointHom v)).obj
                (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
                  (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L
                  (-1))))).hom)) := by
  refine CategoryTheory.Functor.map_comp_reading_square
    (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules) (iℬ := Scheme.Modules.instCategory)
    _ _ _ _ _
    (MonoidalCategory.tensorHom
        (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
      (have := preservesZeroMorphisms_modulePullback B S hS g
       (pointPullbackCompIso X g u v h hvh).inv.app (kernel Q.q) ≫
            (modulePullback B S hS (pointHom v)).map
              (kernelComparison Q.q (modulePullback B S hS g) ≫
              (kernelBaseChangeIso X E Q g).hom))
      (have hQ : IsInvertible (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L := Q.invertible.toAlgebraicGeometry
       (pointPullbackCompIso X g u v h hvh).inv.app
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                (structureRingSheaf B S hS X).property Q.L (-1)) ≫
            (modulePullback B S hS (pointHom v)).map
              (modulePullbackTensorPowerIso g Q.L (-1)).hom))
    _ _ _ _ _ ?hnat ?hsp
  case hnat => exact zariskiReadingTensorObjIso_bifunctorNaturalitySquare T' _ _ _ _ _ _
  case hsp => exact pointPullbackCompIso_sectionConormalSource_baseChange X E g u v h hvh Q

end AlgebraicGeometry.Space

end
