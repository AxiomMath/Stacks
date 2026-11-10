module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.AffineRing
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.System
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints

/-!
# Stacks 09RE over a directed system of spectra

Let `R ⟶ A_i` be a directed system of `R`-algebras with colimit `A`, and consider the system of
spectra `Spec A_i` over `Spec R` with vertex `Spec A`. This file proves the affine case of
Stacks 09RE for it, at the derived sheafifications of a complex `P` of finitely presented
projective `R`-modules and of a K-flat complex `N` of `R`-modules, under a degree bound making
only finitely many degrees of `P` relevant: `Hom(L(Spec A)^*P̃, L(Spec A)^*Ñ)` is the filtered
colimit of the `Hom(L(Spec A_i)^*P̃, L(Spec A_i)^*Ñ)`.

## Main definitions

* `Stacks.LimitHomDescent.Affine.RingSystem`: a directed system of `R`-algebras with a cocone.
* `Stacks.LimitHomDescent.Affine.RingSystem.toSchemeSystem`: its system of spectra.

## Main results

* `Stacks.LimitHomDescent.Affine.Φ_bijective`: the identification `Φ` of morphism sets is
  bijective when `A ⊗_R P` is K-projective.
* `Stacks.LimitHomDescent.Affine.RingSystem.isColim_toSchemeSystem`: the morphism set over
  `Spec A` is the filtered colimit of the morphism sets over the `Spec A_i`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ChangeOfRings TensorProduct
open Stacks.DerivedPullback (schemeFactorIso schemeFactorHom)
open Stacks.FilteredColimitHom (Qh)

attribute [local instance 10000] HasDerivedCategory.standard

universe v u

namespace Stacks.LimitHomDescent.Affine

/-- **A directed system of `R`-algebras with a cocone.** -/
structure RingSystem (R : CommRingCat.{u}) (J : Type v) [Preorder J] where
  /-- The algebra at a stage. -/
  A : J → CommRingCat.{u}
  /-- The structure map `R ⟶ A_j`. -/
  φ : ∀ j, R ⟶ A j
  /-- The transition maps. -/
  β : ∀ {i j : J}, i ≤ j → (A i ⟶ A j)
  φ_β : ∀ {i j : J} (h : i ≤ j), φ i ≫ β h = φ j
  β_β : ∀ {i j k : J} (h : i ≤ j) (h' : j ≤ k), β h ≫ β h' = β (h.trans h')
  β_refl : ∀ i : J, β (le_refl i) = 𝟙 (A i)
  /-- The vertex. -/
  lim : CommRingCat.{u}
  /-- The structure map `R ⟶ A`. -/
  φlim : R ⟶ lim
  /-- The maps to the vertex. -/
  γ : ∀ j, A j ⟶ lim
  φ_γ : ∀ j : J, φ j ≫ γ j = φlim
  β_γ : ∀ {i j : J} (h : i ≤ j), β h ≫ γ j = γ i

/-! ### Morphisms out of `P̃` along a map of spectra -/

section Transpose

variable {R A A' : CommRingCat.{u}}

/-- The transpose of a morphism of complexes `P ⟶ A ⊗_R N` along extension of scalars. -/
def transposeCx (f : R ⟶ A) {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {Z : CochainComplex (ModuleCat.{u} A) ℤ}
    (g : P ⟶
      ((ModuleCat.restrictScalars.{u} f.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) :
    (ext f).obj P ⟶ Z :=
  ((Adjunction.mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom)
    (ComplexShape.up ℤ)).homEquiv P Z).symm g

/-- Transposing along `f ≫ β` the composite of `g` with the base-change map `A ⊗_R N ⟶ A' ⊗_R N`
is the extension along `β` of the transpose of `g` along `f`, up to the isomorphisms
`extComp f β`. -/
theorem transposeCx_comp_tau₀ (f : R ⟶ A) (β : A ⟶ A') {P N : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : P ⟶ ((resExt f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :
    transposeCx (f ≫ β) (Z := (ext (f ≫ β)).obj N)
        (g ≫ (NatTrans.mapHomologicalComplex (tau₀ f β) (ComplexShape.up ℤ)).app N) =
      (extComp f β P).inv ≫ (ext β).map (transposeCx f (Z := (ext f).obj N) g) ≫
        (extComp f β N).hom := by
  ext n : 1
  exact homEquiv_symm_comp_tau₀ f β (g.f n)

end Transpose

/-! ### The identification of the morphism sets -/

section Phi

variable {R A A' : CommRingCat.{u}} (P N : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
  (hN : N.KFlat)

/-- **`Hom_{K(R)}(P, A ⊗_R N) ⟶ Hom(L(Spec f)^*P̃, L(Spec f)^*Ñ)`**: transpose along extension of
scalars, pass to the derived category of `A`, sheafify, and read the result through `Θ`. -/
def Φ (f : R ⟶ A)
    (ψ : (Qh R).obj P ⟶ (Qh R).obj (((resExt f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) :
    (pb (Spec.map f)).obj ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ⟶
      (pb (Spec.map f)).obj ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj N)) :=
  (Θ f P hP).hom ≫
    (tilde.functor A).mapDerivedCategory.map
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.app ((ext f).obj P) ≫
      DerivedCategory.Qh.map (((Adjunction.mapHomotopyCategoryAdjunction
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom) (ComplexShape.up ℤ)).homEquiv
          ((Qh R).obj P) ((Qh A).obj ((ext f).obj N))).symm ψ) ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app ((ext f).obj N)) ≫
    (Θ f N hN).inv

/-- Conjugating `Qh` of the class of a morphism of complexes `h` by `quotientCompQhIso` gives
`Q.map h`. -/
theorem quotientCompQhIso_conj {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
    {X Y : CochainComplex 𝒜 ℤ} (h : X ⟶ Y) :
    (DerivedCategory.quotientCompQhIso 𝒜).inv.app X ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map h) ≫
        (DerivedCategory.quotientCompQhIso 𝒜).hom.app Y = DerivedCategory.Q.map h :=
  ((DerivedCategory.quotientCompQhIso 𝒜).app X).inv_comp_eq.2
    ((DerivedCategory.quotientCompQhIso 𝒜).hom.naturality h)

/-- On the homotopy class of a morphism of complexes `g`, `Φ` is the sheafification of the
derived class of the transpose of `g`, read through `Θ`. -/
theorem Φ_quot (f : R ⟶ A)
    (g : P ⟶ ((resExt f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :
    Φ P N hP hN f ((Qh R).map g) =
      (Θ f P hP).hom ≫ (tilde.functor A).mapDerivedCategory.map
        (DerivedCategory.Q.map (transposeCx f (Z := (ext f).obj N) g)) ≫
        (Θ f N hN).inv := by
  unfold Φ
  exact congrArg
    (fun z => (Θ f P hP).hom ≫ (tilde.functor A).mapDerivedCategory.map z ≫ (Θ f N hN).inv)
    (quotientCompQhIso_conj (transposeCx f (Z := (ext f).obj N) g))

/-- The diagram chase behind `Φ_comp_tau₀`, with every object and morphism a variable: given
compatible isomorphisms `hP`, `hN` and a naturality square `hnat`, the conjugate of
`F.map (eP.inv ≫ m ≫ eN.hom)` by `a'` and `c'` equals the conjugate of
`L.map (a.hom ≫ b ≫ c.inv)` by `θX` and `θY`. -/
theorem Φ_chase {𝒟₀ 𝒟 𝒞 : Type*} [Category* 𝒟₀] [Category* 𝒟] [Category* 𝒞] (L : 𝒟₀ ⥤ 𝒟)
    (F : 𝒞 ⥤ 𝒟) {X₀ X₁ Y₁ Y₀ : 𝒟₀} {TX TY : 𝒟} {CP CN CP' CN' : 𝒞}
    (a : X₀ ≅ X₁) (b : X₁ ⟶ Y₁) (c : Y₀ ≅ Y₁) (θX : L.obj X₀ ≅ TX) (θY : L.obj Y₀ ≅ TY)
    (a' : TX ≅ F.obj CP') (c' : TY ≅ F.obj CN') (aβ : L.obj X₁ ≅ F.obj CP)
    (cβ : L.obj Y₁ ≅ F.obj CN) (eP : CP ≅ CP') (eN : CN ≅ CN') (m : CP ⟶ CN)
    (hP : θX.hom ≫ a'.hom = L.map a.hom ≫ aβ.hom ≫ F.map eP.hom)
    (hN : θY.hom ≫ c'.hom = L.map c.hom ≫ cβ.hom ≫ F.map eN.hom)
    (hnat : L.map b ≫ cβ.hom = aβ.hom ≫ F.map m) :
    a'.hom ≫ F.map (eP.inv ≫ m ≫ eN.hom) ≫ c'.inv =
      θX.inv ≫ L.map (a.hom ≫ b ≫ c.inv) ≫ θY.hom := by
  rw [← cancel_epi θX.hom, ← cancel_mono c'.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hP, hN]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc,
    Iso.inv_hom_id_map_assoc]
  rw [reassoc_of% hnat]

/-- **The identification `Φ` carries post-composition with the base-change map to the map of
the system of spectra.** -/
theorem Φ_comp_tau₀ (f : R ⟶ A) (β : A ⟶ A')
    (ψ : (Qh R).obj P ⟶ (Qh R).obj (((resExt f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) :
    Φ P N hP hN (f ≫ β) (ψ ≫ (Qh R).map
        ((NatTrans.mapHomologicalComplex (tau₀ f β) (ComplexShape.up ℤ)).app N)) =
      schemeFactorHom (Spec.map β) (Spec.map f) (Spec.map (f ≫ β)) (spec_comp' f β)
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P))
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj N))
        (Φ P N hP hN f ψ) := by
  obtain ⟨g, rfl⟩ := (Qh R).map_surjective ψ
  rw [← Functor.map_comp, Φ_quot, Φ_quot, transposeCx_comp_tau₀]
  exact Φ_chase (pb (Spec.map β)) (DerivedCategory.Q ⋙ (tilde.functor A').mapDerivedCategory)
    (Θ f P hP)
    ((tilde.functor A).mapDerivedCategory.map
      (DerivedCategory.Q.map (transposeCx f (Z := (ext f).obj N) g))) (Θ f N hN)
    ((schemeFactorIso (Spec.map β) (Spec.map f) (Spec.map (f ≫ β)) (spec_comp' f β)).app _)
    ((schemeFactorIso (Spec.map β) (Spec.map f) (Spec.map (f ≫ β)) (spec_comp' f β)).app _)
    (Θ (f ≫ β) P hP) (Θ (f ≫ β) N hN) (Θ β ((ext f).obj P) (kFlat_ext f P hP))
    (Θ β ((ext f).obj N) (kFlat_ext f N hN)) (extComp f β P) (extComp f β N)
    ((ext β).map (transposeCx f (Z := (ext f).obj N) g))
    (Θ_cocycle f β P hP) (Θ_cocycle f β N hN)
    (Θ_naturality β (kFlat_ext f P hP) (kFlat_ext f N hN) (transposeCx f (Z := (ext f).obj N) g))

/-- If `f ≫ β = f'`, then `Spec.map β ≫ Spec.map f = Spec.map f'`. -/
theorem spec_comp (f : R ⟶ A) (f' : R ⟶ A') (β : A ⟶ A') (hβ : f ≫ β = f') :
    Spec.map β ≫ Spec.map f = Spec.map f' := by
  rw [← Spec.map_comp, hβ]

/-- For `f ≫ β = f'`, the identification `Φ` along `f'` carries post-composition with the
base-change map `A ⊗_R N ⟶ A' ⊗_R N` to the map `schemeFactorHom` of the factorization
`Spec.map β ≫ Spec.map f = Spec.map f'`. -/
theorem Φ_comp_tau (f : R ⟶ A) (f' : R ⟶ A') (β : A ⟶ A') (hβ : f ≫ β = f')
    (ψ : (Qh R).obj P ⟶ (Qh R).obj (((resExt f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) :
    Φ P N hP hN f' (ψ ≫ (Qh R).map
        ((NatTrans.mapHomologicalComplex (tau f f' β hβ) (ComplexShape.up ℤ)).app N)) =
      schemeFactorHom (Spec.map β) (Spec.map f) (Spec.map f') (spec_comp f f' β hβ)
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P))
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj N))
        (Φ P N hP hN f ψ) := by
  subst hβ
  exact Φ_comp_tau₀ P N hP hN f β ψ

/-- **`Φ` is bijective** when `A ⊗_R P` is K-projective. -/
theorem Φ_bijective (f : R ⟶ A) [((ext f).obj P).IsKProjective] :
    Function.Bijective (Φ P N hP hN f) := by
  have h1 := ((Adjunction.mapHomotopyCategoryAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom) (ComplexShape.up ℤ)).homEquiv
      ((Qh R).obj P) ((Qh A).obj ((ext f).obj N))).symm.bijective
  have h2 := CochainComplex.IsKProjective.Qh_map_bijective ((ext f).obj P)
    ((Qh A).obj ((ext f).obj N))
  have h3 := (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app
    ((ext f).obj P)) ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app
      ((ext f).obj N))).bijective
  have h4 := (StandardModel.mapDerivedCategoryFullyFaithful A).map_bijective
    (DerivedCategory.Q.obj ((ext f).obj P)) (DerivedCategory.Q.obj ((ext f).obj N))
  have h5 := (Iso.homCongr (Θ f P hP).symm (Θ f N hN).symm).bijective
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

end Phi

namespace RingSystem

variable {R : CommRingCat.{u}} {J : Type v} [Preorder J] (S : RingSystem.{v, u} R J)

/-- **The system of spectra** `Spec A_j` over `Spec R`, with vertex `Spec A`. -/
def toSchemeSystem : SchemeSystem.{v, u} (Spec R) J where
  stage j := Spec (S.A j)
  toBase j := Spec.map (S.φ j)
  transition h := Spec.map (S.β h)
  transition_toBase h := by rw [← Spec.map_comp, S.φ_β]
  transition_comp h h' := by rw [← Spec.map_comp, S.β_β]
  transition_refl i := by rw [S.β_refl, Spec.map_id]
  limit := Spec S.lim
  limitToBase := Spec.map S.φlim
  proj j := Spec.map (S.γ j)
  proj_toBase j := by rw [← Spec.map_comp, S.φ_γ]
  proj_transition h := by rw [← Spec.map_comp, S.β_γ]

/-- The transition map `A_i ⟶ A_j`, as an `R`-linear map. -/
def βl {i j : J} (h : i ≤ j) :
    (ModuleCat.restrictScalars (S.φ i).hom).obj (ModuleCat.of (S.A i) (S.A i)) →ₗ[R]
      (ModuleCat.restrictScalars (S.φ j).hom).obj (ModuleCat.of (S.A j) (S.A j)) where
  toFun := S.β h
  map_add' := map_add _
  map_smul' r x := (map_mul (S.β h).hom ((S.φ i) r) x).trans
    (congrArg (· * (S.β h) x) (congrArg (fun g : R ⟶ S.A j => g r) (S.φ_β h)))

/-- The map `A_j ⟶ A`, as an `R`-linear map. -/
def γl (j : J) :
    (ModuleCat.restrictScalars (S.φ j).hom).obj (ModuleCat.of (S.A j) (S.A j)) →ₗ[R]
      (ModuleCat.restrictScalars S.φlim.hom).obj (ModuleCat.of S.lim S.lim) where
  toFun := S.γ j
  map_add' := map_add _
  map_smul' r x := (map_mul (S.γ j).hom ((S.φ j) r) x).trans
    (congrArg (· * (S.γ j) x) (congrArg (fun g : R ⟶ S.lim => g r) (S.φ_γ j)))

variable (N : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The complex `A_j ⊗_R N` of `R`-modules. -/
abbrev stageCx (j : J) : CochainComplex (ModuleCat.{u} R) ℤ :=
  ((resExt (S.φ j)).mapHomologicalComplex (ComplexShape.up ℤ)).obj N

/-- The complex `A ⊗_R N` of `R`-modules. -/
abbrev limCx (S : RingSystem.{v, u} R J) (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  ((resExt S.φlim).mapHomologicalComplex (ComplexShape.up ℤ)).obj N

/-- The transition maps `A_i ⊗_R N ⟶ A_j ⊗_R N`. -/
def tcx {i j : J} (h : i ≤ j) : S.stageCx N i ⟶ S.stageCx N j :=
  (NatTrans.mapHomologicalComplex (tau (S.φ i) (S.φ j) (S.β h) (S.φ_β h))
    (ComplexShape.up ℤ)).app N

/-- The maps `A_j ⊗_R N ⟶ A ⊗_R N`. -/
def ιcx (j : J) : S.stageCx N j ⟶ S.limCx N :=
  (NatTrans.mapHomologicalComplex (tau (S.φ j) S.φlim (S.γ j) (S.φ_γ j))
    (ComplexShape.up ℤ)).app N

/-- In each degree, the transition map `tcx` is `βl h ⊗ id`. -/
theorem tcx_f_apply {i j : J} (h : i ≤ j) (n : ℤ) (x : (S.stageCx N i).X n) :
    (S.tcx N h).f n x = (S.βl h).rTensor (N.X n) x :=
  tau_app_eq_rTensor _ _ _ _ _ (S.βl h) (fun _ => rfl) x

/-- In each degree, the map `ιcx` is `γl j ⊗ id`. -/
theorem ιcx_f_apply (j : J) (n : ℤ) (x : (S.stageCx N j).X n) :
    (S.ιcx N j).f n x = (S.γl j).rTensor (N.X n) x :=
  tau_app_eq_rTensor _ _ _ _ _ (S.γl j) (fun _ => rfl) x

/-- The transition maps `tcx` compose: `tcx h ≫ tcx h' = tcx (h.trans h')`. -/
theorem tcx_comp {i j k : J} (h : i ≤ j) (h' : j ≤ k) :
    S.tcx N h ≫ S.tcx N h' = S.tcx N (h.trans h') := by
  ext n x
  exact tau_comp_app _ _ _ _ _ _ _ _ _ (S.β_β h h') _ x

/-- The maps `ιcx` are compatible with the transition maps `tcx`. -/
theorem tcx_ιcx {i j : J} (h : i ≤ j) : S.tcx N h ≫ S.ιcx N j = S.ιcx N i := by
  ext n x
  exact tau_comp_app _ _ _ _ _ _ _ _ _ (S.β_γ h) _ x

section Colimit

variable [IsDirected J (· ≤ ·)] [Nonempty J]
  (hcol : Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : S.A i) => S.β h x)
    (fun j (x : S.A j) => S.γ j x))

include hcol in
/-- If `A` is the colimit of the `A_j`, then in each degree `n` the module `(A ⊗_R N)^n` is the
colimit of the `(A_j ⊗_R N)^n` along `tcx` and `ιcx`. -/
theorem isStagesColimit_stageCx (n : ℤ) :
    Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : (S.stageCx N i).X n) => (S.tcx N h).f n x)
      (fun j (x : (S.stageCx N j).X n) => (S.ιcx N j).f n x) := by
  classical
  have key := isStagesColimit_rTensor (fun i j h => S.βl h) (fun j => S.γl j)
    (fun i x => congrArg (fun g : S.A i ⟶ S.A i => g x) (S.β_refl i))
    (fun i j k h h' x => congrArg (fun g : S.A i ⟶ S.A k => g x) (S.β_β h h')) hcol (N.X n)
  refine ⟨fun i j h x => ?_, fun x => ?_, fun i x y hxy => ?_⟩
  · exact ((congrArg ((S.ιcx N j).f n).hom (S.tcx_f_apply N h n x)).trans
      ((S.ιcx_f_apply N j n _).trans ((key.ι_trans i j h x).trans (S.ιcx_f_apply N i n x).symm)))
  · obtain ⟨j, y, hy⟩ := key.exists_stage x
    exact ⟨j, y, (S.ιcx_f_apply N j n y).trans hy⟩
  · obtain ⟨k, h, hk⟩ := key.exists_trans_eq i x y
      (((S.ιcx_f_apply N i n x).symm.trans hxy).trans (S.ιcx_f_apply N i n y))
    exact ⟨k, h, ((S.tcx_f_apply N h n x).trans hk).trans (S.tcx_f_apply N h n y).symm⟩

end Colimit

section Main

variable [IsDirected J (· ≤ ·)] [Nonempty J]
  (hcol : Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : S.A i) => S.β h x)
    (fun j (x : S.A j) => S.γ j x))
  (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (hN : N.KFlat)
  [hKP : ∀ j, ((ext (S.φ j)).obj P).IsKProjective] [hKPlim : ((ext S.φlim).obj P).IsKProjective]
  (W : Finset ℤ)
  (hW : ∀ n : ℤ, n ∉ W → IsZero (P.X n) ∨
    (IsZero ((S.limCx N).X n) ∧ IsZero ((S.limCx N).X (n - 1)) ∧
      ∀ j, IsZero ((S.stageCx N j).X n) ∧ IsZero ((S.stageCx N j).X (n + 1))))
  (hfp : ∀ n : ℤ, Module.FinitePresentation R (P.X n))

include hcol hP hN hW hfp in
/-- **Stacks 09RE over a directed system of spectra**, at the derived sheafifications of `P`
and `N`. -/
theorem isColim_toSchemeSystem :
    S.toSchemeSystem.IsColim ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P))
      ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj N)) := by
  have hst := S.isStagesColimit_stageCx N hcol
  have heart := isStagesColimit_homotopy (E := P) (fun _ _ _ h h' => S.tcx_comp N h h')
    (fun _ _ h => S.tcx_ιcx N h)
    (fun n x => (hst n).exists_stage x)
    (fun n j y hy => by
      obtain ⟨k, h, hk⟩ := (hst n).exists_trans_eq j y 0 (hy.trans (map_zero _).symm)
      exact ⟨k, h, hk.trans (map_zero _)⟩) W hW hfp
  refine Stacks.IsStagesColimit.ofEquiv _ _
    (fun j => (Equiv.ofBijective _ (Φ_bijective P N hP hN (S.φ j))).symm)
    (Equiv.ofBijective _ (Φ_bijective P N hP hN S.φlim)).symm ?_ ?_ heart
  · intro i j h s
    refine (Equiv.symm_apply_eq _).2 ((Φ_comp_tau P N hP hN (S.φ i) (S.φ j) (S.β h)
      (S.φ_β h) _).trans (congrArg _ (Equiv.ofBijective_apply_symm_apply _ _ s))).symm
  · intro i s
    refine (Equiv.symm_apply_eq _).2 ((Φ_comp_tau P N hP hN (S.φ i) S.φlim (S.γ i)
      (S.φ_γ i) _).trans (congrArg _ (Equiv.ofBijective_apply_symm_apply _ _ s))).symm

end Main

end RingSystem

end Stacks.LimitHomDescent.Affine

end
