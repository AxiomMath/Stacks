module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.ConormalSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceTensorPointPaste

/-!
# The conormal source read at scheme points, and its base change

Let `q : ℰ ⟶ ℒ` be an invertible quotient of a quasi-coherent module on an algebraic space `X`
and `x : T ⟶ X` a scheme point.  The source `Ker(q) ⊗ ℒ^{⊗ -1}` of the conormal isomorphism of
Stacks 0B4I is read at `x` as the source `Ker(q_x) ⊗ ℒ_x^{⊗ -1}` of Stacks 0B3V on `T`: Stacks
03EL for `x`, the Zariski reading tensor isomorphism, and the tensor product of the kernel factor
with the inverse-line factor.  Along `h : T' ⟶ T` this reading is carried to the reading at
`x ∘ h` by the base-change comparison of Stacks 0B3V.

## Main definitions

* `CategoryTheory.Functor.compBifunctorMap`: a morphism into `G(A₁, A₂)` followed by
  `G(k, i)`.

## Main results

* `CategoryTheory.Functor.compBifunctorMap_baseChange_of_squares`: the paste giving the base
  change of such a composite.
* `AlgebraicGeometry.Space.zariskiReadingTensorComparison_comp_eq`: Stacks 03EL for `x ∘ h`
  read on `T'`, with `x ∘ h` written as a composite or as a point.
* `AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso_hom_comp_inv` and
  `AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso_inv_comp_hom`: the identification of
  the readings at `x ∘ h` and `x` against its inverse.
* `AlgebraicGeometry.Space.conormalSourcePointReading_baseChange_of`: the base change of the
  conormal source read at scheme points, given the monoidality of the base change of the Zariski
  reading and the base change of the inverse-line factor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

namespace CategoryTheory.Functor

/-- A morphism `μ : S ⟶ G(A₁, A₂)` followed by `G(k, i) : G(A₁, A₂) ⟶ G(K, Λ)`. -/
abbrev compBifunctorMap {𝒞 : Type*} [iC : Category 𝒞] (G : 𝒞 ⥤ 𝒞 ⥤ 𝒞) {S A₁ A₂ K Λ : 𝒞}
    (μ : S ⟶ (G.obj A₁).obj A₂) (k : A₁ ⟶ K) (i : A₂ ⟶ Λ) : S ⟶ (G.obj K).obj Λ :=
  μ ≫ ((G.map k).app A₂ ≫ (G.obj K).map i)

/-- **The base change of `μ ≫ G(k, i)`**: if `μ` is monoidal along `P` up to the identifications
`a ≫ a'`, `b ≫ b'` (`CategoryTheory.Functor.TensorPasteConclusion`), the comparison `κ` of `P`
with the two bifunctors is natural, `cs` is `κ` followed by `F(kb, ib)`, and `k`, `i` are carried
to `k'`, `i'` through the inverses `u₁`, `u₂` of the identifications, then
`u ≫ P(μ ≫ G(k, i)) ≫ cs = μ' ≫ F(k', i')` for `u` inverse to `θ ≫ R'(c)` and `μ'` equal to
`R'(m') ≫ Z''`. -/
theorem compBifunctorMap_baseChange_of_squares {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [iℬ : Category ℬ] [i𝒞 : Category 𝒞] [Category 𝒟] {P : 𝒞 ⥤ ℬ} {R : 𝒟 ⥤ 𝒞} {R' : 𝒜 ⥤ ℬ}
    {G : 𝒞 ⥤ 𝒞 ⥤ 𝒞} {F : ℬ ⥤ ℬ ⥤ ℬ} {D D' : 𝒟} {A₁ A₂ K₀ Λ₀ : 𝒞} {W₁ W₂ V₁ V₂ K' Λ' : ℬ}
    {GD E'' Ex : 𝒜} {m : D ⟶ D'} {Z : R.obj D' ⟶ (G.obj A₁).obj A₂}
    {κA : P.obj ((G.obj A₁).obj A₂) ⟶ (F.obj (P.obj A₁)).obj (P.obj A₂)}
    {a : P.obj A₁ ⟶ W₁} {a' : W₁ ⟶ V₁} {b : P.obj A₂ ⟶ W₂} {b' : W₂ ⟶ V₂}
    {θ : P.obj (R.obj D) ⟶ R'.obj GD} {c : GD ⟶ Ex} {m' : Ex ⟶ E''}
    {Z'' : R'.obj E'' ⟶ (F.obj V₁).obj V₂} {u : R'.obj Ex ⟶ P.obj (R.obj D)}
    {k : A₁ ⟶ K₀} {i : A₂ ⟶ Λ₀}
    {κK : P.obj ((G.obj K₀).obj Λ₀) ⟶ (F.obj (P.obj K₀)).obj (P.obj Λ₀)}
    {kb : P.obj K₀ ⟶ K'} {ib : P.obj Λ₀ ⟶ Λ'} {cs : P.obj ((G.obj K₀).obj Λ₀) ⟶ (F.obj K').obj Λ'}
    {u₁ : V₁ ⟶ P.obj A₁} {u₂ : V₂ ⟶ P.obj A₂} {k' : V₁ ⟶ K'} {i' : V₂ ⟶ Λ'}
    {μ'' : R'.obj Ex ⟶ (F.obj V₁).obj V₂}
    (t : TensorPasteConclusion P R R' F m Z κA a a' b b' θ c m' Z'')
    (huv : u ≫ θ ≫ R'.map c = 𝟙 _) (hv₁ : (a ≫ a') ≫ u₁ = 𝟙 _) (hv₂ : (b ≫ b') ≫ u₂ = 𝟙 _)
    (hκ : P.map ((G.map k).app A₂ ≫ (G.obj K₀).map i) ≫ κK =
      κA ≫ ((F.map (P.map k)).app (P.obj A₂) ≫ (F.obj (P.obj K₀)).map (P.map i)))
    (hcs : cs = κK ≫ ((F.map kb).app (P.obj Λ₀) ≫ (F.obj K').map ib))
    (hk : u₁ ≫ P.map k ≫ kb = k') (hi : u₂ ≫ P.map i ≫ ib = i')
    (hμ : R'.map m' ≫ Z'' = μ'') :
    u ≫ P.map (compBifunctorMap G (R.map m ≫ Z) k i) ≫ cs = compBifunctorMap F μ'' k' i' := by
  subst hμ
  have hk' : P.map k ≫ kb = (a ≫ a') ≫ k' := by
    rw [← hk, ← Category.assoc, hv₁, Category.id_comp]
  have hi' : P.map i ≫ ib = (b ≫ b') ≫ i' := by
    rw [← hi, ← Category.assoc, hv₂, Category.id_comp]
  have t' : P.map (R.map m ≫ Z) ≫ κA ≫ ((F.map (a ≫ a')).app (P.obj A₂) ≫
      (F.obj V₁).map (b ≫ b')) = θ ≫ R'.map c ≫ R'.map m' ≫ Z'' := t
  calc u ≫ P.map (compBifunctorMap G (R.map m ≫ Z) k i) ≫ cs
      = u ≫ P.map (R.map m ≫ Z) ≫ (P.map ((G.map k).app A₂ ≫ (G.obj K₀).map i) ≫ κK) ≫
          ((F.map kb).app (P.obj Λ₀) ≫ (F.obj K').map ib) := by
        rw [hcs, compBifunctorMap, P.map_comp]
        simp only [Category.assoc]
    _ = u ≫ P.map (R.map m ≫ Z) ≫ κA ≫ ((F.map (P.map k ≫ kb)).app (P.obj A₂) ≫
          (F.obj K').map (P.map i ≫ ib)) := by
        rw [hκ, Category.assoc, bifunctor_map_app_comp_obj_map]
    _ = u ≫ (P.map (R.map m ≫ Z) ≫ κA ≫ ((F.map (a ≫ a')).app (P.obj A₂) ≫
          (F.obj V₁).map (b ≫ b'))) ≫ ((F.map k').app V₂ ≫ (F.obj K').map i') := by
        rw [hk', hi', ← bifunctor_map_app_comp_obj_map]
        simp only [Category.assoc]
    _ = compBifunctorMap F (R'.map m' ≫ Z'') k' i' := by
        rw [t']
        simp only [compBifunctorMap, Category.assoc, reassoc_of% huv]

/-- The inverse of an identification `R'(e) ≫ z⁻¹` composed with `z ≫ R'(e)`. -/
theorem mapIso_symm_trans_symm_hom_comp {𝒜 ℬ : Type*} [Category 𝒜] [iℬ : Category ℬ]
    (R' : 𝒜 ⥤ ℬ) {A B : 𝒜} {Y : ℬ} (e : B ≅ A) (z : Y ≅ R'.obj B) :
    (R'.mapIso e.symm ≪≫ z.symm).hom ≫ z.hom ≫ R'.map e.hom = 𝟙 _ := by
  simp

/-- `z ≫ R'(e)` composed with its inverse `R'(e⁻¹) ≫ z⁻¹`. -/
theorem comp_mapIso_symm_trans_symm_hom {𝒜 ℬ : Type*} [Category 𝒜] [iℬ : Category ℬ]
    (R' : 𝒜 ⥤ ℬ) {A B : 𝒜} {Y : ℬ} (e : B ≅ A) (z : Y ≅ R'.obj B) :
    (z.hom ≫ R'.map e.hom) ≫ (R'.mapIso e.symm ≪≫ z.symm).hom = 𝟙 _ := by
  simp

/-- `θ ≫ R'(e)` composed with its inverse `R'(e⁻¹) ≫ θ⁻¹`. -/
theorem comp_map_inv_comp_inv {𝒜 ℬ : Type*} [Category 𝒜] [iℬ : Category ℬ]
    (R' : 𝒜 ⥤ ℬ) {A B : 𝒜} {Y : ℬ} (e : B ≅ A) (θ : Y ⟶ R'.obj B) [IsIso θ] :
    (θ ≫ R'.map e.hom) ≫ (R'.map e.inv ≫ CategoryTheory.inv θ) = 𝟙 _ := by
  simp [← R'.map_comp_assoc]

/-- Images of heterogeneously equal morphisms between equal objects are heterogeneously equal. -/
theorem heq_map_of_heq {𝒜 ℬ : Type*} [Category 𝒜] [iℬ : Category ℬ] (F : 𝒜 ⥤ ℬ)
    {X Y X' Y' : 𝒜} (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'} (hf : HEq f f') :
    HEq (F.map f) (F.map f') := by
  subst hX hY
  obtain rfl := eq_of_heq hf
  rfl

end CategoryTheory.Functor

/-- Composites of heterogeneously equal morphisms between equal objects are heterogeneously
equal. -/
theorem CategoryTheory.heq_comp_of_heq {𝒞 : Type*} [i𝒞 : Category 𝒞] {X Y Z X' Y' Z' : 𝒞}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'}
    {g' : Y' ⟶ Z'} (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst hX hY hZ
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  rfl


namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (Q : InvertibleQuotient X E)

/-- Stacks 03EL for `x ∘ h` followed by the Zariski reading tensor isomorphism, with the point
`x ∘ h` written as a composite or as a point. -/
theorem zariskiReadingTensorComparison_comp_eq {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T) (A₁ A₂ : Modules.{u, u} B S hS X.1 X.2) (hA₁ : A₁.IsQuasicoherentOnSite)
    (hA₂ : A₂.IsQuasicoherentOnSite) :
    (@CategoryTheory.CategoryStruct.comp _ (@CategoryTheory.Category.toCategoryStruct _
        Scheme.Modules.instCategory) _ _ _
        (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
            Scheme.Modules.instCategory (zariskiReadingFunctor T')
          ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj ((A₁ ⊗ A₂)))
              ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T')
              (isAlgebraicSpace_yoneda B S hS T')) ((modulePullback B S hS ((representedSpaceMap B S
              hS h) ≫ pointHom x)).obj (A₁)) ((modulePullback B S hS ((representedSpaceMap B S hS h)
              ≫ pointHom x)).obj (A₂))))
          (modulePullbackTensorIso B S hS ((representedSpaceMap B S hS h) ≫ pointHom x) (A₁)
              (A₂)).hom)
        ((zariskiReadingTensorObjIso T' ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫
            pointHom x)).obj (A₁)) ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫
            pointHom x)).obj (A₂)) (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B
            S hS ((representedSpaceMap B S hS h) ≫ pointHom x) (A₁) hA₁)
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
            ((representedSpaceMap B S hS h) ≫ pointHom x) (A₂) hA₂)).hom ≫
            (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
            ((zariskiReadingFunctor T').obj ((modulePullback B S hS ((representedSpaceMap B S hS h)
            ≫ pointHom x)).obj (A₁))) ((zariskiReadingFunctor T').obj ((modulePullback B S hS
            ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₂)))).hom)) =
      (@CategoryTheory.CategoryStruct.comp _ (@CategoryTheory.Category.toCategoryStruct _
          Scheme.Modules.instCategory) _ _ _
        (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
            Scheme.Modules.instCategory (zariskiReadingFunctor T')
          ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj ((A₁ ⊗ A₂)))
              ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T')
              (isAlgebraicSpace_yoneda B S hS T')) ((modulePullback B S hS (pointHom (yoneda.map h ≫
              x))).obj (A₁)) ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj (A₂))))
          (modulePullbackTensorIso B S hS (pointHom (yoneda.map h ≫ x)) (A₁) (A₂)).hom)
        ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj
            (A₁)) ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj (A₂))
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
            (pointHom (yoneda.map h ≫ x)) (A₁) hA₁)
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
            (pointHom (yoneda.map h ≫ x)) (A₂) hA₂)).hom ≫ (monoidalTensorSheafTensorIso
            ((BigFppfOver.toScheme B S hS).obj T') ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj (A₁)))
            ((zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom (yoneda.map h ≫
            x))).obj (A₂)))).hom)) :=
  eq_of_heq (CategoryTheory.heq_comp_of_heq rfl rfl rfl
    (CategoryTheory.Functor.heq_map_of_heq (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory) _ rfl rfl HEq.rfl)
    (CategoryTheory.heq_comp_of_heq rfl rfl rfl HEq.rfl HEq.rfl))

/-- The identification `R'((x ∘ h)^*A) ≅ τ^*R(x^*A)` followed by its inverse, the base change of
the Zariski reading and Stacks 03LU. -/
theorem pointZariskiModuleBaseChangeIso_hom_comp_inv {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶
    X.1) (h : T' ⟶ T)
    (A : Modules.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherentOnSite) :
    (@CategoryTheory.CategoryStruct.comp _ (@CategoryTheory.Category.toCategoryStruct _
        Scheme.Modules.instCategory) _ _ _ (pointZariskiModuleBaseChangeIso X (A) hA x h).hom
        (@CategoryTheory.CategoryStruct.comp _ (@CategoryTheory.Category.toCategoryStruct _
        Scheme.Modules.instCategory) _ _ _ ((zariskiReadingPullbackHom h).app
        ((modulePullback B S hS (pointHom x)).obj (A))) (@CategoryTheory.Functor.map _ _
        ((BigFppfOver.toScheme B S hS).obj T').Modules Scheme.Modules.instCategory
        (zariskiReadingFunctor T')
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj ((modulePullback B S hS
            (pointHom x)).obj (A)))
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A))
            ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app
            (A))))) = 𝟙 _ :=
  CategoryTheory.Functor.mapIso_symm_trans_symm_hom_comp
    (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules) (iℬ := Scheme.Modules.instCategory)
    (zariskiReadingFunctor T') ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
        (pointHom x)).app A) (zariskiReadingPullbackIso h _ (isQuasicoherentOnSite_pointPullback X A
        hA T x))

/-- The base change of the Zariski reading and Stacks 03LU followed by their inverse
`τ^*R(x^*A) ≅ R'((x ∘ h)^*A)`. -/
theorem pointZariskiModuleBaseChangeIso_inv_comp_hom {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶
    X.1) (h : T' ⟶ T)
    (A : Modules.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherentOnSite) :
    (@CategoryTheory.CategoryStruct.comp _ (@CategoryTheory.Category.toCategoryStruct _
        Scheme.Modules.instCategory) _ _ _ (@CategoryTheory.CategoryStruct.comp _
        (@CategoryTheory.Category.toCategoryStruct _ Scheme.Modules.instCategory) _ _ _
        ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj (A)))
        (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T')
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj ((modulePullback B S hS
            (pointHom x)).obj (A)))
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A))
            ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app
            (A)))) (pointZariskiModuleBaseChangeIso X (A) hA x h).hom) = 𝟙 _ :=
  CategoryTheory.Functor.comp_mapIso_symm_trans_symm_hom
    (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules) (iℬ := Scheme.Modules.instCategory)
    (zariskiReadingFunctor T') ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
        (pointHom x)).app A) (zariskiReadingPullbackIso h _ (isQuasicoherentOnSite_pointPullback X A
        hA T x))

/-- **The source of the conormal isomorphism of Stacks 0B4I read at scheme points is compatible
with base change**, given the monoidality of the base change of the Zariski reading and the base
change of the inverse-line factor: for `x : T ⟶ X` and `h : T' ⟶ T`, the identification of the
readings at `x ∘ h` and `x`, the inverse image along `h` of the reading at `x`, and the
base-change comparison of Stacks 0B3V give the reading at `x ∘ h`. -/
theorem conormalSourcePointReading_baseChange_of [hQ : IsInvertible (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property Q.L]
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T)
    (hc : ∀ (N M : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2)
      (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite),
      CategoryTheory.Functor.TensorPasteUpper
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N) (M)))
      (C' := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj
          T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)).obj
              ((zariskiReadingFunctor T).obj (N))).obj ((zariskiReadingFunctor T).obj (M)))
      (Y₁ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (N)))
      (Y₂ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (M)))
      (W₁ := (zariskiReadingFunctor T').obj ((modulePullback B S hS (representedSpaceMap B S hS
          h)).obj (N)))
      (W₂ := (zariskiReadingFunctor T').obj ((modulePullback B S hS (representedSpaceMap B S hS
          h)).obj (M)))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (E' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T')
          (isAlgebraicSpace_yoneda B S hS T')) ((modulePullback B S hS (representedSpaceMap B S hS
          h)).obj (N)) ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
          (zariskiReadingFunctor T') (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingTensorObjIso T (N) (M) hN hM).hom ≫ (monoidalTensorSheafTensorIso
          ((BigFppfOver.toScheme B S hS).obj T) ((zariskiReadingFunctor T).obj (N))
          ((zariskiReadingFunctor T).obj (M))).hom) ((Stacks.RingedSpace.comparisonBifunctorIso
          ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app ((zariskiReadingFunctor
          T).obj (N), (zariskiReadingFunctor T).obj (M))) ((zariskiReadingPullbackHom h).app (N))
          ((zariskiReadingPullbackHom h).app (M)) ((zariskiReadingPullbackHom h).app
          ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h) N M).hom
      ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          (N)) ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (representedSpaceMap
          B S hS h) (N) hN) (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (M) hM)).hom ≫ (monoidalTensorSheafTensorIso
          ((BigFppfOver.toScheme B S hS).obj T') ((zariskiReadingFunctor T').obj
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N))) ((zariskiReadingFunctor
          T').obj ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M)))).hom))
    (hi : (pointZariskiModuleBaseChangeIso X (Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)) x h).hom ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
        (inversePointReadingIso X T x Q.L).hom ≫
      (Stacks.Divisors.inverseQuotientBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (sectionPointQuotient X E hE Q T x) (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h)).hom =
      (inversePointReadingIso X T' (yoneda.map h ≫ x) Q.L).hom) :
    (pointZariskiModuleBaseChangeIso X (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X.1
        X.2) (kernel Q.q) (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS
        X) (structureRingSheaf B S hS X).property Q.L (-1)))
        (isQuasicoherentOnSite_sectionConormalSource X E hE Q) x h).hom ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
        (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj
            T).Modules) (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫ ((zariskiReadingTensorObjIso T
          ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)) ((modulePullback B S hS
          (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS
          X) (structureRingSheaf B S hS X).property Q.L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)))
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))))).hom))
      (kernelPointReadingHom X E hE Q T x) (inversePointReadingIso X T x Q.L).hom) ≫
      (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (pointZariskiModuleBaseChangeIso X E hE x h) (sectionPointQuotient X E hE Q T x)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h)
        (sectionPointQuotient_baseChange_q X E hE Q x h)).hom =
    (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T').Modules)
        (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      (@CategoryTheory.CategoryStruct.comp _ (@CategoryTheory.Category.toCategoryStruct _
          Scheme.Modules.instCategory) _ _ _
        (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
            Scheme.Modules.instCategory (zariskiReadingFunctor T')
          ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj
              ((kernel Q.q ⊗ Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS
              X) (structureRingSheaf B S hS X).property Q.L (-1)))) ((MonoidalCategory.tensorObj
              (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
              ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj (kernel Q.q))
              ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1)))))
          (modulePullbackTensorIso B S hS (pointHom (yoneda.map h ≫ x)) (kernel Q.q)
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1))).hom)
        ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj
            (kernel Q.q)) ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)))
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
            (pointHom (yoneda.map h ≫ x)) (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q))
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
            (pointHom (yoneda.map h ≫ x)) (Stacks.SheafOfModules.Invertible.tensorPower
            (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))
            (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))).hom ≫
            (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
            ((zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom (yoneda.map h ≫
            x))).obj (kernel Q.q))) ((zariskiReadingFunctor T').obj ((modulePullback B S hS
            (pointHom (yoneda.map h ≫ x))).obj (Stacks.SheafOfModules.Invertible.tensorPower
            (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))))).hom))
      (kernelPointReadingHom X E hE Q T' (yoneda.map h ≫ x)) (inversePointReadingIso X T'
          (yoneda.map h ≫ x) Q.L).hom) :=
  CategoryTheory.Functor.compBifunctorMap_baseChange_of_squares
    (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules) (iℬ := Scheme.Modules.instCategory)
    (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules) (i𝒞 := Scheme.Modules.instCategory)
    (κK := (Stacks.RingedSpace.comparisonBifunctorIso
      ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app (_, _))
    (pointReadingBaseChange_tensor_of X x h hc (kernel Q.q)
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))
      (isQuasicoherentOnSite_kernel_q X E hE Q)
      (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))
    (pointZariskiModuleBaseChangeIso_hom_comp_inv X x h
      (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1)))
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q))
    ((@CategoryTheory.Functor.comp_map_inv_comp_inv _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        _ Scheme.Modules.instCategory
        (zariskiReadingFunctor T') _ _ _
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).app
          (kernel Q.q)) ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj
              (kernel Q.q))) (isIso_zariskiReadingPullbackHom_app h _
              (isQuasicoherentOnSite_pointPullback X
        (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q) T x))))
    (pointZariskiModuleBaseChangeIso_inv_comp_hom X x h
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))
      (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))
    (((Stacks.RingedSpace.comparisonBifunctorIso
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.naturality
        (X := ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
            (kernel Q.q)), (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)))))
        (Y := (kernel (sectionPointQuotient X E hE Q T x).q, _))
        (kernelPointReadingHom X E hE Q T x, (inversePointReadingIso X T x Q.L).hom)))
    (by
      exact (Stacks.Divisors.conormalSourceBaseChange_hom _ _ _ _ _ _ _ _).trans
        (congrArg (_ ≫ ·) (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ _ _).symm))
    (kernelPointReadingHom_baseChange X E hE Q x h) hi
    (zariskiReadingTensorComparison_comp_eq X x h (kernel Q.q)
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))
      (isQuasicoherentOnSite_kernel_q X E hE Q)
      (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))

end AlgebraicGeometry.Space

end
