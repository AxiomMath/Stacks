module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleTensorBifunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceReading

/-!
# Naturality of the Zariski reading tensor isomorphism, and the monoidality of mates

Let `T` be an object of the big fppf site over `S`, with scheme `T₀`, and let `R_T` be the
Zariski reading of `𝒪`-modules on the small étale site of the represented algebraic space `T`
(`AlgebraicGeometry.Space.zariskiReadingFunctor`).  On quasi-coherent modules `R_T` carries
tensor products to tensor products, `R_T(𝓟 ⊗ 𝓠) ≅ R_T 𝓟 ⊗ R_T 𝓠`
(`AlgebraicGeometry.Space.zariskiReadingTensorObjIso`).  This file proves that this
identification is natural in `𝓟` and `𝓠`, factor by factor: the comparison of Stacks 03EL at
`ε : (T₀)_étale ⟶ (T₀)_Zar`, the comparison of Stacks 04M0, and the monoidality of the Zariski
restriction of Descent, Proposition 03DX (2) on quasi-coherent modules, all of which are
components of natural constructions.

It also records the categorical half of the monoidality of the base change
`τ^*(R_T M) ⟶ R_{T'}(φ^* M)` of the Zariski reading
(`AlgebraicGeometry.Space.zariskiReadingPullbackHom`): for adjunctions `a ⊣ Z`, `a' ⊣ Z'`,
`φ^* ⊣ φ_*`, `τ^* ⊣ τ_*`, a transformation `σ : φ_* ⋙ Z ⟶ Z' ⋙ τ_*` and comparisons of the left
adjoints with tensor bifunctors, the transposed comparison `θ` is monoidal for the lax
comparisons `μ = η ≫ Z(c_a ≫ (ε ⊗ ε))` of the right adjoints as soon as the conjugate
`τ^* ⋙ a' ⟶ a ⋙ φ^*` of `σ` is monoidal; and the lax comparison of a composite right adjoint
is the composite of the lax comparisons.

## Main results

* `AlgebraicGeometry.Space.zariskiReadingTensorObjIso_hom_naturality`: **naturality of the
  Zariski reading tensor isomorphism** for morphisms of quasi-coherent modules, at the monoidal
  tensor products of both sides; `..._naturality'` is the same at the tensor product sheaf
  bifunctor of the scheme.
* `AlgebraicGeometry.Space.zariskiReadingTensorObjIso_hom_eq` and
  `AlgebraicGeometry.Space.zariskiReadingTensorIso_hom_eq`: the tensor isomorphism with its
  identity-chart detour cancelled.
* `AlgebraicGeometry.SmallEtale.associatedModuleTensorIso_hom_naturality`,
  `AlgebraicGeometry.SmallEtale.restrictModuleTensorIso_hom_naturality`,
  `AlgebraicGeometry.Space.representedSmallEtaleModuleTensorIso_hom_naturality`,
  `AlgebraicGeometry.Space.representedSmallEtaleModuleInverseTensorIso_hom_naturality`,
  `AlgebraicGeometry.Space.modulesTensorObjIso_hom_naturality_tensorHom` and
  `AlgebraicGeometry.Space.selfOpensPushforwardIso_hom_naturality`: naturality of the factors.
* `AlgebraicGeometry.SmallEtale.restrictModuleTensorIso_inv_eq_unit_comp_lax` and
  `AlgebraicGeometry.Space.representedSmallEtaleModuleInverseTensorIso_inv_eq`: the inverses of
  the two monoidality isomorphisms of right adjoints are the lax comparisons.
* `CategoryTheory.Adjunction.transposeComparison_tensor`: monoidality of a transposed
  comparison, given that of the conjugate of `σ`.
* `CategoryTheory.Adjunction.inv_eq_comp_lax`: the lax comparison of a composite right adjoint.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w

/-! ### Categorical lemmas -/

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- A family of isomorphisms which are the components of an isomorphism of bifunctors is
natural, in the curried form. -/
theorem NatIso.app_hom_naturality_curried (SC : C ⥤ C ⥤ C) (SD : D ⥤ D ⥤ D) (L : C ⥤ D)
    (θ : Functor.uncurry.obj SC ⋙ L ≅ L.prod L ⋙ Functor.uncurry.obj SD)
    (k : ∀ M N, L.obj ((SC.obj M).obj N) ≅ (SD.obj (L.obj M)).obj (L.obj N))
    (hk : ∀ M N, θ.app (M, N) = k M N) {M M' N N' : C} (a : M ⟶ M') (b : N ⟶ N') :
    L.map ((SC.map a).app N ≫ (SC.obj M').map b) ≫ (k M' N').hom =
      (k M N).hom ≫ ((SD.map (L.map a)).app (L.obj N) ≫ (SD.obj (L.obj M')).map (L.map b)) := by
  rw [← hk, ← hk]
  exact θ.hom.naturality (X := (M, N)) (Y := (M', N')) (a, b)

/-- Composition in a curried bifunctor, both variables at once. -/
@[reassoc]
theorem Functor.map_app_comp_obj_map_comp {E : Type*} [Category E] (F : C ⥤ D ⥤ E)
    {A A' A'' : C} {X Y Z : D} (f : A ⟶ A') (f' : A' ⟶ A'') (g : X ⟶ Y) (g' : Y ⟶ Z) :
    ((F.map f).app X ≫ (F.obj A').map g) ≫ ((F.map f').app Y ≫ (F.obj A'').map g') =
      (F.map (f ≫ f')).app X ≫ (F.obj A'').map (g ≫ g') := by
  simp only [Category.assoc, Functor.map_comp, NatTrans.comp_app, NatTrans.naturality_assoc]

/-- The lax comparison of a right adjoint, built from a comparison of the left adjoint by the
unit and the counit, is natural. -/
theorem Adjunction.unit_comp_map_comp_counit_naturality {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (SC : C ⥤ C ⥤ C) (SD : D ⥤ D ⥤ D)
    (c : ∀ A B : C, L.obj ((SC.obj A).obj B) ⟶ (SD.obj (L.obj A)).obj (L.obj B))
    (hc : ∀ {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B'),
      L.map ((SC.map f).app B ≫ (SC.obj A').map g) ≫ c A' B' =
        c A B ≫ ((SD.map (L.map f)).app (L.obj B) ≫ (SD.obj (L.obj A')).map (L.map g)))
    {M M' N N' : D} (a : M ⟶ M') (b : N ⟶ N') :
    ((SC.map (R.map a)).app (R.obj N) ≫ (SC.obj (R.obj M')).map (R.map b)) ≫
        adj.unit.app ((SC.obj (R.obj M')).obj (R.obj N')) ≫
          R.map (c (R.obj M') (R.obj N') ≫
            ((SD.map (adj.counit.app M')).app (L.obj (R.obj N')) ≫
              (SD.obj M').map (adj.counit.app N'))) =
      (adj.unit.app ((SC.obj (R.obj M)).obj (R.obj N)) ≫
          R.map (c (R.obj M) (R.obj N) ≫
            ((SD.map (adj.counit.app M)).app (L.obj (R.obj N)) ≫
              (SD.obj M).map (adj.counit.app N)))) ≫
        R.map ((SD.map a).app N ≫ (SD.obj M').map b) := by
  have h1 : ((SC.map (R.map a)).app (R.obj N) ≫ (SC.obj (R.obj M')).map (R.map b)) ≫
      adj.unit.app ((SC.obj (R.obj M')).obj (R.obj N')) =
      adj.unit.app ((SC.obj (R.obj M)).obj (R.obj N)) ≫ R.map (L.map
        ((SC.map (R.map a)).app (R.obj N) ≫ (SC.obj (R.obj M')).map (R.map b))) :=
    adj.unit.naturality _
  have ea := adj.counit.naturality a
  have eb := adj.counit.naturality b
  simp only [Functor.comp_map, Functor.id_map] at ea eb
  have h3 : ((SD.map (L.map (R.map a))).app (L.obj (R.obj N)) ≫
        (SD.obj (L.obj (R.obj M'))).map (L.map (R.map b))) ≫
      ((SD.map (adj.counit.app M')).app (L.obj (R.obj N')) ≫
        (SD.obj M').map (adj.counit.app N')) =
      ((SD.map (adj.counit.app M)).app (L.obj (R.obj N)) ≫
          (SD.obj M).map (adj.counit.app N)) ≫
        ((SD.map a).app N ≫ (SD.obj M').map b) :=
    (Functor.map_app_comp_obj_map_comp SD _ _ _ _).trans
      ((congrArg₂ (fun x y => (SD.map x).app _ ≫ (SD.obj M').map y) ea eb).trans
        (Functor.map_app_comp_obj_map_comp SD _ _ _ _).symm)
  have hc' := hc (R.map a) (R.map b)
  simp only [Category.assoc] at h1 h3 hc' ⊢
  rw [reassoc_of% h1, ← R.map_comp, reassoc_of% hc', h3]
  simp only [Functor.map_comp, Category.assoc]

/-- Naturality of the forward maps of a family of isomorphisms follows from that of the
inverses. -/
theorem Iso.hom_comp_eq_of_inv_comp {X X' Y Y' : C} (e : X ≅ Y) (e' : X' ≅ Y') (f : X ⟶ X')
    (g : Y ⟶ Y') (h : g ≫ e'.inv = e.inv ≫ f) : f ≫ e'.hom = e.hom ≫ g := by
  rw [← cancel_epi e.inv, Iso.inv_hom_id_assoc, ← reassoc_of% h, Iso.inv_hom_id,
    Category.comp_id]

/-- A composite of isomorphisms in which two pairs cancel, read on forward maps. This is the
shape of the Zariski reading tensor isomorphism once its factors are named. -/
theorem Iso.hom_eq_of_eq_cancel {𝒵 : Type*} [Category 𝒵] (T : 𝒵 ⥤ 𝒵 ⥤ 𝒵)
    {Zt Zs Rt Mt Mt' RP MP ZP RQ MQ ZQ : 𝒵}
    (μ : Zt ≅ Zs) (r₀ : Rt ≅ Mt) (s₀ : Mt ≅ Zt) (V : Mt ≅ Mt') (W : Mt' ≅ (T.obj MP).obj MQ)
    (rP : RP ≅ MP) (sP : MP ≅ ZP) (rQ : RQ ≅ MQ) (sQ : MQ ≅ ZQ) (I : Zt ≅ (T.obj ZP).obj ZQ)
    (hI : I = μ ≪≫ μ.symm ≪≫ (r₀ ≪≫ s₀).symm ≪≫
      (r₀ ≪≫ V ≪≫ W ≪≫ (Functor.uncurry.obj T).mapIso (Iso.prod rP.symm rQ.symm)) ≪≫
        ((T.mapIso (rP ≪≫ sP)).app RQ ≪≫ (T.obj ZP).mapIso (rQ ≪≫ sQ))) :
    I.hom = s₀.inv ≫ V.hom ≫ W.hom ≫ ((T.map sP.hom).app MQ ≫ (T.obj ZP).map sQ.hom) := by
  subst hI
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Iso.app_hom,
    Iso.prod_hom, Functor.uncurry_obj_map, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, Functor.map_comp, NatTrans.comp_app]
  congr 3
  simp only [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp]
  simp only [Category.assoc, NatTrans.naturality_assoc]
  simp

/-- Two commutative squares give one in the curried bifunctor. -/
theorem Functor.map_app_comp_obj_map_square {E : Type*} [Category E] (F : C ⥤ D ⥤ E)
    {A A' B B' : C} {X X' Y Y' : D} {f : A ⟶ A'} {p : A' ⟶ B'} {p' : A ⟶ B} {f' : B ⟶ B'}
    {g : X ⟶ X'} {q : X' ⟶ Y'} {q' : X ⟶ Y} {g' : Y ⟶ Y'}
    (hf : f ≫ p = p' ≫ f') (hg : g ≫ q = q' ≫ g') :
    ((F.map f).app X ≫ (F.obj A').map g) ≫ ((F.map p).app X' ≫ (F.obj B').map q) =
      ((F.map p').app X ≫ (F.obj B).map q') ≫ ((F.map f').app Y ≫ (F.obj B').map g') := by
  rw [Functor.map_app_comp_obj_map_comp, Functor.map_app_comp_obj_map_comp, hf, hg]

/-- Two commutative squares, one under a functor `G`, paste under a further functor `F`. -/
theorem Functor.map_map_comp_mapIso_trans_hom {E : Type*} [Category E] (F : D ⥤ E) (G : C ⥤ D)
    {X X' Y Y' : C} {W W' : D} {f : X ⟶ X'} {g : Y ⟶ Y'} {k : W ⟶ W'}
    {m : X ≅ Y} {m' : X' ≅ Y'} {t : G.obj Y ≅ W} {t' : G.obj Y' ≅ W'}
    (hm : f ≫ m'.hom = m.hom ≫ g) (ht : G.map g ≫ t'.hom = t.hom ≫ k) :
    F.map (G.map f) ≫ (F.mapIso (G.mapIso m' ≪≫ t')).hom =
      (F.mapIso (G.mapIso m ≪≫ t)).hom ≫ F.map k := by
  simp only [Functor.mapIso_hom, Iso.trans_hom, ← Functor.map_comp, ← Category.assoc, hm]
  simp only [Functor.map_comp, Category.assoc, ht]

/-- Moving the image of an isomorphism across an equation. -/
theorem Functor.eq_map_inv_comp_of_eq_map_hom_comp (F : C ⥤ D) {X Y : C} {W : D} (e : X ≅ Y)
    (k : F.obj Y ⟶ W) (j : F.obj X ⟶ W) (h : j = F.map e.hom ≫ k) : k = F.map e.inv ≫ j := by
  rw [h, ← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp]

/-- An isomorphism followed by its inverse, under two functors. -/
theorem Functor.map_map_inv_comp_mapIso_trans_hom {E : Type*} [Category E] (F : D ⥤ E)
    (G : C ⥤ D) {X Y : C} {W : D} (e : X ≅ Y) (t : G.obj Y ≅ W) :
    F.map (G.map e.inv) ≫ (F.mapIso (G.mapIso e ≪≫ t)).hom = F.map t.hom := by
  simp only [Functor.mapIso_hom, Iso.trans_hom, ← Functor.map_comp, ← Category.assoc,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp]

/-- Four commutative squares paste. -/
theorem comp_comp_comp_comp_paste {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ Y₄ : C}
    {f₀ : X₀ ⟶ Y₀} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {f₃ : X₃ ⟶ Y₃} {f₄ : X₄ ⟶ Y₄}
    {x₁ : X₀ ⟶ X₁} {x₂ : X₁ ⟶ X₂} {x₃ : X₂ ⟶ X₃} {x₄ : X₃ ⟶ X₄}
    {y₁ : Y₀ ⟶ Y₁} {y₂ : Y₁ ⟶ Y₂} {y₃ : Y₂ ⟶ Y₃} {y₄ : Y₃ ⟶ Y₄}
    (h₁ : f₀ ≫ y₁ = x₁ ≫ f₁) (h₂ : f₁ ≫ y₂ = x₂ ≫ f₂) (h₃ : f₂ ≫ y₃ = x₃ ≫ f₃)
    (h₄ : f₃ ≫ y₄ = x₄ ≫ f₄) :
    f₀ ≫ y₁ ≫ y₂ ≫ y₃ ≫ y₄ = (x₁ ≫ x₂ ≫ x₃ ≫ x₄) ≫ f₄ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [Category.assoc]

/-- `L(η_X ≫ R g) ≫ ε_Y = g`. -/
theorem Adjunction.map_unit_comp_map_comp_counit {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X : C}
    {Y : D} (g : L.obj X ⟶ Y) :
    L.map (adj.unit.app X ≫ R.map g) ≫ adj.counit.app Y = g := by
  have h := adj.counit.naturality g
  simp only [Functor.comp_map, Functor.id_map] at h
  rw [Functor.map_comp, Category.assoc, h, ← Category.assoc]
  simp

/-- The unit of an adjunction transported along an isomorphism of right adjoints. -/
theorem Adjunction.ofNatIsoRight_unit_app' {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) (X : C) :
    (adj.ofNatIsoRight iso).unit.app X = adj.unit.app X ≫ iso.hom.app (F.obj X) := by
  simp [Adjunction.ofNatIsoRight]

/-- The counit of an adjunction transported along an isomorphism of right adjoints. -/
theorem Adjunction.ofNatIsoRight_counit_app' {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) (Y : D) :
    (adj.ofNatIsoRight iso).counit.app Y = F.map (iso.inv.app Y) ≫ adj.counit.app Y := by
  simp [Adjunction.ofNatIsoRight]

/-- **The lax comparison of a composite right adjoint is the composite of the lax
comparisons**, read through the isomorphism `R₂ ⋙ R₁ ≅ Z`. -/
theorem Adjunction.inv_eq_comp_lax {𝒵 𝒮 ℰ : Type*} [Category 𝒵] [Category 𝒮] [Category ℰ]
    {L₁ : 𝒵 ⥤ 𝒮} {R₁ : 𝒮 ⥤ 𝒵} {L₂ : 𝒮 ⥤ ℰ} {R₂ : ℰ ⥤ 𝒮} {Z : ℰ ⥤ 𝒵}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (ι : R₂ ⋙ R₁ ≅ Z)
    (Z2 : 𝒵 ⥤ 𝒵 ⥤ 𝒵) (S2 : 𝒮 ⥤ 𝒮 ⥤ 𝒮) (E2 : ℰ ⥤ ℰ ⥤ ℰ)
    (c₁ : ∀ A B, L₁.obj ((Z2.obj A).obj B) ⟶ (S2.obj (L₁.obj A)).obj (L₁.obj B))
    (hc₁ : ∀ {A A' B B'} (f : A ⟶ A') (g : B ⟶ B'),
      L₁.map ((Z2.map f).app B ≫ (Z2.obj A').map g) ≫ c₁ A' B' =
        c₁ A B ≫ ((S2.map (L₁.map f)).app (L₁.obj B) ≫ (S2.obj (L₁.obj A')).map (L₁.map g)))
    (c₂ : ∀ X Y, L₂.obj ((S2.obj X).obj Y) ⟶ (E2.obj (L₂.obj X)).obj (L₂.obj Y))
    (hc₂ : ∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
      L₂.map ((S2.map f).app Y ≫ (S2.obj X').map g) ≫ c₂ X' Y' =
        c₂ X Y ≫ ((E2.map (L₂.map f)).app (L₂.obj Y) ≫ (E2.obj (L₂.obj X')).map (L₂.map g)))
    (P Q : ℰ) (J : R₂.obj ((E2.obj P).obj Q) ≅ (S2.obj (R₂.obj P)).obj (R₂.obj Q))
    (hJ : J.inv = adj₂.unit.app _ ≫ R₂.map (c₂ _ _ ≫
      ((E2.map (adj₂.counit.app P)).app _ ≫ (E2.obj P).map (adj₂.counit.app Q))))
    (K : R₁.obj ((S2.obj (R₂.obj P)).obj (R₂.obj Q)) ≅
      (Z2.obj (R₁.obj (R₂.obj P))).obj (R₁.obj (R₂.obj Q)))
    (hK : K.inv = adj₁.unit.app _ ≫ R₁.map (c₁ _ _ ≫
      ((S2.map (adj₁.counit.app (R₂.obj P))).app _ ≫
        (S2.obj (R₂.obj P)).map (adj₁.counit.app (R₂.obj Q)))))
    (I : Z.obj ((E2.obj P).obj Q) ≅ (Z2.obj (Z.obj P)).obj (Z.obj Q))
    (hI : I.hom = ι.inv.app _ ≫ R₁.map J.hom ≫ K.hom ≫
      ((Z2.map (ι.hom.app P)).app _ ≫ (Z2.obj (Z.obj P)).map (ι.hom.app Q))) :
    I.inv = ((adj₁.comp adj₂).ofNatIsoRight ι).unit.app ((Z2.obj (Z.obj P)).obj (Z.obj Q)) ≫
      Z.map ((L₂.map (c₁ (Z.obj P) (Z.obj Q)) ≫ c₂ _ _) ≫
        ((E2.map (((adj₁.comp adj₂).ofNatIsoRight ι).counit.app P)).app _ ≫
          (E2.obj P).map (((adj₁.comp adj₂).ofNatIsoRight ι).counit.app Q))) := by
  have h1 : I.inv = ((Z2.map (ι.inv.app P)).app _ ≫ (Z2.obj _).map (ι.inv.app Q)) ≫ K.inv ≫
      R₁.map J.inv ≫ ι.hom.app _ := by
    apply Iso.inv_ext
    rw [hI]
    simp only [Category.assoc]
    rw [Functor.map_app_comp_obj_map_comp_assoc]
    simp [← Functor.map_comp_assoc]
  rw [h1, hJ, hK]
  simp only [Adjunction.ofNatIsoRight_unit_app', Adjunction.ofNatIsoRight_counit_app',
    Adjunction.comp_unit_app, Adjunction.comp_counit_app, Category.assoc]
  rw [← ι.hom.naturality, Functor.comp_map, ← R₁.map_comp_assoc]
  set u := L₁.map (ι.inv.app P) ≫ adj₁.counit.app (R₂.obj P) with hu
  set v := L₁.map (ι.inv.app Q) ≫ adj₁.counit.app (R₂.obj Q) with hv
  have e₁ : (E2.map ((L₁ ⋙ L₂).map (ι.inv.app P) ≫ L₂.map (adj₁.counit.app (R₂.obj P)) ≫
        adj₂.counit.app P)).app (L₂.obj (L₁.obj (Z.obj Q))) ≫
      (E2.obj P).map ((L₁ ⋙ L₂).map (ι.inv.app Q) ≫ L₂.map (adj₁.counit.app (R₂.obj Q)) ≫
        adj₂.counit.app Q) =
      ((E2.map (L₂.map u)).app (L₂.obj (L₁.obj (Z.obj Q))) ≫
        (E2.obj (L₂.obj (R₂.obj P))).map (L₂.map v)) ≫
      ((E2.map (adj₂.counit.app P)).app (L₂.obj (R₂.obj Q)) ≫
        (E2.obj P).map (adj₂.counit.app Q)) := by
    have h := Functor.map_app_comp_obj_map_comp E2 (L₂.map u) (adj₂.counit.app P) (L₂.map v)
      (adj₂.counit.app Q)
    simp only [Functor.id_obj] at h
    rw [h, hu, hv, Functor.comp_map, Functor.comp_map,
      L₂.map_comp, L₂.map_comp, Category.assoc, Category.assoc]
  have e₂ : (S2.map u).app (L₁.obj (Z.obj Q)) ≫ (S2.obj (R₂.obj P)).map v =
      ((S2.map (L₁.map (ι.inv.app P))).app (L₁.obj (Z.obj Q)) ≫
        (S2.obj (L₁.obj ((R₂ ⋙ R₁).obj P))).map (L₁.map (ι.inv.app Q))) ≫
      ((S2.map (adj₁.counit.app (R₂.obj P))).app (L₁.obj (R₁.obj (R₂.obj Q))) ≫
        (S2.obj (R₂.obj P)).map (adj₁.counit.app (R₂.obj Q))) := by
    have h := Functor.map_app_comp_obj_map_comp S2 (L₁.map (ι.inv.app P))
      (adj₁.counit.app (R₂.obj P)) (L₁.map (ι.inv.app Q)) (adj₁.counit.app (R₂.obj Q))
    exact h.symm
  have hη₂ := adj₂.unit.naturality (c₁ (Z.obj P) (Z.obj Q) ≫
    ((S2.map u).app (L₁.obj (Z.obj Q)) ≫ (S2.obj (R₂.obj P)).map v))
  have hη₁ := adj₁.unit.naturality ((Z2.map (ι.inv.app P)).app (Z.obj Q) ≫
    (Z2.obj ((R₂ ⋙ R₁).obj P)).map (ι.inv.app Q))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hη₂ hη₁
  rw [e₁]
  simp only [Category.assoc]
  rw [← reassoc_of% (hc₂ u v), ← L₂.map_comp_assoc]
  conv_rhs => rw [← R₁.map_comp_assoc, R₂.map_comp, ← reassoc_of% hη₂, reassoc_of% e₂]
  rw [← reassoc_of% (hc₁ (ι.inv.app P) (ι.inv.app Q))]
  simp only [R₁.map_comp, R₂.map_comp, Category.assoc]
  rw [← reassoc_of% hη₁]
  rfl

section Transpose

variable {ℰ ℰ' 𝒵 𝒵' : Type*} [Category ℰ] [Category ℰ'] [Category 𝒵] [Category 𝒵']
  {φu : ℰ ⥤ ℰ'} {φl : ℰ' ⥤ ℰ} {τu : 𝒵 ⥤ 𝒵'} {τl : 𝒵' ⥤ 𝒵}
  {a : 𝒵 ⥤ ℰ} {Z : ℰ ⥤ 𝒵} {a' : 𝒵' ⥤ ℰ'} {Z' : ℰ' ⥤ 𝒵'}
  (adjφ : φu ⊣ φl) (adjτ : τu ⊣ τl) (adja : a ⊣ Z) (adja' : a' ⊣ Z')
  (σ : φl ⋙ Z ⟶ Z' ⋙ τl)

/-- The transposed comparison, transposed once more along `a' ⊣ Z'`, is the conjugate of `σ`
followed by `φ^*` of the counit. -/
theorem Adjunction.map_transposeComparison_comp_counit (N : ℰ) :
    a'.map (Adjunction.transposeComparison adjφ adjτ σ N) ≫ adja'.counit.app (φu.obj N) =
      ((conjugateEquiv (adja.comp adjφ) (adjτ.comp adja')).symm σ).app (Z.obj N) ≫
        φu.map (adja.counit.app N) := by
  rw [Adjunction.transposeComparison_eq adjφ adjτ adja adja' σ N, ← Z'.map_comp]
  exact Adjunction.map_unit_comp_map_comp_counit adja' _

/-- **Monoidality of the transposed comparison.**  Given comparisons `c_a`, `c_{a'}`, `c_φ`,
`c_τ` of the left adjoints with tensor bifunctors, the lax comparisons
`μ = η ≫ Z(c_a ≫ (ε ⊗ ε))` of `Z` and `Z'`, and the monoidality of the conjugate
`m : τ^* ⋙ a' ⟶ a ⋙ φ^*` of `σ`, the transposed comparison is monoidal:
`τ^*(μ) ≫ θ_{P ⊗ Q} ≫ Z'(c_φ) = c_τ ≫ (θ_P ⊗ θ_Q) ≫ μ'`. -/
theorem Adjunction.transposeComparison_tensor (E2 : ℰ ⥤ ℰ ⥤ ℰ) (E2' : ℰ' ⥤ ℰ' ⥤ ℰ')
    (Z2 : 𝒵 ⥤ 𝒵 ⥤ 𝒵) (Z2' : 𝒵' ⥤ 𝒵' ⥤ 𝒵')
    (ca : ∀ A B, a.obj ((Z2.obj A).obj B) ⟶ (E2.obj (a.obj A)).obj (a.obj B))
    (ca' : ∀ A B, a'.obj ((Z2'.obj A).obj B) ⟶ (E2'.obj (a'.obj A)).obj (a'.obj B))
    (hca' : ∀ {A A' B B'} (f : A ⟶ A') (g : B ⟶ B'),
      a'.map ((Z2'.map f).app B ≫ (Z2'.obj A').map g) ≫ ca' A' B' =
        ca' A B ≫ ((E2'.map (a'.map f)).app (a'.obj B) ≫ (E2'.obj (a'.obj A')).map (a'.map g)))
    (cφ : ∀ M N, φu.obj ((E2.obj M).obj N) ⟶ (E2'.obj (φu.obj M)).obj (φu.obj N))
    (hcφ : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      φu.map ((E2.map f).app N ≫ (E2.obj M').map g) ≫ cφ M' N' =
        cφ M N ≫ ((E2'.map (φu.map f)).app (φu.obj N) ≫ (E2'.obj (φu.obj M')).map (φu.map g)))
    (cτ : ∀ A B, τu.obj ((Z2.obj A).obj B) ⟶ (Z2'.obj (τu.obj A)).obj (τu.obj B))
    (hm : ∀ A B,
      ((conjugateEquiv (adja.comp adjφ) (adjτ.comp adja')).symm σ).app ((Z2.obj A).obj B) ≫
          φu.map (ca A B) ≫ cφ (a.obj A) (a.obj B) =
        a'.map (cτ A B) ≫ ca' (τu.obj A) (τu.obj B) ≫
          ((E2'.map (((conjugateEquiv (adja.comp adjφ) (adjτ.comp adja')).symm σ).app A)).app
              (a'.obj (τu.obj B)) ≫
            (E2'.obj (φu.obj (a.obj A))).map
              (((conjugateEquiv (adja.comp adjφ) (adjτ.comp adja')).symm σ).app B)))
    (P Q : ℰ) :
    τu.map (adja.unit.app ((Z2.obj (Z.obj P)).obj (Z.obj Q)) ≫
        Z.map (ca (Z.obj P) (Z.obj Q) ≫ ((E2.map (adja.counit.app P)).app (a.obj (Z.obj Q)) ≫
          (E2.obj P).map (adja.counit.app Q)))) ≫
        Adjunction.transposeComparison adjφ adjτ σ ((E2.obj P).obj Q) ≫ Z'.map (cφ P Q) =
      cτ (Z.obj P) (Z.obj Q) ≫
        ((Z2'.map (Adjunction.transposeComparison adjφ adjτ σ P)).app (τu.obj (Z.obj Q)) ≫
          (Z2'.obj (Z'.obj (φu.obj P))).map (Adjunction.transposeComparison adjφ adjτ σ Q)) ≫
        adja'.unit.app ((Z2'.obj (Z'.obj (φu.obj P))).obj (Z'.obj (φu.obj Q))) ≫
          Z'.map (ca' (Z'.obj (φu.obj P)) (Z'.obj (φu.obj Q)) ≫
            ((E2'.map (adja'.counit.app (φu.obj P))).app (a'.obj (Z'.obj (φu.obj Q))) ≫
            (E2'.obj (φu.obj P)).map (adja'.counit.app (φu.obj Q)))) := by
  set m := (conjugateEquiv (adja.comp adjφ) (adjτ.comp adja')).symm σ with hmdef
  set θ := Adjunction.transposeComparison adjφ adjτ σ with hθ
  set μ := adja.unit.app ((Z2.obj (Z.obj P)).obj (Z.obj Q)) ≫
        Z.map (ca (Z.obj P) (Z.obj Q) ≫ ((E2.map (adja.counit.app P)).app (a.obj (Z.obj Q)) ≫
          (E2.obj P).map (adja.counit.app Q))) with hμ
  have hmn : a'.map (τu.map μ) ≫ m.app (Z.obj ((E2.obj P).obj Q)) =
      m.app ((Z2.obj (Z.obj P)).obj (Z.obj Q)) ≫ φu.map (a.map μ) := m.naturality μ
  have e1 : a.map μ ≫ adja.counit.app ((E2.obj P).obj Q) =
      ca (Z.obj P) (Z.obj Q) ≫ ((E2.map (adja.counit.app P)).app (a.obj (Z.obj Q)) ≫
          (E2.obj P).map (adja.counit.app Q)) :=
    Adjunction.map_unit_comp_map_comp_counit adja _
  have hcn : a'.map (Z'.map (cφ P Q)) ≫ adja'.counit.app _ =
      adja'.counit.app _ ≫ cφ P Q := adja'.counit.naturality (cφ P Q)
  have ePQ := Adjunction.map_transposeComparison_comp_counit adjφ adjτ adja adja' σ
    ((E2.obj P).obj Q)
  have eP := Adjunction.map_transposeComparison_comp_counit adjφ adjτ adja adja' σ P
  have eQ := Adjunction.map_transposeComparison_comp_counit adjφ adjτ adja adja' σ Q
  rw [← hmdef, ← hθ] at ePQ eP eQ
  clear_value m θ μ
  apply (adja'.homEquiv _ _).symm.injective
  simp only [homEquiv_counit]
  have hL : a'.map (τu.map μ ≫ θ ((E2.obj P).obj Q) ≫ Z'.map (cφ P Q)) ≫ adja'.counit.app _ =
      m.app ((Z2.obj (Z.obj P)).obj (Z.obj Q)) ≫ φu.map (ca (Z.obj P) (Z.obj Q)) ≫
        cφ (a.obj (Z.obj P)) (a.obj (Z.obj Q)) ≫
          ((E2'.map (φu.map (adja.counit.app P))).app (φu.obj (a.obj (Z.obj Q))) ≫
            (E2'.obj (φu.obj P)).map (φu.map (adja.counit.app Q))) := by
    rw [a'.map_comp, a'.map_comp]
    simp only [Category.assoc]
    have e4 := hcφ (adja.counit.app P) (adja.counit.app Q)
    simp only [Functor.id_obj, Functor.comp_obj] at e4
    rw [hcn, reassoc_of% ePQ, reassoc_of% hmn, ← φu.map_comp_assoc, e1, φu.map_comp,
      Category.assoc, e4]
  have hR : a'.map (cτ (Z.obj P) (Z.obj Q) ≫
        ((Z2'.map (θ P)).app (τu.obj (Z.obj Q)) ≫ (Z2'.obj (Z'.obj (φu.obj P))).map (θ Q)) ≫
        adja'.unit.app ((Z2'.obj (Z'.obj (φu.obj P))).obj (Z'.obj (φu.obj Q))) ≫
          Z'.map (ca' (Z'.obj (φu.obj P)) (Z'.obj (φu.obj Q)) ≫
            ((E2'.map (adja'.counit.app (φu.obj P))).app (a'.obj (Z'.obj (φu.obj Q))) ≫
            (E2'.obj (φu.obj P)).map (adja'.counit.app (φu.obj Q))))) ≫ adja'.counit.app _ =
      a'.map (cτ (Z.obj P) (Z.obj Q)) ≫ ca' (τu.obj (Z.obj P)) (τu.obj (Z.obj Q)) ≫
          ((E2'.map (m.app (Z.obj P))).app (a'.obj (τu.obj (Z.obj Q))) ≫
            (E2'.obj (φu.obj (a.obj (Z.obj P)))).map (m.app (Z.obj Q))) ≫
          ((E2'.map (φu.map (adja.counit.app P))).app (φu.obj (a.obj (Z.obj Q))) ≫
            (E2'.obj (φu.obj P)).map (φu.map (adja.counit.app Q))) := by
    rw [Functor.map_comp a' (cτ _ _), Functor.map_comp a' ((Z2'.map (θ P)).app _ ≫ _)]
    simp only [Category.assoc]
    have e5 := Functor.map_app_comp_obj_map_comp E2' (a'.map (θ P)) (adja'.counit.app _)
      (a'.map (θ Q)) (adja'.counit.app _)
    rw [eP, eQ, ← Functor.map_app_comp_obj_map_comp] at e5
    simp only [Functor.id_obj, Category.assoc] at e5
    rw [Adjunction.map_unit_comp_map_comp_counit, reassoc_of% hca', e5]
    rfl
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hm' := hm (Z.obj P) (Z.obj Q)
  simp only [Category.assoc] at hm' ⊢
  rw [reassoc_of% hm']

end Transpose

end CategoryTheory

/-! ### The étale associated module and its Zariski restriction -/

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03EL at `ε` is natural**: the associated module of a tensor product of morphisms is
the tensor product of their associated modules. -/
theorem associatedModuleTensorIso_hom_naturality {M M' N N' : S.Modules} (a : M ⟶ M')
    (b : N ⟶ N') :
    (associatedModule B S hS).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          S.zariskiRingedSite.toRingedTopos.O).map a).app N ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            S.zariskiRingedSite.toRingedTopos.O).obj M').map b) ≫
        (associatedModuleTensorIso B S hS M' N').hom =
      (associatedModuleTensorIso B S hS M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS).toRingedTopos.O).map
            ((associatedModule B S hS).map a)).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedSite B S hS).toRingedTopos.O).obj _).map
            ((associatedModule B S hS).map b)) :=
  NatIso.app_hom_naturality_curried _ _ _ (associatedModuleTensorBifunctorIso B S hS)
    (associatedModuleTensorIso B S hS) (associatedModuleTensorBifunctorIso_app B S hS) a b

/-- The inverse of the Zariski restriction of a tensor product, unfolded. -/
theorem restrictModuleTensorIso_inv_eq_unit_comp_lax'
    (M N : SheafOfModules.{u} (structureSheaf B S hS))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (restrictModuleTensorIso B S hS M N hM hN).inv =
      (associatedModuleAdjunction B S hS).unit.app _ ≫
        (restrictModule B S hS).map ((associatedModuleTensorIso B S hS _ _).hom ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedSite B S hS).toRingedTopos.O).obj
              ((associatedModule B S hS).obj ((restrictModule B S hS).obj M))).map
              ((associatedModuleAdjunction B S hS).counit.app N) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedSite B S hS).toRingedTopos.O).map
              ((associatedModuleAdjunction B S hS).counit.app M)).app N)) :=
  rfl

/-- **The inverse of the Zariski restriction of a tensor product is the lax comparison of the
right adjoint**: the unit followed by the restriction of Stacks 03EL at `ε` and of the two
counits. -/
theorem restrictModuleTensorIso_inv_eq_unit_comp_lax
    (M N : SheafOfModules.{u} (structureSheaf B S hS))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (restrictModuleTensorIso B S hS M N hM hN).inv =
      (associatedModuleAdjunction B S hS).unit.app _ ≫
        (restrictModule B S hS).map ((associatedModuleTensorIso B S hS _ _).hom ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedSite B S hS).toRingedTopos.O).map
              ((associatedModuleAdjunction B S hS).counit.app M)).app _ ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedSite B S hS).toRingedTopos.O).obj M).map
              ((associatedModuleAdjunction B S hS).counit.app N))) :=
  (restrictModuleTensorIso_inv_eq_unit_comp_lax' B S hS M N hM hN).trans
    (congrArg (fun k => _ ≫ (restrictModule B S hS).map (_ ≫ k))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedSite B S hS).toRingedTopos.O).map
              ((associatedModuleAdjunction B S hS).counit.app M)).naturality
        ((associatedModuleAdjunction B S hS).counit.app N)))

/-- **The Zariski restriction of a tensor product of quasi-coherent modules is natural.** -/
theorem restrictModuleTensorIso_hom_naturality
    {M M' N N' : SheafOfModules.{u} (structureSheaf B S hS)} (a : M ⟶ M') (b : N ⟶ N')
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hM' : M'.IsQuasicoherentOnSite) (hN' : N'.IsQuasicoherentOnSite) :
    (restrictModule B S hS).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS).toRingedTopos.O).map a).app N ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedSite B S hS).toRingedTopos.O).obj M').map b) ≫
        (restrictModuleTensorIso B S hS M' N' hM' hN').hom =
      (restrictModuleTensorIso B S hS M N hM hN).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          S.zariskiRingedSite.toRingedTopos.O).map ((restrictModule B S hS).map a)).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            S.zariskiRingedSite.toRingedTopos.O).obj _).map ((restrictModule B S hS).map b)) := by
  refine Iso.hom_comp_eq_of_inv_comp _ _ _ _ ?_
  rw [restrictModuleTensorIso_inv_eq_unit_comp_lax, restrictModuleTensorIso_inv_eq_unit_comp_lax]
  exact Adjunction.unit_comp_map_comp_counit_naturality (associatedModuleAdjunction B S hS)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.zariskiRingedSite.toRingedTopos.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS).toRingedTopos.O)
    (fun X Y => (associatedModuleTensorIso B S hS X Y).hom)
    (fun f g => associatedModuleTensorIso_hom_naturality B S hS f g) a b

end AlgebraicGeometry.SmallEtale

/-! ### The comparison of Stacks 04M0 -/

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (e : C' ≌ C) [e.functor.IsContinuous J' J]
  (O : Sheaf J CommRingCat.{w})
  [hmos : _root_.IsMorphismOfSites.{w} e.inverse J J']
  [J.HasSheafCompose (forget RingCat.{w})] [J'.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [J'.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C] [LocallySmall.{w} C']

/-- The compatibility of the reindexing along an equivalence of sites with the tensor product
sheaf, as an isomorphism of bifunctors. -/
def reindexTensorBifunctorIso :
    Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O) ⋙
        (reindexEquivalence.{w, w, u, v, u, v} e
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor ≅
      Functor.prod (reindexEquivalence.{w, w, u, v, u, v} e
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor
        (reindexEquivalence.{w, w, u, v, u, v} e
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor ⋙
        Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          (reindexCommRing J' e O)) :=
  Functor.isoWhiskerLeft _ (pullbackModulesReindexIso J' e O).symm ≪≫
    Stacks.SheafOfModules.pullbackTensorIso (reindexRingedToposModulesHom J' e O) ≪≫
    Functor.isoWhiskerRight (NatIso.prod (pullbackModulesReindexIso J' e O)
      (pullbackModulesReindexIso J' e O)) _

/-- The components of `Stacks.SheafOfModules.reindexTensorBifunctorIso` are
`Stacks.SheafOfModules.reindexTensorIso`. -/
theorem reindexTensorBifunctorIso_app
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (reindexTensorBifunctorIso J' e O).app (M, N) = reindexTensorIso J' e O M N :=
  AlgebraicGeometry.SmallEtale.isoWhiskerLeft_trans_isoWhiskerRight_prod_app
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (reindexCommRing J' e O))
    (pullbackModulesReindexIso J' e O)
    (Stacks.SheafOfModules.pullbackTensorIso (reindexRingedToposModulesHom J' e O)) M N

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

section Represented

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The comparison of Stacks 04M0 with the tensor product is natural.** -/
theorem representedSmallEtaleModuleTensorIso_hom_naturality
    {M M' N N' : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)} (a : M ⟶ M')
    (b : N ⟶ N') :
    (representedSmallEtaleModuleEquivalence B S hS U).functor.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (representedSchemeCommRingStructureSheaf B S hS U)).map a).app N ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (representedSchemeCommRingStructureSheaf B S hS U)).obj M').map b) ≫
        (representedSmallEtaleModuleTensorIso B S hS U M' N').hom =
      (representedSmallEtaleModuleTensorIso B S hS U M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).map
            ((representedSmallEtaleModuleEquivalence B S hS U).functor.map a)).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj _).map
            ((representedSmallEtaleModuleEquivalence B S hS U).functor.map b)) :=
  NatIso.app_hom_naturality_curried _ _ _
    (Stacks.SheafOfModules.reindexTensorBifunctorIso
      (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U))
    (representedSmallEtaleModuleTensorIso B S hS U)
    (Stacks.SheafOfModules.reindexTensorBifunctorIso_app
      (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U))
    a b

/-- The inverse comparison of Stacks 04M0 with the tensor product, unfolded. -/
theorem representedSmallEtaleModuleInverseTensorIso_eq
    (P Q : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    representedSmallEtaleModuleInverseTensorIso B S hS U P Q =
  (representedSmallEtaleModuleEquivalence B S hS U).inverse.mapIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).mapIso (X := P)
          (Y := (representedSmallEtaleModuleEquivalence B S hS U).functor.obj
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P))
          ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app P).symm).app Q ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS (yoneda.obj U)
              (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj
            ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj
              ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P))).mapIso
          (X := Q)
          (Y := (representedSmallEtaleModuleEquivalence B S hS U).functor.obj
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q))
          ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app Q).symm ≪≫
        (representedSmallEtaleModuleTensorIso B S hS U
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q)).symm) ≪≫
    ((representedSmallEtaleModuleEquivalence B S hS U).unitIso.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (representedSchemeCommRingStructureSheaf B S hS U)).obj
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)).obj
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q))).symm :=
  rfl

/-- The inverse of the inverse comparison of Stacks 04M0 with the tensor product, unfolded. -/
theorem representedSmallEtaleModuleInverseTensorIso_inv_eq'
    (P Q : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (representedSmallEtaleModuleInverseTensorIso B S hS U P Q).inv =
      (representedSmallEtaleModuleEquivalence B S hS U).unitIso.hom.app
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (representedSchemeCommRingStructureSheaf B S hS U)).obj
              ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)).obj
              ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q)) ≫
        (representedSmallEtaleModuleEquivalence B S hS U).inverse.map
          (((representedSmallEtaleModuleTensorIso B S hS U
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q)).hom ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              (structureSheaf B S hS (yoneda.obj U)
                (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj
              ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj
                ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P))).map
              ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.hom.app Q)) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              (structureSheaf B S hS (yoneda.obj U)
                (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).map
              ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.hom.app P)).app Q) :=
  by rw [representedSmallEtaleModuleInverseTensorIso_eq]; rfl

/-- **The inverse of the inverse comparison of Stacks 04M0 with the tensor product is the lax
comparison of the inverse equivalence.** -/
theorem representedSmallEtaleModuleInverseTensorIso_inv_eq
    (P Q : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (representedSmallEtaleModuleInverseTensorIso B S hS U P Q).inv =
      (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction.unit.app
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (representedSchemeCommRingStructureSheaf B S hS U)).obj
              ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)).obj
              ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q)) ≫
        (representedSmallEtaleModuleEquivalence B S hS U).inverse.map
          ((representedSmallEtaleModuleTensorIso B S hS U
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q)).hom ≫
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              (structureSheaf B S hS (yoneda.obj U)
                (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).map
              ((representedSmallEtaleModuleEquivalence B S hS U).toAdjunction.counit.app P)).app _ ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              (structureSheaf B S hS (yoneda.obj U)
                (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj P).map
              ((representedSmallEtaleModuleEquivalence B S hS U).toAdjunction.counit.app Q))) :=
  (representedSmallEtaleModuleInverseTensorIso_inv_eq' B S hS U P Q).trans
    (congrArg (fun k => _ ≫ (representedSmallEtaleModuleEquivalence B S hS U).inverse.map k)
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).map
          ((representedSmallEtaleModuleEquivalence B S hS U).toAdjunction.counit.app P)).naturality
          ((representedSmallEtaleModuleEquivalence B S hS U).toAdjunction.counit.app Q)))))

/-- **The inverse comparison of Stacks 04M0 with the tensor product is natural.** -/
theorem representedSmallEtaleModuleInverseTensorIso_hom_naturality
    {P P' Q Q' : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)} (a : P ⟶ P')
    (b : Q ⟶ Q') :
    (representedSmallEtaleModuleEquivalence B S hS U).inverse.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).map a).app Q ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj P').map b) ≫
        (representedSmallEtaleModuleInverseTensorIso B S hS U P' Q').hom =
      (representedSmallEtaleModuleInverseTensorIso B S hS U P Q).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (representedSchemeCommRingStructureSheaf B S hS U)).map
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.map a)).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (representedSchemeCommRingStructureSheaf B S hS U)).obj _).map
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.map b)) := by
  refine Iso.hom_comp_eq_of_inv_comp _ _ _ _ ?_
  rw [representedSmallEtaleModuleInverseTensorIso_inv_eq,
    representedSmallEtaleModuleInverseTensorIso_inv_eq]
  exact Adjunction.unit_comp_map_comp_counit_naturality
    (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (representedSchemeCommRingStructureSheaf B S hS U))
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)))
    (fun X Y => (representedSmallEtaleModuleTensorIso B S hS U X Y).hom)
    (fun f g => representedSmallEtaleModuleTensorIso_hom_naturality B S hS U f g) a b

end Represented

section Monoidal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The comparison of the monoidal product of `𝒪`-modules with the tensor product sheaf is
natural. -/
theorem modulesTensorObjIso_hom_naturality_tensorHom {G₁ G₂ G₁' G₂' : Modules.{u, u} B S hS F hF}
    (a : G₁ ⟶ G₂) (b : G₁' ⟶ G₂') :
    (a ⊗ₘ b) ≫ (modulesTensorObjIso B S hS F hF G₂ G₂').hom =
      (modulesTensorObjIso B S hS F hF G₁ G₁').hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS F hF)).map a).app G₁' ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS F hF)).obj G₂).map b) :=
  (Stacks.SheafOfModules.tensorObjIso_naturality _ _ a b).trans
    (congrArg (_ ≫ ·) (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ a b).symm)

end Monoidal

section Reading

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (T : BigFppfOver B S hS)

/-- The inverse equivalence sends a quasi-coherent module to a quasi-coherent module. -/
private theorem isQuasicoherentOnSite_inverse_obj
    {P : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hP : P.IsQuasicoherentOnSite) :
    ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj P).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T _).1
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((representedSmallEtaleModuleEquivalence B S hS T).counitIso.app P).symm hP)

/-- **The Zariski reading tensor isomorphism, with its identity-chart detour cancelled**: the
inverse identification of the reading with the restriction of the module read on the scheme,
the 04M0 and 03DX tensor comparisons, and the two identifications on the factors. -/
theorem zariskiReadingTensorObjIso_hom_eq
    (P Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    (zariskiReadingTensorObjIso T P Q hP hQ).hom =
      (selfOpensPushforwardIso B S hS T (P ⊗ Q)).inv ≫
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso
            (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) P Q) ≪≫
            representedSmallEtaleModuleInverseTensorIso B S hS T P Q)).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj P)
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj Q)
          ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T _).1
            (SheafOfModules.IsQuasicoherentOnSite.of_iso
              ((representedSmallEtaleModuleEquivalence B S hS T).counitIso.app P).symm hP))
          ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T _).1
            (SheafOfModules.IsQuasicoherentOnSite.of_iso
              ((representedSmallEtaleModuleEquivalence B S hS T).counitIso.app Q).symm hQ))).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).map
            (selfOpensPushforwardIso B S hS T P).hom).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).obj _).map
            (selfOpensPushforwardIso B S hS T Q).hom) :=
  Iso.hom_eq_of_eq_cancel _
    ((zariskiReadingFunctor T).mapIso
      (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) P Q))
    (restrictToChartSchemeIdEtaleChartIso B S hS T (P ⊗ Q))
    (selfOpensPushforwardIso B S hS T (P ⊗ Q)) _ _
    (restrictToChartSchemeIdEtaleChartIso B S hS T P) (selfOpensPushforwardIso B S hS T P)
    (restrictToChartSchemeIdEtaleChartIso B S hS T Q) (selfOpensPushforwardIso B S hS T Q)
    (zariskiReadingTensorObjIso T P Q hP hQ) rfl

/-- The identification of the Zariski reading with the restriction of the module read on the
scheme is natural. -/
theorem selfOpensPushforwardIso_hom_naturality
    {N N' : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (g : N ⟶ N') :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map g) ≫
        (selfOpensPushforwardIso B S hS T N').hom =
      (selfOpensPushforwardIso B S hS T N).hom ≫ (zariskiReadingFunctor T).map g :=
  (zariskiReadingIso T).hom.naturality g

/-- `AlgebraicGeometry.Space.selfOpensPushforwardIso_hom_naturality` for the inverses. -/
theorem selfOpensPushforwardIso_inv_naturality
    {N N' : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (g : N ⟶ N') :
    (zariskiReadingFunctor T).map g ≫ (selfOpensPushforwardIso B S hS T N').inv =
      (selfOpensPushforwardIso B S hS T N).inv ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map g) :=
  (zariskiReadingIso T).inv.naturality g

/-- **Naturality of the Zariski reading tensor isomorphism**, with the tensor product of the
two readings of morphisms written through the tensor product sheaf bifunctor. -/
theorem zariskiReadingTensorObjIso_hom_naturality'
    {P P' Q Q' : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (a : P ⟶ P') (b : Q ⟶ Q') (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite)
    (hP' : P'.IsQuasicoherentOnSite) (hQ' : Q'.IsQuasicoherentOnSite) :
    (zariskiReadingFunctor T).map
      (MonoidalCategory.tensorHom (C := Modules.{u, u} B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)) a b) ≫ (zariskiReadingTensorObjIso T P' Q' hP' hQ').hom =
      (zariskiReadingTensorObjIso T P Q hP hQ).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).map
            ((zariskiReadingFunctor T).map a)).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).obj _).map
            ((zariskiReadingFunctor T).map b)) := by
  have h₁ := selfOpensPushforwardIso_inv_naturality T
    (MonoidalCategory.tensorHom (C := Modules.{u, u} B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)) a b)
  have h₃ := _root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso_hom_naturality
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
    ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map a)
    ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map b)
    (isQuasicoherentOnSite_inverse_obj T hP) (isQuasicoherentOnSite_inverse_obj T hQ)
    (isQuasicoherentOnSite_inverse_obj T hP') (isQuasicoherentOnSite_inverse_obj T hQ')
  rw [zariskiReadingTensorObjIso_hom_eq, zariskiReadingTensorObjIso_hom_eq]
  refine comp_comp_comp_comp_paste h₁ ?_ h₃ ?_
  · exact Functor.map_map_comp_mapIso_trans_hom _ _
      (modulesTensorObjIso_hom_naturality_tensorHom B S hS (yoneda.obj T)
        (isAlgebraicSpace_yoneda B S hS T) a b)
      (representedSmallEtaleModuleInverseTensorIso_hom_naturality B S hS T a b)
  · exact Functor.map_app_comp_obj_map_square _ (selfOpensPushforwardIso_hom_naturality T a)
      (selfOpensPushforwardIso_hom_naturality T b)

/-- **The Zariski reading tensor isomorphism at the tensor product sheaf, with its
identity-chart detour cancelled.** -/
theorem zariskiReadingTensorIso_hom_eq
    (P Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    (zariskiReadingTensorIso T P Q hP hQ).hom =
      (zariskiReadingIso T).inv.app _ ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
          (representedSmallEtaleModuleInverseTensorIso B S hS T P Q).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj P)
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj Q)
          ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T _).1
            (SheafOfModules.IsQuasicoherentOnSite.of_iso
              ((representedSmallEtaleModuleEquivalence B S hS T).counitIso.app P).symm hP))
          ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T _).1
            (SheafOfModules.IsQuasicoherentOnSite.of_iso
              ((representedSmallEtaleModuleEquivalence B S hS T).counitIso.app Q).symm hQ))).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).map
            ((zariskiReadingIso T).hom.app P)).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).obj _).map
            ((zariskiReadingIso T).hom.app Q)) :=
  (Functor.eq_map_inv_comp_of_eq_map_hom_comp (zariskiReadingFunctor T)
      (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) P Q) _ _
      rfl).trans
    ((congrArg (_ ≫ ·) (zariskiReadingTensorObjIso_hom_eq T P Q hP hQ)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (selfOpensPushforwardIso_inv_naturality T
          (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) P
            Q).inv)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ _) (Functor.map_map_inv_comp_mapIso_trans_hom _ _
              (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) P Q)
              (representedSmallEtaleModuleInverseTensorIso B S hS T P Q)))))))))

section SchemeTensor

attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

/-- **Naturality of the Zariski reading tensor isomorphism**:
`R_T(a ⊗ b) ≫ (R_T(P' ⊗ Q') ≅ R_T P' ⊗ R_T Q') = (R_T(P ⊗ Q) ≅ R_T P ⊗ R_T Q) ≫ (R_T a ⊗ R_T b)`
for morphisms `a : P ⟶ P'` and `b : Q ⟶ Q'` of quasi-coherent modules. -/
theorem zariskiReadingTensorObjIso_hom_naturality
    {P P' Q Q' : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (a : P ⟶ P') (b : Q ⟶ Q') (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite)
    (hP' : P'.IsQuasicoherentOnSite) (hQ' : Q'.IsQuasicoherentOnSite) :
    (zariskiReadingFunctor T).map
      (MonoidalCategory.tensorHom (C := Modules.{u, u} B S hS (yoneda.obj T)
        (isAlgebraicSpace_yoneda B S hS T)) a b) ≫
        (zariskiReadingTensorObjIso T P' Q' hP' hQ').hom =
      (zariskiReadingTensorObjIso T P Q hP hQ).hom ≫
        (MonoidalCategory.tensorHom (C := ((BigFppfOver.toScheme B S hS).obj T).Modules)
          ((zariskiReadingFunctor T).map a) ((zariskiReadingFunctor T).map b)) :=
  (zariskiReadingTensorObjIso_hom_naturality' T a b hP hQ hP' hQ').trans
    (congrArg (_ ≫ ·) (Stacks.PullbackSheafTensor.tensorSheafMap_eq_tensorHom
      ((zariskiReadingFunctor T).map a) ((zariskiReadingFunctor T).map b)))

end SchemeTensor

end Reading

end AlgebraicGeometry.Space

end
