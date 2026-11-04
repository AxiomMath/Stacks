module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedPullbackTensor

/-!
# Stacks 07A4 on affine representables, on total complexes

Let `g : U' ⟶ U` be a morphism of objects of the big fppf site with affine underlying schemes, with
map of rings of global functions `A ⟶ A'`. For complexes `P`, `N` of `A`-modules, the comparison
`g^*Tot(P ⊗ N)^~ ≅ Tot((A' ⊗ P) ⊗ (A' ⊗ N))^~` through Stacks 03EL on total complexes and the one
through the extension of scalars of the total complex differ by multiplication by an element of
`A'`, the same for all `P`, `N`.

The comparison is made for an arbitrary morphism of ringed topoi `f`, functors
`G : Mod(A) ⥤ Mod(𝒪_Y)`, `G' : Mod(A') ⥤ Mod(𝒪_X)` with `G'` fully faithful and
`G ⋙ f^* ≅ (A' ⊗_A -) ⋙ G'`, and is then specialized to the associated modules.

## Main results

* `Stacks.Generic.pullbackTensorChain_eq`: the comparison of total complexes, for abstract
  functors and bifunctors, from the comparison on objects.
* `Stacks.Sheaves.DerivedPullback.exists_pullbackTensorModuleHom_eq`: the two module-level
  comparisons `f^*(M ⊗ N)' ≅ ((A' ⊗ M) ⊗ (A' ⊗ N))''` differ by a unit.
* `Stacks.Sheaves.DerivedPullback.exists_pullbackTensorTotalChain_eq`: the same on total complexes.
* `AlgebraicGeometry.Space.exists_representedAffinePullbackTensorChain_eq`: the case of the
  associated modules on affine representables.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Generic

/-- A summand inclusion composed with the inverse of an isomorphism of complexes is read off from
its composite with the forward map. -/
private theorem comp_inv_f_of_comp_hom_f {ι : Type*} {c : ComplexShape ι} {C : Type*}
    {_ : Category C} {_ : Preadditive C} {K L : HomologicalComplex C c} (e : K ≅ L) (n : ι)
    {A B : C} (τ : A ≅ B) (f : A ⟶ K.X n) (g : B ⟶ L.X n) (h : f ≫ e.hom.f n = τ.hom ≫ g) :
    g ≫ e.inv.f n = τ.inv ≫ f := by
  rw [Iso.eq_inv_comp, ← reassoc_of% h, ← HomologicalComplex.comp_f, Iso.hom_inv_id]
  simp

/-- **Two comparisons of total complexes from one comparison of modules.**  Let
`G : V ⥤ W`, `pb : W ⥤ W'`, `ext : V ⥤ V'`, `G' : V' ⥤ W'` with `r : G ⋙ pb ≅ ext ⋙ G'`, and
bifunctors on the four categories with comparisons `τ`, `σ`, `τ'` and `δ₀` on objects, read on
total complexes by `t`, `Θ`, `t'` and `μ`.  If the module-level comparison through `σ` is the
one through `δ₀` followed by `z`, then the two comparisons of total complexes differ by the map
`Z` induced by `z`. -/
theorem pullbackTensorChain_eq {ι : Type*} {c : ComplexShape ι} {_ : TotalComplexShape c c c}
    {_ : DecidableEq ι}
    {V W W' V' : Type*} {_ : Category V} {_ : Category W} {_ : Category W'} {_ : Category V'}
    {_ : Preadditive V} {_ : Preadditive W} {_ : Preadditive W'} {_ : Preadditive V'}
    {G : V ⥤ W} {pb : W ⥤ W'} {ext : V ⥤ V'} {G' : V' ⥤ W'}
    [G.Additive] [pb.Additive] [ext.Additive] [G'.Additive]
    [(ext ⋙ G').Additive]
    {TV : V ⥤ V ⥤ V} {TW : W ⥤ W ⥤ W} {TW' : W' ⥤ W' ⥤ W'} {TV' : V' ⥤ V' ⥤ V'}
    {_ : TV.PreservesZeroMorphisms} {_ : ∀ X, (TV.obj X).PreservesZeroMorphisms}
    {_ : TW.PreservesZeroMorphisms} {_ : ∀ X, (TW.obj X).PreservesZeroMorphisms}
    {_ : TW'.PreservesZeroMorphisms} {_ : ∀ X, (TW'.obj X).PreservesZeroMorphisms}
    {_ : TV'.PreservesZeroMorphisms} {_ : ∀ X, (TV'.obj X).PreservesZeroMorphisms}
    {P N : HomologicalComplex V c}
    [HomologicalComplex.HasMapBifunctor P N TV c]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex c).obj P)
      ((G.mapHomologicalComplex c).obj N) TW c]
    [HomologicalComplex.HasMapBifunctor
      ((pb.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj P))
      ((pb.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj N)) TW' c]
    [HomologicalComplex.HasMapBifunctor ((ext.mapHomologicalComplex c).obj P)
      ((ext.mapHomologicalComplex c).obj N) TV' c]
    [HomologicalComplex.HasMapBifunctor
      ((G'.mapHomologicalComplex c).obj ((ext.mapHomologicalComplex c).obj P))
      ((G'.mapHomologicalComplex c).obj ((ext.mapHomologicalComplex c).obj N)) TW' c]
    (r : G ⋙ pb ≅ ext ⋙ G')
    (τ : ∀ a b, G.obj ((TV.obj a).obj b) ≅ (TW.obj (G.obj a)).obj (G.obj b))
    (σ : ∀ x y, pb.obj ((TW.obj x).obj y) ≅ (TW'.obj (pb.obj x)).obj (pb.obj y))
    (τ' : ∀ a b, G'.obj ((TV'.obj a).obj b) ≅ (TW'.obj (G'.obj a)).obj (G'.obj b))
    (δ₀ : ∀ a b, ext.obj ((TV.obj a).obj b) ⟶ (TV'.obj (ext.obj a)).obj (ext.obj b))
    (z : ∀ a b, (TV'.obj (ext.obj a)).obj (ext.obj b) ⟶ (TV'.obj (ext.obj a)).obj (ext.obj b))
    (t : (G.mapHomologicalComplex c).obj (HomologicalComplex.mapBifunctor P N TV c) ≅
      HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex c).obj P)
        ((G.mapHomologicalComplex c).obj N) TW c)
    (ht : ∀ p q n h, G.map (HomologicalComplex.ιMapBifunctor P N TV c p q n h) ≫ t.hom.f n =
      (τ (P.X p) (N.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex c).obj P)
        ((G.mapHomologicalComplex c).obj N) TW c p q n h)
    (Θ : (pb.mapHomologicalComplex c).obj (HomologicalComplex.mapBifunctor
        ((G.mapHomologicalComplex c).obj P) ((G.mapHomologicalComplex c).obj N) TW c) ≅
      HomologicalComplex.mapBifunctor
        ((pb.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj P))
        ((pb.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj N)) TW' c)
    (hΘ : ∀ p q n h, pb.map
      (HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex c).obj P)
        ((G.mapHomologicalComplex c).obj N) TW c p q n h) ≫ Θ.hom.f n =
      (σ (G.obj (P.X p)) (G.obj (N.X q))).hom ≫ HomologicalComplex.ιMapBifunctor
        ((pb.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj P))
        ((pb.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj N)) TW' c p q n h)
    (hext : ∀ n {A : W'} (u v : ((pb.mapHomologicalComplex c).obj
        (HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex c).obj P)
          ((G.mapHomologicalComplex c).obj N) TW c)).X n ⟶ A),
      (∀ p q h, pb.map
        (HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex c).obj P)
          ((G.mapHomologicalComplex c).obj N) TW c p q n h) ≫ u =
        pb.map
          (HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex c).obj P)
            ((G.mapHomologicalComplex c).obj N) TW c p q n h) ≫ v) → u = v)
    (t' : (G'.mapHomologicalComplex c).obj (HomologicalComplex.mapBifunctor
        ((ext.mapHomologicalComplex c).obj P) ((ext.mapHomologicalComplex c).obj N) TV' c) ≅
      HomologicalComplex.mapBifunctor
        ((G'.mapHomologicalComplex c).obj ((ext.mapHomologicalComplex c).obj P))
        ((G'.mapHomologicalComplex c).obj ((ext.mapHomologicalComplex c).obj N)) TW' c)
    (ht' : ∀ p q n h, G'.map
      (HomologicalComplex.ιMapBifunctor ((ext.mapHomologicalComplex c).obj P)
        ((ext.mapHomologicalComplex c).obj N) TV' c p q n h) ≫
        t'.hom.f n = (τ' (ext.obj (P.X p)) (ext.obj (N.X q))).hom ≫ HomologicalComplex.ιMapBifunctor
        ((G'.mapHomologicalComplex c).obj ((ext.mapHomologicalComplex c).obj P))
        ((G'.mapHomologicalComplex c).obj ((ext.mapHomologicalComplex c).obj N)) TW' c p q n h)
    (μ : HomologicalComplex.mapBifunctor ((ext.mapHomologicalComplex c).obj P)
        ((ext.mapHomologicalComplex c).obj N) TV' c ≅
      (ext.mapHomologicalComplex c).obj (HomologicalComplex.mapBifunctor P N TV c))
    (hμ : ∀ p q n h, ext.map (HomologicalComplex.ιMapBifunctor P N TV c p q n h) ≫ μ.inv.f n =
      δ₀ (P.X p) (N.X q) ≫ HomologicalComplex.ιMapBifunctor
        ((ext.mapHomologicalComplex c).obj P) ((ext.mapHomologicalComplex c).obj N) TV' c p q n h)
    (Z : HomologicalComplex.mapBifunctor ((ext.mapHomologicalComplex c).obj P)
        ((ext.mapHomologicalComplex c).obj N) TV' c ⟶
      HomologicalComplex.mapBifunctor ((ext.mapHomologicalComplex c).obj P)
        ((ext.mapHomologicalComplex c).obj N) TV' c)
    (hZ : ∀ p q n h, HomologicalComplex.ιMapBifunctor ((ext.mapHomologicalComplex c).obj P)
      ((ext.mapHomologicalComplex c).obj N) TV' c p q n h ≫ Z.f n =
      z (P.X p) (N.X q) ≫ HomologicalComplex.ιMapBifunctor
        ((ext.mapHomologicalComplex c).obj P) ((ext.mapHomologicalComplex c).obj N) TV' c p q n h)
    (hmod : ∀ a b, pb.map (τ a b).hom ≫ (σ (G.obj a) (G.obj b)).hom ≫
        ((TW'.map (r.hom.app a)).app (pb.obj (G.obj b)) ≫
          (TW'.obj (G'.obj (ext.obj a))).map (r.hom.app b)) ≫ (τ' (ext.obj a) (ext.obj b)).inv =
      (r.hom.app ((TV.obj a).obj b) ≫ G'.map (δ₀ a b)) ≫ G'.map (z a b)) :
    ((pb.mapHomologicalComplex c).map t.hom ≫ Θ.hom) ≫
        (HomologicalComplex.mapBifunctorMap
          (K₁ := (pb.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj P))
          (L₁ := (G'.mapHomologicalComplex c).obj ((ext.mapHomologicalComplex c).obj P))
          (K₂ := (pb.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj N))
          (L₂ := (G'.mapHomologicalComplex c).obj ((ext.mapHomologicalComplex c).obj N))
          ((Functor.mapHomologicalComplexCompIso r c ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ G')) c).symm).hom.app P)
          ((Functor.mapHomologicalComplexCompIso r c ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ G')) c).symm).hom.app N)
          TW' c ≫ t'.inv) =
      (Functor.mapHomologicalComplexCompIso r c ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ G')) c).symm).hom.app
          (HomologicalComplex.mapBifunctor P N TV c) ≫
        (G'.mapHomologicalComplex c).map μ.inv ≫ (G'.mapHomologicalComplex c).map Z := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  -- reduce to the summands of `pb(Tot_W(G P, G N))`
  have hcancel : ∀ {A : W'} (u v : ((pb.mapHomologicalComplex c).obj
      ((G.mapHomologicalComplex c).obj (HomologicalComplex.mapBifunctor P N TV c))).X n ⟶ A),
      (∀ p q h, pb.map (G.map (HomologicalComplex.ιMapBifunctor P N TV c p q n h)) ≫ u =
        pb.map (G.map (HomologicalComplex.ιMapBifunctor P N TV c p q n h)) ≫ v) → u = v := by
    intro A u v huv
    refine (cancel_epi (pb.map (t.inv.f n))).1 ?_
    refine hext n _ _ (fun p q h => ?_)
    have hinv := comp_inv_f_of_comp_hom_f t n (τ (P.X p) (N.X q)) _ _ (ht p q n h)
    rw [← Category.assoc, ← Functor.map_comp, hinv, Functor.map_comp, Category.assoc,
      huv p q h, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      ← hinv]
  refine hcancel _ _ (fun p q h => ?_)
  have hinv' := comp_inv_f_of_comp_hom_f t' n (τ' (ext.obj (P.X p)) (ext.obj (N.X q))) _ _
    (ht' p q n h)
  have h2 : ∀ (K : HomologicalComplex V c) (i : ι),
      ((Functor.mapHomologicalComplexCompIso r c ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ G')) c).symm).hom.app K).f i =
        r.hom.app (K.X i) := fun K i => by
    simp [Functor.mapHomologicalComplexCompIso]
  have hr : pb.map (G.map (HomologicalComplex.ιMapBifunctor P N TV c p q n h)) ≫
      r.hom.app ((HomologicalComplex.mapBifunctor P N TV c).X n) =
      r.hom.app ((TV.obj (P.X p)).obj (N.X q)) ≫
        G'.map (ext.map (HomologicalComplex.ιMapBifunctor P N TV c p q n h)) :=
    r.hom.naturality _
  have e1 : pb.map (G.map (HomologicalComplex.ιMapBifunctor P N TV c p q n h)) ≫
      (((pb.mapHomologicalComplex c).map t.hom ≫ Θ.hom) ≫
        (HomologicalComplex.mapBifunctorMap
          (K₁ := (pb.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj P))
          (L₁ := (G'.mapHomologicalComplex c).obj ((ext.mapHomologicalComplex c).obj P))
          (K₂ := (pb.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj N))
          (L₂ := (G'.mapHomologicalComplex c).obj ((ext.mapHomologicalComplex c).obj N))
          ((Functor.mapHomologicalComplexCompIso r c ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ G')) c).symm).hom.app P)
          ((Functor.mapHomologicalComplexCompIso r c ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ G')) c).symm).hom.app N)
          TW' c ≫ t'.inv)).f n =
      (pb.map (τ (P.X p) (N.X q)).hom ≫ (σ (G.obj (P.X p)) (G.obj (N.X q))).hom ≫
        ((TW'.map (r.hom.app (P.X p))).app (pb.obj (G.obj (N.X q))) ≫
          (TW'.obj (G'.obj (ext.obj (P.X p)))).map (r.hom.app (N.X q))) ≫
        (τ' (ext.obj (P.X p)) (ext.obj (N.X q))).inv) ≫
        G'.map
          (HomologicalComplex.ιMapBifunctor ((ext.mapHomologicalComplex c).obj P)
            ((ext.mapHomologicalComplex c).obj N) TV' c p q n h) := by
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [show ((pb.mapHomologicalComplex c).map t.hom).f n = pb.map (t.hom.f n) from rfl,
      ← Category.assoc, ← Functor.map_comp, ht, Functor.map_comp, Category.assoc,
      reassoc_of% (hΘ p q n h), HomologicalComplex.ι_mapBifunctorMap_assoc, h2, h2, hinv']
    simp only [Functor.mapHomologicalComplex_obj_X]
  have e2 : pb.map (G.map (HomologicalComplex.ιMapBifunctor P N TV c p q n h)) ≫
      ((Functor.mapHomologicalComplexCompIso r c ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ G')) c).symm).hom.app
          (HomologicalComplex.mapBifunctor P N TV c) ≫
        (G'.mapHomologicalComplex c).map μ.inv ≫ (G'.mapHomologicalComplex c).map Z).f n =
      ((r.hom.app ((TV.obj (P.X p)).obj (N.X q)) ≫ G'.map (δ₀ (P.X p) (N.X q))) ≫
        G'.map (z (P.X p) (N.X q))) ≫
        G'.map
          (HomologicalComplex.ιMapBifunctor ((ext.mapHomologicalComplex c).obj P)
            ((ext.mapHomologicalComplex c).obj N) TV' c p q n h) := by
    simp only [HomologicalComplex.comp_f]
    rw [h2, show ((G'.mapHomologicalComplex c).map μ.inv).f n = G'.map (μ.inv.f n) from rfl,
      show ((G'.mapHomologicalComplex c).map Z).f n = G'.map (Z.f n) from rfl,
      reassoc_of% hr, ← G'.map_comp, ← G'.map_comp, reassoc_of% (hμ p q n h), hZ]
    simp only [Functor.map_comp, Category.assoc]
  rw [e1, e2, hmod]

/-- Precomposition with a map commutes with the scalar multiple of the identity of a complex,
degreewise. -/
theorem comp_smul_id_f {R : Type*} [Semiring R] {ι : Type*} {c : ComplexShape ι}
    {C : Type*} {_ : Category C} {_ : Preadditive C} {_ : Linear R C}
    {K : HomologicalComplex C c} {Y : C} (n : ι) (f : Y ⟶ K.X n) (r : R) :
    f ≫ (r • 𝟙 K).f n = (r • 𝟙 Y) ≫ f := by
  rw [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, Linear.comp_smul,
    Linear.smul_comp, Category.comp_id, Category.id_comp]

/-- An `R`-linear endomorphism `c • 𝟙` of `R` that is an isomorphism has `c` a unit. -/
theorem isUnit_of_isIso_smul_id {R : Type*} [CommRing R] (c : R)
    [IsIso (c • 𝟙 (ModuleCat.of R R))] : IsUnit c := by
  have h := congrArg (fun g => ModuleCat.Hom.hom g (1 : R))
    (IsIso.inv_hom_id (c • 𝟙 (ModuleCat.of R R)))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at h
  exact isUnit_iff_exists_inv.mpr ⟨_, h⟩

/-- If `c • 𝟙 X` is an isomorphism for an `R`-module `X ≅ R`, then `c` is a unit. -/
theorem isUnit_of_isIso_smul_id_of_iso {R : Type*} [CommRing R] {X : ModuleCat R}
    (e : X ≅ ModuleCat.of R R) (c : R) (h : IsIso (c • 𝟙 X)) : IsUnit c := by
  have : IsIso (c • 𝟙 (ModuleCat.of R R)) := by
    have he : e.inv ≫ (c • 𝟙 X) ≫ e.hom = c • 𝟙 _ := by
      rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, e.inv_hom_id]
    rw [← he]
    infer_instance
  exact isUnit_of_isIso_smul_id c

end Stacks.Generic

namespace Stacks.Sheaves.DerivedPullback

universe v u' w v' u'' w' uV uV' vV vV' uA

section Chain

variable {X : AlgebraicGeometry.RingedTopos.{v, u', w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u'', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : AlgebraicGeometry.RingedToposHom X Y)
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O)
      (ComplexShape.up ℤ)]

/-- The comparison `f^*Tot(P ⊗ N)' ⟶ Tot(P' ⊗ N')'` through Stacks 03EL on total complexes, for
functors `G : V ⥤ Mod(𝒪_Y)`, `G' : V' ⥤ Mod(𝒪_X)` with `r : G ⋙ f^* ≅ ext ⋙ G'`, and comparisons
`t`, `t'` of `G` and `G'` with the total tensor complexes. -/
def pullbackTensorTotalChain {V : Type uV} {V' : Type uV'} {_ : Category.{vV} V}
    {_ : Category.{vV'} V'} {_ : Preadditive V}
    {_ : Preadditive V'}
    {G : V ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))} {ext : V ⥤ V'}
    {G' : V' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    [G.Additive] [ext.Additive] [G'.Additive] [(ext ⋙ G').Additive]
    {TV : V ⥤ V ⥤ V} {TV' : V' ⥤ V' ⥤ V'}
    [TV.PreservesZeroMorphisms] [∀ X, (TV.obj X).PreservesZeroMorphisms]
    [TV'.PreservesZeroMorphisms] [∀ X, (TV'.obj X).PreservesZeroMorphisms]
    {P N : HomologicalComplex V (ComplexShape.up ℤ)}
    [HomologicalComplex.HasMapBifunctor P N TV (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ)]
    
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ ext ⋙ G')
    (t : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (HomologicalComplex.mapBifunctor P N TV (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
    (t' : (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (HomologicalComplex.mapBifunctor ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
        ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
  (((f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).map t.hom ≫
    (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso f.toModulesHom
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)).hom) ≫
    (HomologicalComplex.mapBifunctorMap
      (K₁ := (((f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
      (L₁ := ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
      (K₂ := (((f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)))
      (L₂ := ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)))
      ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ G'))
        (ComplexShape.up ℤ)).symm).hom.app P)
        ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ G'))
        (ComplexShape.up ℤ)).symm).hom.app N) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ) ≫ t'.inv)

/-- The comparison `f^*Tot(P ⊗ N)' ⟶ Tot(P' ⊗ N')'` through `r` on the total complex followed by
a comparison `μ` of total complexes. -/
def pullbackExtensionTotalChain {V : Type uV} {V' : Type uV'} {_ : Category.{vV} V}
    {_ : Category.{vV'} V'} {_ : Preadditive V}
    {_ : Preadditive V'}
    {G : V ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))} {ext : V ⥤ V'}
    {G' : V' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    [G.Additive] [ext.Additive] [G'.Additive] [(ext ⋙ G').Additive]
    {TV : V ⥤ V ⥤ V} {TV' : V' ⥤ V' ⥤ V'}
    [TV.PreservesZeroMorphisms] [∀ X, (TV.obj X).PreservesZeroMorphisms]
    [TV'.PreservesZeroMorphisms] [∀ X, (TV'.obj X).PreservesZeroMorphisms]
    {P N : HomologicalComplex V (ComplexShape.up ℤ)}
    [HomologicalComplex.HasMapBifunctor P N TV (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ)]
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ ext ⋙ G')
    (μ : HomologicalComplex.mapBifunctor ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ) ≅
      (ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor P N TV (ComplexShape.up ℤ))) :
    ((f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor P N TV (ComplexShape.up ℤ))) ⟶
      (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ)) :=
  (Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ G'))
        (ComplexShape.up ℤ)).symm).hom.app
        (HomologicalComplex.mapBifunctor P N TV (ComplexShape.up ℤ)) ≫
    (G'.mapHomologicalComplex (ComplexShape.up ℤ)).map μ.inv

/-- **The two comparisons of total complexes for the pullback along a morphism of ringed
topoi differ by `Z`**, as soon as the module-level comparison through Stacks 03EL is the one
through `δ₀` followed by `z`. -/
theorem pullbackTensorTotalChain_eq {V : Type uV} {V' : Type uV'} {_ : Category.{vV} V}
    {_ : Category.{vV'} V'} {_ : Preadditive V}
    {_ : Preadditive V'}
    {G : V ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))} {ext : V ⥤ V'}
    {G' : V' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    [G.Additive] [ext.Additive] [G'.Additive] [(ext ⋙ G').Additive]
    {TV : V ⥤ V ⥤ V} {TV' : V' ⥤ V' ⥤ V'}
    [TV.PreservesZeroMorphisms] [∀ X, (TV.obj X).PreservesZeroMorphisms]
    [TV'.PreservesZeroMorphisms] [∀ X, (TV'.obj X).PreservesZeroMorphisms]
    {P N : HomologicalComplex V (ComplexShape.up ℤ)}
    [HomologicalComplex.HasMapBifunctor P N TV (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ)]
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ ext ⋙ G')
    (τ : ∀ a b, G.obj ((TV.obj a).obj b) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj a)).obj (G.obj b))
    (τ' : ∀ a b, G'.obj ((TV'.obj a).obj b) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj a)).obj (G'.obj b))
    (δ₀ : ∀ a b, ext.obj ((TV.obj a).obj b) ⟶ (TV'.obj (ext.obj a)).obj (ext.obj b))
    (z : ∀ a b, (TV'.obj (ext.obj a)).obj (ext.obj b) ⟶ (TV'.obj (ext.obj a)).obj (ext.obj b))
    (t : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (HomologicalComplex.mapBifunctor P N TV (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
    (ht : ∀ p q n h, G.map (HomologicalComplex.ιMapBifunctor P N TV (ComplexShape.up ℤ) p q n h)
      ≫ t.hom.f n =
      (τ (P.X p) (N.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p q n h)
    (t' : (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (HomologicalComplex.mapBifunctor ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
        ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))
    (ht' : ∀ p q n h, G'.map
      (HomologicalComplex.ιMapBifunctor ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ) p q n h) ≫
        t'.hom.f n = (τ' (ext.obj (P.X p)) (ext.obj (N.X q))).hom ≫
          HomologicalComplex.ιMapBifunctor
            ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
            ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p q n h)
    (μ : HomologicalComplex.mapBifunctor ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ) ≅
      (ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor P N TV (ComplexShape.up ℤ)))
    (hμ : ∀ p q n h, ext.map
      (HomologicalComplex.ιMapBifunctor P N TV (ComplexShape.up ℤ) p q n h) ≫ μ.inv.f n =
      δ₀ (P.X p) (N.X q) ≫ HomologicalComplex.ιMapBifunctor
        ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ) p q n h)
    (Z : HomologicalComplex.mapBifunctor ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ) ⟶
      HomologicalComplex.mapBifunctor ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ))
    (hZ : ∀ p q n h, HomologicalComplex.ιMapBifunctor
      ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ)
      p q n h ≫ Z.f n =
      z (P.X p) (N.X q) ≫ HomologicalComplex.ιMapBifunctor
        ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TV' (ComplexShape.up ℤ) p q n h)
    (hmod : ∀ a b, (f.toModulesHom.pullbackModules).map (τ a b).hom ≫
        (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (G.obj a, G.obj b) ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (r.hom.app a)).app
          ((f.toModulesHom.pullbackModules).obj (G.obj b)) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj (ext.obj a))).map
            (r.hom.app b)) ≫
        (τ' (ext.obj a) (ext.obj b)).inv =
      (r.hom.app ((TV.obj a).obj b) ≫ G'.map (δ₀ a b)) ≫ G'.map (z a b)) :
    pullbackTensorTotalChain f r t t' =
      pullbackExtensionTotalChain f r μ ≫ (G'.mapHomologicalComplex (ComplexShape.up ℤ)).map Z :=
  Stacks.Generic.pullbackTensorChain_eq (c := (ComplexShape.up ℤ)) (G := G)
    (pb := (f.toModulesHom.pullbackModules)) (ext := ext) (G' := G')
    (TV := TV) (TW := (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))
    (TW' := (Stacks.SheafOfModules.Tensor.sheafTensor X.O)) (TV' := TV') (P := P) (N := N) r τ
    (fun x y => (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).app (x, y)) τ' δ₀ z t ht
    (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso f.toModulesHom
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    (fun p q n h => Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_hom f.toModulesHom
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) p q n h)
    (fun n _ _ _ h => Stacks.Sheaves.DerivedPullback.hom_ext_pullbackTotal f.toModulesHom
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) n h)
    t' ht' μ hμ Z hZ hmod

section Module

/-- `f^*(M ⊗ N)' ≅ f^*M' ⊗ f^*N' ≅ (A' ⊗ M)'' ⊗ (A' ⊗ N)'' ≅ ((A' ⊗ M) ⊗ (A' ⊗ N))''`, through
Stacks 03EL, for `G : Mod(A) ⥤ Mod(𝒪_Y)` and `G' : Mod(A') ⥤ Mod(𝒪_X)` with comparisons `τ`, `τ'`
with the tensor products and `r : G ⋙ f^* ≅ (A' ⊗_A -) ⋙ G'`. -/
def pullbackTensorModuleHom {A A' : Type uA} [CommRing A] [CommRing A'] (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (τ : ∀ M N : ModuleCat.{uA} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (τ' : ∀ M N : ModuleCat.{uA} A', G'.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (M N : ModuleCat.{uA} A) :
    (f.toModulesHom.pullbackModules).obj (G.obj (M ⊗ N)) ⟶
      G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M ⊗
        (ModuleCat.extendScalars.{uA, uA, uA} φ).obj N) :=
  (f.toModulesHom.pullbackModules).map (τ M N).hom ≫
    (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (G.obj M, G.obj N) ≫
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (r.hom.app M)).app
      ((f.toModulesHom.pullbackModules).obj (G.obj N)) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
        (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M))).map (r.hom.app N)) ≫
    (τ' ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M)
      ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj N)).inv

/-- `f^*(M ⊗ N)' ≅ (A' ⊗ (M ⊗ N))'' ≅ ((A' ⊗ M) ⊗ (A' ⊗ N))''`, through the extension of scalars
of the tensor product. -/
def pullbackExtensionModuleHom {A A' : Type uA} [CommRing A] [CommRing A'] (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (M N : ModuleCat.{uA} A) :
    (f.toModulesHom.pullbackModules).obj (G.obj (M ⊗ N)) ⟶
      G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M ⊗
        (ModuleCat.extendScalars.{uA, uA, uA} φ).obj N) :=
  r.hom.app (M ⊗ N) ≫ G'.map (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars.{uA, uA, uA} φ) M N)

/-- The comparison `pullbackExtensionModuleHom f φ r M N` is an isomorphism. -/
instance isIso_pullbackExtensionModuleHom {A A' : Type uA} [CommRing A] [CommRing A'] (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (M N : ModuleCat.{uA} A) :
    IsIso (pullbackExtensionModuleHom f φ r M N) := by
  unfold pullbackExtensionModuleHom
  infer_instance

/-- The comparison `pullbackTensorModuleHom f φ r τ τ' M N` is an isomorphism. -/
instance isIso_pullbackTensorModuleHom {A A' : Type uA} [CommRing A] [CommRing A'] (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (τ : ∀ M N : ModuleCat.{uA} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (τ' : ∀ M N : ModuleCat.{uA} A', G'.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (M N : ModuleCat.{uA} A) :
    IsIso (pullbackTensorModuleHom f φ r τ τ' M N) :=
  ((f.toModulesHom.pullbackModules).mapIso (τ M N) ≪≫
    (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).app (G.obj M, G.obj N) ≪≫
    ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).mapIso (r.app M)).app
        ((f.toModulesHom.pullbackModules).obj (G.obj N))) ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
        (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M))).mapIso (r.app N)) ≪≫
    (τ' ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M)
      ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj N)).symm).isIso_hom

omit [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).Additive]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).obj M).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O) (ComplexShape.up ℤ)] in
/-- `pullbackExtensionModuleHom f φ r M N` is natural in `N`. -/
theorem pullbackExtensionModuleHom_naturality_right {A A' : Type uA} [CommRing A] [CommRing A']
    (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (M : ModuleCat.{uA} A) {N N' : ModuleCat.{uA} A} (g : N ⟶ N') :
    (f.toModulesHom.pullbackModules).map (G.map (M ◁ g)) ≫ pullbackExtensionModuleHom f φ r M N' =
      pullbackExtensionModuleHom f φ r M N ≫
        G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M ◁
          (ModuleCat.extendScalars.{uA, uA, uA} φ).map g) := by
  unfold pullbackExtensionModuleHom
  rw [← Category.assoc, show (f.toModulesHom.pullbackModules).map (G.map (M ◁ g)) ≫
    r.hom.app (M ⊗ N') =
      r.hom.app (M ⊗ N) ≫ G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).map (M ◁ g)) from
        r.hom.naturality (M ◁ g),
    Category.assoc, Category.assoc, ← G'.map_comp, ← G'.map_comp,
    Functor.OplaxMonoidal.δ_natural_right]

omit [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).Additive]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).obj M).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O) (ComplexShape.up ℤ)] in
/-- `pullbackExtensionModuleHom f φ r M N` is natural in `M`. -/
theorem pullbackExtensionModuleHom_naturality_left {A A' : Type uA} [CommRing A] [CommRing A']
    (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    {M M' : ModuleCat.{uA} A} (g : M ⟶ M') (N : ModuleCat.{uA} A) :
    (f.toModulesHom.pullbackModules).map (G.map (g ▷ N)) ≫ pullbackExtensionModuleHom f φ r M' N =
      pullbackExtensionModuleHom f φ r M N ≫
        G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g ▷
          (ModuleCat.extendScalars.{uA, uA, uA} φ).obj N) := by
  unfold pullbackExtensionModuleHom
  rw [← Category.assoc, show (f.toModulesHom.pullbackModules).map (G.map (g ▷ N)) ≫
    r.hom.app (M' ⊗ N) =
      r.hom.app (M ⊗ N) ≫ G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).map (g ▷ N)) from
        r.hom.naturality (g ▷ N),
    Category.assoc, Category.assoc, ← G'.map_comp, ← G'.map_comp,
    Functor.OplaxMonoidal.δ_natural_left]

omit [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).obj M).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O) (ComplexShape.up ℤ)] in
/-- `pullbackTensorModuleHom f φ r τ τ' M N` is natural in `N`, provided `τ` and `τ'` are natural
in the second variable. -/
theorem pullbackTensorModuleHom_naturality_right {A A' : Type uA} [CommRing A] [CommRing A']
    (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (τ : ∀ M N : ModuleCat.{uA} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (hτ : ∀ (M : ModuleCat.{uA} A) {N N' : ModuleCat.{uA} A} (g : N ⟶ N'),
      G.map (M ◁ g) ≫ (τ M N').hom = (τ M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).map (G.map g))
    (τ' : ∀ M N : ModuleCat.{uA} A', G'.obj (M ⊗ N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (hτ' : ∀ (M : ModuleCat.{uA} A') {N N' : ModuleCat.{uA} A'} (g : N ⟶ N'),
      G'.map (M ◁ g) ≫ (τ' M N').hom = (τ' M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).map (G'.map g))
    (M : ModuleCat.{uA} A) {N N' : ModuleCat.{uA} A} (g : N ⟶ N') :
    (f.toModulesHom.pullbackModules).map (G.map (M ◁ g)) ≫ pullbackTensorModuleHom f φ r τ τ' M N' =
      pullbackTensorModuleHom f φ r τ τ' M N ≫
        G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M ◁
          (ModuleCat.extendScalars.{uA, uA, uA} φ).map g) := by
  have s₁ : (f.toModulesHom.pullbackModules).map (G.map (M ◁ g)) ≫
      (f.toModulesHom.pullbackModules).map (τ M N').hom =
      (f.toModulesHom.pullbackModules).map (τ M N).hom ≫
        (f.toModulesHom.pullbackModules).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).map (G.map g)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hτ]
  have s₂ := Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_snd f.toModulesHom
    (G.obj M) (G.map g)
  have s₃ : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
      ((f.toModulesHom.pullbackModules).obj (G.obj M))).map
      ((f.toModulesHom.pullbackModules).map (G.map g)) ≫
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (r.hom.app M)).app
        ((f.toModulesHom.pullbackModules).obj (G.obj N')) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M))).map (r.hom.app N')) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (r.hom.app M)).app
        ((f.toModulesHom.pullbackModules).obj (G.obj N)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M))).map (r.hom.app N)) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
        (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M))).map
        (G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g)) := by
    have hr : (f.toModulesHom.pullbackModules).map (G.map g) ≫ r.hom.app N' = r.hom.app N ≫
        G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g) :=
      r.hom.naturality g
    calc ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
           ((f.toModulesHom.pullbackModules).obj (G.obj M))).map
           ((f.toModulesHom.pullbackModules).map (G.map g)) ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (r.hom.app M)).app
            ((f.toModulesHom.pullbackModules).obj (G.obj N')) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M))).map (r.hom.app N'))
        = ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (r.hom.app M)).app
          ((f.toModulesHom.pullbackModules).obj (G.obj N)) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M))).map
              ((f.toModulesHom.pullbackModules).map (G.map g)) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M))).map (r.hom.app N') := by
          rw [← Category.assoc, NatTrans.naturality, Category.assoc]; rfl
      _ = ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (r.hom.app M)).app
        ((f.toModulesHom.pullbackModules).obj (G.obj N)) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M))).map (r.hom.app N) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M))).map
              (G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g)) := by
          rw [← Functor.map_comp, hr, Functor.map_comp]
      _ = _ := (Category.assoc _ _ _).symm
  have s₄ := AlgebraicGeometry.Space.square_inv _ _ _ _
    (hτ' ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M)
      ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g))
  unfold pullbackTensorModuleHom
  exact AlgebraicGeometry.Space.paste_four_squares _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂ s₃ s₄

omit [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).obj M).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O) (ComplexShape.up ℤ)] in
/-- `pullbackTensorModuleHom f φ r τ τ' M N` is natural in `M`, provided `τ` and `τ'` are natural
in the first variable. -/
theorem pullbackTensorModuleHom_naturality_left {A A' : Type uA} [CommRing A] [CommRing A']
    (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (τ : ∀ M N : ModuleCat.{uA} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (hτ : ∀ {M M' : ModuleCat.{uA} A} (g : M ⟶ M') (N : ModuleCat.{uA} A),
      G.map (g ▷ N) ≫ (τ M' N).hom = (τ M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map (G.map g)).app (G.obj N)))
    (τ' : ∀ M N : ModuleCat.{uA} A', G'.obj (M ⊗ N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (hτ' : ∀ {M M' : ModuleCat.{uA} A'} (g : M ⟶ M') (N : ModuleCat.{uA} A'),
      G'.map (g ▷ N) ≫ (τ' M' N).hom = (τ' M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (G'.map g)).app (G'.obj N)))
    {M M' : ModuleCat.{uA} A} (g : M ⟶ M') (N : ModuleCat.{uA} A) :
    (f.toModulesHom.pullbackModules).map (G.map (g ▷ N)) ≫ pullbackTensorModuleHom f φ r τ τ' M' N =
      pullbackTensorModuleHom f φ r τ τ' M N ≫
        G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g ▷
          (ModuleCat.extendScalars.{uA, uA, uA} φ).obj N) := by
  have s₁ : (f.toModulesHom.pullbackModules).map (G.map (g ▷ N)) ≫
      (f.toModulesHom.pullbackModules).map (τ M' N).hom =
      (f.toModulesHom.pullbackModules).map (τ M N).hom ≫
        (f.toModulesHom.pullbackModules).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map (G.map g)).app (G.obj N)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hτ]
  have s₂ := Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_fst f.toModulesHom
    (G.map g) (G.obj N)
  have s₃ : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
      ((f.toModulesHom.pullbackModules).map (G.map g))).app
      ((f.toModulesHom.pullbackModules).obj (G.obj N)) ≫
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (r.hom.app M')).app
        ((f.toModulesHom.pullbackModules).obj (G.obj N)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M'))).map (r.hom.app N)) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (r.hom.app M)).app
        ((f.toModulesHom.pullbackModules).obj (G.obj N)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M))).map (r.hom.app N)) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
        (G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g))).app
        (G'.obj ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj N)) := by
    rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp,
      show (f.toModulesHom.pullbackModules).map (G.map g) ≫ r.hom.app M' = r.hom.app M ≫
          G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g) from
        r.hom.naturality g, Functor.map_comp, NatTrans.comp_app, Category.assoc,
      Category.assoc]
    exact congrArg (_ ≫ ·) (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
      (G'.map ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g))).naturality (r.hom.app N)).symm
  have s₄ := AlgebraicGeometry.Space.square_inv _ _ _ _
    (hτ' ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g)
      ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj N))
  unfold pullbackTensorModuleHom
  exact AlgebraicGeometry.Space.paste_four_squares _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂ s₃ s₄

/-- The ratio of the two module-level comparisons, as an endomorphism of `(A' ⊗ M) ⊗ (A' ⊗ N)`. -/
def pullbackTensorModuleRatio {A A' : Type uA} [CommRing A] [CommRing A'] (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (τ : ∀ M N : ModuleCat.{uA} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (τ' : ∀ M N : ModuleCat.{uA} A', G'.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (hG' : G'.FullyFaithful) (M N : ModuleCat.{uA} A) :
    (ModuleCat.extendScalars.{uA, uA, uA} φ).obj M ⊗
    (ModuleCat.extendScalars.{uA, uA, uA} φ).obj N ⟶
    (ModuleCat.extendScalars.{uA, uA, uA} φ).obj M ⊗
    (ModuleCat.extendScalars.{uA, uA, uA} φ).obj N :=
  hG'.preimage (inv (pullbackExtensionModuleHom f φ r M N) ≫ pullbackTensorModuleHom f φ r τ τ' M N)

omit [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).obj M).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O) (ComplexShape.up ℤ)] in
/-- The image of `pullbackTensorModuleRatio` under `G'` is
`inv (pullbackExtensionModuleHom f φ r M N) ≫ pullbackTensorModuleHom f φ r τ τ' M N`. -/
theorem map_pullbackTensorModuleRatio {A A' : Type uA} [CommRing A] [CommRing A'] (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (τ : ∀ M N : ModuleCat.{uA} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (τ' : ∀ M N : ModuleCat.{uA} A', G'.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (hG' : G'.FullyFaithful) (M N : ModuleCat.{uA} A) :
    G'.map (pullbackTensorModuleRatio f φ r τ τ' hG' M N) =
      inv (pullbackExtensionModuleHom f φ r M N) ≫ pullbackTensorModuleHom f φ r τ τ' M N :=
  hG'.map_preimage _

omit [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).obj M).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O) (ComplexShape.up ℤ)] in
/-- `pullbackTensorModuleRatio f φ r τ τ' hG' M N` is natural in `N`. -/
theorem pullbackTensorModuleRatio_naturality_right {A A' : Type uA} [CommRing A] [CommRing A']
    (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (τ : ∀ M N : ModuleCat.{uA} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (hτr : ∀ (M : ModuleCat.{uA} A) {N N' : ModuleCat.{uA} A} (g : N ⟶ N'),
      G.map (M ◁ g) ≫ (τ M N').hom = (τ M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).map (G.map g))
    (_hτl : ∀ {M M' : ModuleCat.{uA} A} (g : M ⟶ M') (N : ModuleCat.{uA} A),
      G.map (g ▷ N) ≫ (τ M' N).hom = (τ M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map (G.map g)).app (G.obj N)))
    (τ' : ∀ M N : ModuleCat.{uA} A', G'.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (hτr' : ∀ (M : ModuleCat.{uA} A') {N N' : ModuleCat.{uA} A'} (g : N ⟶ N'),
      G'.map (M ◁ g) ≫ (τ' M N').hom = (τ' M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).map (G'.map g))
    (_hτl' : ∀ {M M' : ModuleCat.{uA} A'} (g : M ⟶ M') (N : ModuleCat.{uA} A'),
      G'.map (g ▷ N) ≫ (τ' M' N).hom = (τ' M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (G'.map g)).app (G'.obj N)))
    (hG' : G'.FullyFaithful)
    (M : ModuleCat.{uA} A) {N N' : ModuleCat.{uA} A} (g : N ⟶ N') :
    ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M ◁
      (ModuleCat.extendScalars.{uA, uA, uA} φ).map g) ≫
      pullbackTensorModuleRatio f φ r τ τ' hG' M N' =
      pullbackTensorModuleRatio f φ r τ τ' hG' M N ≫
        ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj M ◁
          (ModuleCat.extendScalars.{uA, uA, uA} φ).map g) :=
  hG'.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, map_pullbackTensorModuleRatio,
      map_pullbackTensorModuleRatio]
    exact AlgebraicGeometry.Space.inv_comp_naturality _ _ _ _ _ _
      (pullbackExtensionModuleHom_naturality_right f φ r M g)
      (pullbackTensorModuleHom_naturality_right f φ r τ hτr τ' hτr' M g))

omit [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).obj M).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O) (ComplexShape.up ℤ)] in
/-- `pullbackTensorModuleRatio f φ r τ τ' hG' M N` is natural in `M`. -/
theorem pullbackTensorModuleRatio_naturality_left {A A' : Type uA} [CommRing A] [CommRing A']
    (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (τ : ∀ M N : ModuleCat.{uA} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (_hτr : ∀ (M : ModuleCat.{uA} A) {N N' : ModuleCat.{uA} A} (g : N ⟶ N'),
      G.map (M ◁ g) ≫ (τ M N').hom = (τ M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).map (G.map g))
    (hτl : ∀ {M M' : ModuleCat.{uA} A} (g : M ⟶ M') (N : ModuleCat.{uA} A),
      G.map (g ▷ N) ≫ (τ M' N).hom = (τ M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map (G.map g)).app (G.obj N)))
    (τ' : ∀ M N : ModuleCat.{uA} A', G'.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (_hτr' : ∀ (M : ModuleCat.{uA} A') {N N' : ModuleCat.{uA} A'} (g : N ⟶ N'),
      G'.map (M ◁ g) ≫ (τ' M N').hom = (τ' M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).map (G'.map g))
    (hτl' : ∀ {M M' : ModuleCat.{uA} A'} (g : M ⟶ M') (N : ModuleCat.{uA} A'),
      G'.map (g ▷ N) ≫ (τ' M' N).hom = (τ' M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (G'.map g)).app (G'.obj N)))
    (hG' : G'.FullyFaithful)
    {M M' : ModuleCat.{uA} A} (g : M ⟶ M') (N : ModuleCat.{uA} A) :
    ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g ▷
      (ModuleCat.extendScalars.{uA, uA, uA} φ).obj N) ≫
      pullbackTensorModuleRatio f φ r τ τ' hG' M' N =
      pullbackTensorModuleRatio f φ r τ τ' hG' M N ≫
        ((ModuleCat.extendScalars.{uA, uA, uA} φ).map g ▷
          (ModuleCat.extendScalars.{uA, uA, uA} φ).obj N) :=
  hG'.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, map_pullbackTensorModuleRatio,
      map_pullbackTensorModuleRatio]
    exact AlgebraicGeometry.Space.inv_comp_naturality _ _ _ _ _ _
      (pullbackExtensionModuleHom_naturality_left f φ r g N)
      (pullbackTensorModuleHom_naturality_left f φ r τ hτl τ' hτl' g N))

/-- The ratio, as a natural endomorphism of `(M, N) ↦ (A' ⊗ M) ⊗ (A' ⊗ N)`. -/
def pullbackTensorModuleRatioNatTrans {A A' : Type uA} [CommRing A] [CommRing A'] (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (τ : ∀ M N : ModuleCat.{uA} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (hτr : ∀ (M : ModuleCat.{uA} A) {N N' : ModuleCat.{uA} A} (g : N ⟶ N'),
      G.map (M ◁ g) ≫ (τ M N').hom = (τ M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).map (G.map g))
    (hτl : ∀ {M M' : ModuleCat.{uA} A} (g : M ⟶ M') (N : ModuleCat.{uA} A),
      G.map (g ▷ N) ≫ (τ M' N).hom = (τ M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map (G.map g)).app (G.obj N)))
    (τ' : ∀ M N : ModuleCat.{uA} A', G'.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (hτr' : ∀ (M : ModuleCat.{uA} A') {N N' : ModuleCat.{uA} A'} (g : N ⟶ N'),
      G'.map (M ◁ g) ≫ (τ' M N').hom = (τ' M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).map (G'.map g))
    (hτl' : ∀ {M M' : ModuleCat.{uA} A'} (g : M ⟶ M') (N : ModuleCat.{uA} A'),
      G'.map (g ▷ N) ≫ (τ' M' N).hom = (τ' M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (G'.map g)).app (G'.obj N)))
    (hG' : G'.FullyFaithful) :
    ModuleCat.ExtendScalars.tensorBifunctor φ ⟶ ModuleCat.ExtendScalars.tensorBifunctor φ where
  app M :=
    { app := fun N => pullbackTensorModuleRatio f φ r τ τ' hG' M N
      naturality := fun _ _ g =>
        pullbackTensorModuleRatio_naturality_right f φ r τ hτr hτl τ' hτr' hτl' hG' M g }
  naturality _ _ g := NatTrans.ext (funext fun N =>
    pullbackTensorModuleRatio_naturality_left f φ r τ hτr hτl τ' hτr' hτl' hG' g N)

omit [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O).obj M).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v, w, w, w} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u'', v', w', w', w'} Y.O) (ComplexShape.up ℤ)] in
/-- **The two module-level comparisons `f^*(M ⊗ N)' ≅ ((A' ⊗ M) ⊗ (A' ⊗ N))''` differ by a unit
of `A'`**, for `G'` fully faithful: a natural endomorphism of `(M, N) ↦ (A' ⊗ M) ⊗ (A' ⊗ N)` is a
scalar multiplication, by a unit since both comparisons are isomorphisms and
`(A' ⊗ A) ⊗ (A' ⊗ A) ≅ A'`. -/
theorem exists_pullbackTensorModuleHom_eq {A A' : Type uA} [CommRing A] [CommRing A'] (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (τ : ∀ M N : ModuleCat.{uA} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (hτr : ∀ (M : ModuleCat.{uA} A) {N N' : ModuleCat.{uA} A} (g : N ⟶ N'),
      G.map (M ◁ g) ≫ (τ M N').hom = (τ M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).map (G.map g))
    (hτl : ∀ {M M' : ModuleCat.{uA} A} (g : M ⟶ M') (N : ModuleCat.{uA} A),
      G.map (g ▷ N) ≫ (τ M' N).hom = (τ M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map (G.map g)).app (G.obj N)))
    (τ' : ∀ M N : ModuleCat.{uA} A', G'.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (hτr' : ∀ (M : ModuleCat.{uA} A') {N N' : ModuleCat.{uA} A'} (g : N ⟶ N'),
      G'.map (M ◁ g) ≫ (τ' M N').hom = (τ' M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).map (G'.map g))
    (hτl' : ∀ {M M' : ModuleCat.{uA} A'} (g : M ⟶ M') (N : ModuleCat.{uA} A'),
      G'.map (g ▷ N) ≫ (τ' M' N).hom = (τ' M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (G'.map g)).app (G'.obj N)))
    (hG' : G'.FullyFaithful) :
    ∃ c : A', IsUnit c ∧ ∀ M N : ModuleCat.{uA} A,
      pullbackTensorModuleHom f φ r τ τ' M N =
        pullbackExtensionModuleHom f φ r M N ≫ G'.map (c • 𝟙 _) := by
  obtain ⟨c, hc⟩ := ModuleCat.ExtendScalars.exists_bifunctor_app_eq_smul _
    (pullbackTensorModuleRatioNatTrans f φ r τ hτr hτl τ' hτr' hτl' hG')
  refine ⟨c, ?_, fun M N => ?_⟩
  · have hmap : IsIso
        (G'.map (c • 𝟙 ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj (𝟙_ (ModuleCat.{uA} A)) ⊗
        (ModuleCat.extendScalars.{uA, uA, uA} φ).obj (𝟙_ (ModuleCat.{uA} A))))) := by
      rw [← show pullbackTensorModuleRatio f φ r τ τ' hG' (𝟙_ _) (𝟙_ _) = c • 𝟙 _ from hc _ _,
        map_pullbackTensorModuleRatio]
      infer_instance
    exact Stacks.Generic.isUnit_of_isIso_smul_id_of_iso
      (MonoidalCategory.tensorIso
        (Functor.Monoidal.εIso (ModuleCat.extendScalars.{uA, uA, uA} φ)).symm
        (Functor.Monoidal.εIso (ModuleCat.extendScalars.{uA, uA, uA} φ)).symm ≪≫
          MonoidalCategory.leftUnitor (𝟙_ (ModuleCat.{uA} A'))) c (hG'.isIso_of_isIso_map _)
  have h := map_pullbackTensorModuleRatio f φ r τ τ' hG' M N
  rw [show pullbackTensorModuleRatio f φ r τ τ' hG' M N = c • 𝟙 _ from hc M N] at h
  rw [h, IsIso.hom_inv_id_assoc]

/-- **The two comparisons `f^*Tot(P ⊗_A N)' ≅ Tot((A' ⊗ P) ⊗_{A'} (A' ⊗ N))''` differ by a unit
of `A'`**, the same for all complexes `P`, `N` of `A`-modules: the one through Stacks 03EL on total
complexes and the one through the extension of scalars of the total complex. -/
theorem exists_pullbackTensorTotalChain_eq {A A' : Type uA} [CommRing A] [CommRing A']
    (φ : A →+* A')
    {G : ModuleCat.{uA} A ⥤ SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {G' : ModuleCat.{uA} A' ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    [G.Additive] [G'.Additive] [((ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G').Additive]
    (r : G ⋙ (f.toModulesHom.pullbackModules) ≅ (ModuleCat.extendScalars.{uA, uA, uA} φ) ⋙ G')
    (τ : ∀ M N : ModuleCat.{uA} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (hτr : ∀ (M : ModuleCat.{uA} A) {N N' : ModuleCat.{uA} A} (g : N ⟶ N'),
      G.map (M ◁ g) ≫ (τ M N').hom = (τ M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).map (G.map g))
    (hτl : ∀ {M M' : ModuleCat.{uA} A} (g : M ⟶ M') (N : ModuleCat.{uA} A),
      G.map (g ▷ N) ≫ (τ M' N).hom = (τ M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map (G.map g)).app (G.obj N)))
    (τ' : ∀ M N : ModuleCat.{uA} A', G'.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (hτr' : ∀ (M : ModuleCat.{uA} A') {N N' : ModuleCat.{uA} A'} (g : N ⟶ N'),
      G'.map (M ◁ g) ≫ (τ' M N').hom = (τ' M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).map (G'.map g))
    (hτl' : ∀ {M M' : ModuleCat.{uA} A'} (g : M ⟶ M') (N : ModuleCat.{uA} A'),
      G'.map (g ▷ N) ≫ (τ' M' N).hom = (τ' M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (G'.map g)).app (G'.obj N)))
    (hG' : G'.FullyFaithful)
    (t : ∀ P N : HomologicalComplex (ModuleCat.{uA} A) (ComplexShape.up ℤ),
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (HomologicalComplex.mapBifunctor P N (curriedTensor (ModuleCat.{uA} A)) (ComplexShape.up ℤ)) ≅
        HomologicalComplex.mapBifunctor
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
    (ht : ∀ P N : HomologicalComplex (ModuleCat.{uA} A) (ComplexShape.up ℤ), ∀ p q n h,
      G.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor (ModuleCat.{uA} A))
        (ComplexShape.up ℤ) p q n h) ≫ (t P N).hom.f n =
        (τ (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p q n h)
    (t' : ∀ P N : HomologicalComplex (ModuleCat.{uA} A) (ComplexShape.up ℤ),
      (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (HomologicalComplex.mapBifunctor
        (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (curriedTensor (ModuleCat.{uA} A')) (ComplexShape.up ℤ)) ≅
        HomologicalComplex.mapBifunctor
          ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P))
          ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj N)) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ))
    (ht' : ∀ P N : HomologicalComplex (ModuleCat.{uA} A) (ComplexShape.up ℤ), ∀ p q n h,
      G'.map (HomologicalComplex.ιMapBifunctor
        (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (curriedTensor (ModuleCat.{uA} A')) (ComplexShape.up ℤ) p q n h) ≫
        (t' P N).hom.f n =
          (τ' ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj (P.X p))
            ((ModuleCat.extendScalars.{uA, uA, uA} φ).obj (N.X q))).hom ≫
          HomologicalComplex.ιMapBifunctor
            ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P))
            ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj N)) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (ComplexShape.up ℤ) p q n h)
    (μ : ∀ P N : HomologicalComplex (ModuleCat.{uA} A) (ComplexShape.up ℤ),
      HomologicalComplex.mapBifunctor
      (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
      (curriedTensor (ModuleCat.{uA} A')) (ComplexShape.up ℤ) ≅
        ((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (HomologicalComplex.mapBifunctor P N (curriedTensor (ModuleCat.{uA} A))
          (ComplexShape.up ℤ)))
    (hμ : ∀ P N : HomologicalComplex (ModuleCat.{uA} A) (ComplexShape.up ℤ), ∀ p q n h,
      (ModuleCat.extendScalars.{uA, uA, uA} φ).map
      (HomologicalComplex.ιMapBifunctor P N (curriedTensor (ModuleCat.{uA} A))
        (ComplexShape.up ℤ) p q n h) ≫
        (μ P N).inv.f n = Functor.OplaxMonoidal.δ (ModuleCat.extendScalars.{uA, uA, uA} φ)
          (P.X p) (N.X q) ≫
          HomologicalComplex.ιMapBifunctor
            (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)
            (((ModuleCat.extendScalars.{uA, uA, uA} φ).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj N) (curriedTensor (ModuleCat.{uA} A'))
            (ComplexShape.up ℤ) p q n h) :
    ∃ c : A', IsUnit c ∧ ∀ P N : HomologicalComplex (ModuleCat.{uA} A) (ComplexShape.up ℤ),
      pullbackTensorTotalChain f r (t P N) (t' P N) =
        pullbackExtensionTotalChain f r (μ P N) ≫
          (G'.mapHomologicalComplex (ComplexShape.up ℤ)).map (c • 𝟙 _) := by
  obtain ⟨c, hcu, hc⟩ := exists_pullbackTensorModuleHom_eq f φ r τ hτr hτl τ' hτr' hτl' hG'
  refine ⟨c, hcu, fun P N => ?_⟩
  exact pullbackTensorTotalChain_eq f (G := G) (ext := (ModuleCat.extendScalars.{uA, uA, uA} φ))
    (G' := G') (TV := (curriedTensor (ModuleCat.{uA} A)))
    (TV' := (curriedTensor (ModuleCat.{uA} A'))) (P := P) (N := N) r τ τ'
    (fun a b => Functor.OplaxMonoidal.δ (ModuleCat.extendScalars.{uA, uA, uA} φ) a b)
    (fun _ _ => c • 𝟙 _) (t P N) (ht P N) (t' P N) (ht' P N) (μ P N) (hμ P N) (c • 𝟙 _)
    (fun p q n h => Stacks.Generic.comp_smul_id_f n _ c)
    (fun a b => by
      have h := hc a b
      unfold pullbackTensorModuleHom pullbackExtensionModuleHom at h
      exact h)

end Module

end Chain

end Stacks.Sheaves.DerivedPullback

namespace CochainComplex.ExtendScalars

/-- The inverse of the monoidality of degreewise extension of scalars, on summands. -/
theorem extendScalars_map_ι_extendScalarsMonoidalIso_inv {A A' : Type u} [CommRing A] [CommRing A']
    (φ : A →+* A') (P N : CochainComplex (ModuleCat.{u} A) ℤ) (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (ModuleCat.extendScalars.{u, u, u} φ).map
        (HomologicalComplex.ιMapBifunctor P N (curriedTensor (ModuleCat.{u} A))
          (ComplexShape.up ℤ) p q n h) ≫
      (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).inv.f n =
    Functor.OplaxMonoidal.δ (ModuleCat.extendScalars.{u, u, u} φ) (P.X p) (N.X q) ≫
      HomologicalComplex.ιMapBifunctor
        ((CochainComplex.ExtendScalars.mapCochainComplex φ).obj P)
        ((CochainComplex.ExtendScalars.mapCochainComplex φ).obj N)
        (curriedTensor (ModuleCat.{u} A')) (ComplexShape.up ℤ) p q n h := by
  have hh : HomologicalComplex.ιMapBifunctor
        ((CochainComplex.ExtendScalars.mapCochainComplex φ).obj P)
        ((CochainComplex.ExtendScalars.mapCochainComplex φ).obj N)
        (curriedTensor (ModuleCat.{u} A')) (ComplexShape.up ℤ) p q n h ≫
      (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).hom.f n =
      Functor.LaxMonoidal.μ (ModuleCat.extendScalars.{u, u, u} φ) (P.X p) (N.X q) ≫
        (ModuleCat.extendScalars.{u, u, u} φ).map
          (HomologicalComplex.ιMapBifunctor P N (curriedTensor (ModuleCat.{u} A))
            (ComplexShape.up ℤ) p q n h) :=
    CochainComplex.ExtendScalars.ι_extendScalarsMonoidalIso_hom φ P N n p q h
  calc (ModuleCat.extendScalars.{u, u, u} φ).map
        (HomologicalComplex.ιMapBifunctor P N (curriedTensor (ModuleCat.{u} A))
          (ComplexShape.up ℤ) p q n h) ≫
      (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).inv.f n
      = (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars.{u, u, u} φ) (P.X p) (N.X q) ≫
          Functor.LaxMonoidal.μ (ModuleCat.extendScalars.{u, u, u} φ) (P.X p) (N.X q) ≫
          (ModuleCat.extendScalars.{u, u, u} φ).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor (ModuleCat.{u} A))
              (ComplexShape.up ℤ) p q n h)) ≫
        (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).inv.f n := by
        rw [Functor.Monoidal.δ_μ_assoc]
    _ = _ := by
        rw [← hh, Category.assoc, Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
          HomologicalComplex.id_f]
        exact congrArg (_ ≫ ·) (Category.comp_id _)

end CochainComplex.ExtendScalars

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

attribute [local instance] additive_extendScalars_representedAffineRingHom
  additive_pullbackModules_representedSpaceMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g₀ : U' ⟶ U)

/-- The comparison `g^*Tot(P ⊗_A N)^~ ⟶ Tot((A' ⊗ P) ⊗_{A'} (A' ⊗ N))^~` through Stacks 03EL on
total complexes, for complexes `P`, `N` of `A`-modules. -/
def representedAffinePullbackTensorChain
    (P N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :=
  Stacks.Sheaves.DerivedPullback.pullbackTensorTotalChain
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g₀))
    (representedAffineToposPullbackIso B S hS g₀)
    (representedAffineToposTensorComplexIso B S hS U P N)
    (representedAffineToposTensorComplexIso B S hS U'
      (((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N))

/-- The comparison `g^*Tot(P ⊗_A N)^~ ⟶ Tot((A' ⊗ P) ⊗_{A'} (A' ⊗ N))^~` through the extension
of scalars of the total complex, for complexes `P`, `N` of `A`-modules. -/
def representedAffinePullbackExtensionChain
    (P N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :=
  Stacks.Sheaves.DerivedPullback.pullbackExtensionTotalChain
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g₀))
    (representedAffineToposPullbackIso B S hS g₀)
    (CochainComplex.ExtendScalars.extendScalarsMonoidalIso
      (representedAffineCommRingCatHom B S hS g₀).hom P N)

/-- **The two comparisons `g^*Tot(P ⊗_A N)^~ ≅ Tot((A' ⊗ P) ⊗_{A'} (A' ⊗ N))^~` differ by a
unit of `A'`**, the same for all complexes `P`, `N` of `A`-modules: the one through Stacks 03EL
on total complexes and the one through the extension of scalars of the total complex. -/
theorem exists_representedAffinePullbackTensorChain_eq :
    ∃ c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤), IsUnit c ∧
      ∀ P N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ,
      representedAffinePullbackTensorChain B S hS g₀ P N =
        representedAffinePullbackExtensionChain B S hS g₀ P N ≫
          ((representedAffineToposAssociated B S hS U').mapHomologicalComplex
            (ComplexShape.up ℤ)).map (c • 𝟙 _) :=
  Stacks.Sheaves.DerivedPullback.exists_pullbackTensorTotalChain_eq
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g₀))
    (representedAffineCommRingCatHom B S hS g₀).hom (G := representedAffineToposAssociated B S hS U)
    (G' := representedAffineToposAssociated B S hS U')
    (representedAffineToposPullbackIso B S hS g₀) (representedAffineToposTensorIso B S hS U)
    (fun M _ _ g => representedAffineToposTensorIso_hom_naturality_right B S hS U M g)
    (fun g N => representedAffineToposTensorIso_hom_naturality_left B S hS U g N)
    (representedAffineToposTensorIso B S hS U')
    (fun M _ _ g => representedAffineToposTensorIso_hom_naturality_right B S hS U' M g)
    (fun g N => representedAffineToposTensorIso_hom_naturality_left B S hS U' g N)
    (representedAffineToposAssociatedFullyFaithful B S hS U')
    (fun P N => representedAffineToposTensorComplexIso B S hS U P N)
    (fun _ _ p q n h => CategoryTheory.Functor.ι_mapBifunctorTotalIso_hom _ _ _ _ _ _ _ _ _ _
      _ _ p q n h)
    (fun P N => representedAffineToposTensorComplexIso B S hS U'
      (((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N))
    (fun _ _ p q n h => CategoryTheory.Functor.ι_mapBifunctorTotalIso_hom _ _ _ _ _ _ _ _ _ _
      _ _ p q n h)
    (fun P N => CochainComplex.ExtendScalars.extendScalarsMonoidalIso
      (representedAffineCommRingCatHom B S hS g₀).hom P N)
    (fun P N p q n h =>
      CochainComplex.ExtendScalars.extendScalars_map_ι_extendScalarsMonoidalIso_inv _ P N p q n h)

end AlgebraicGeometry.Space

end
