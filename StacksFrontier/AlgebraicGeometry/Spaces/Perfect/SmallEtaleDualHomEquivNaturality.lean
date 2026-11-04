module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDualHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedBidualNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomDinaturality

/-!
# Naturality in the perfect object of `Hom(E, M) ≅ Hom(𝒪_X, E^∨ ⊗^L M)`

Let `X` be an algebraic space.  The identification
`AlgebraicGeometry.Space.smallEtaleHomAddEquivUnitTensorDual` of
`Hom(E, M)` with `Hom(𝒪_X, E^∨ ⊗^L M)`, for `E` perfect, is natural in `E`: for a morphism
`u : E ⟶ E'` of perfect objects, precomposition with `u` corresponds to postcomposition with
`u^∨ ⊗^L M`, where `u^∨ : E'^∨ ⟶ E^∨` is the dual morphism
`AlgebraicGeometry.Space.smallEtaleDerivedDualMap`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomTensorDualNatIso_naturality_left`: the
  isomorphism `RSheafHom(E, -) ≅ E^∨ ⊗^L -` is natural in `E`.
* `AlgebraicGeometry.Space.smallEtaleHomAddEquivUnitTensorDual_naturality_left`:
  `Hom(E, M) ≃+ Hom(𝒪_X, E^∨ ⊗^L M)` is natural in `E`.
* `AlgebraicGeometry.Space.smallEtaleExtAddEquivUnitTensorDual_naturality_left`: the same for
  `Ext^i(E, M) = Hom(E, M[i])`.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- `RSheafHom(u, M)` on `X` is the derived internal Hom of the model at the image of `u`, brought
back along the derived equivalence. -/
theorem smallEtaleDerivedSheafHom_map_app
    {E E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (u : E ⟶ E')
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedSheafHom B S hS X).map u.op).app M =
      (smallEtaleModelDerivedEquivalence B S hS X).inverse.map
        (((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.map u).op).app
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj M)) := rfl

/-- An abstract form of the naturality of the dual transported along an equivalence: for an
equivalence `e : C ≌ D`, a bifunctor `R` on `D` contravariant in its first variable and
`s : e(O) ≅ O'`, the identification `e(e⁻¹ R(e E, e O)) ≅ R(e E, O')` is natural in `E`. -/
theorem _root_.CategoryTheory.Equivalence.transportDual_naturality {C D : Type*} [Category C]
    [Category D] (e : C ≌ D) (R : Dᵒᵖ ⥤ D ⥤ D) {O : C} {O' : D} (s : e.functor.obj O ≅ O')
    {E E' : C} (u : E ⟶ E') :
    e.functor.map (e.inverse.map ((R.map (e.functor.map u).op).app (e.functor.obj O))) ≫
        e.counit.app _ ≫ (R.obj (op (e.functor.obj E))).map s.hom =
      (e.counit.app _ ≫ (R.obj (op (e.functor.obj E'))).map s.hom) ≫
        (R.map (e.functor.map u).op).app O' := by
  have h := e.counit.naturality ((R.map (e.functor.map u).op).app (e.functor.obj O))
  simp only [Functor.comp_map, Functor.id_map] at h
  rw [← Category.assoc, h, Category.assoc, Category.assoc, NatTrans.naturality]

/-- The identification of the dual on `X`, read on the model, with the dual on the model,
spelled out. -/
theorem smallEtaleModelDerivedDualIso_hom
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleModelDerivedDualIso B S hS X E).hom =
      (smallEtaleModelDerivedEquivalence B S hS X).counit.app _ ≫
        ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).obj
          (op ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E))).map
            (smallEtaleModelDerivedStructureSheafIso B S hS X).hom :=
  rfl

/-- The identification of the dual on `X`, read on the model, with the dual on the model is
natural in the dualized object. -/
theorem smallEtaleModelDerivedDualIso_naturality
    {E E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (u : E ⟶ E') :
    (smallEtaleModelDerivedEquivalence B S hS X).functor.map
          (((smallEtaleDerivedSheafHom B S hS X).map u.op).app
            ((DerivedCategory.singleFunctor _ 0).obj
              (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))) ≫
        (smallEtaleModelDerivedDualIso B S hS X E).hom =
      (smallEtaleModelDerivedDualIso B S hS X E').hom ≫
        ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.map u).op).app
            (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2)) :=
  Equivalence.transportDual_naturality (smallEtaleModelDerivedEquivalence B S hS X)
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleModelDerivedStructureSheafIso B S hS X) u

/-- The component of `smallEtaleDerivedSheafHomTensorDualNatIso` at `M`, spelled out. -/
theorem smallEtaleDerivedSheafHomTensorDualNatIso_hom_app
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedSheafHomTensorDualNatIso B S hS X E hE).hom.app M =
      (smallEtaleModelDerivedEquivalence B S hS X).inverse.map
          ((RingedSite.derivedDualTensorSheafHomIso (smallEtaleModelRingedSite B S hS X.1 X.2)
              ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E)
              ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj M)
              (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE)).inv ≫
            ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
              (smallEtaleModelRingedSite B S hS X.1 X.2)
              (RingedSite.canonicalRingedSiteDerivedTensorProduct
                (smallEtaleModelRingedSite B S hS X.1 X.2))).inv.app
                (RingedSite.derivedDual (smallEtaleModelRingedSite B S hS X.1 X.2)
                  ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E))).app
              ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj M) ≫
            ((Stacks.SheafOfModules.derivedTensorProductFunctor
              (smallEtaleModelRingedSite B S hS X.1 X.2)).map
                (smallEtaleModelDerivedDualIso B S hS X E).inv).app
              ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj M)) ≫
        (smallEtaleModelDerivedEquivalence B S hS X).inverse.map
          ((smallEtaleModelDerivedTensorIso B S hS X).inv.app
            (smallEtaleDerivedDual B S hS X E, M)) ≫ 𝟙 _ ≫
        (smallEtaleModelDerivedEquivalence B S hS X).unitIso.inv.app
          (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj M) ≫
        𝟙 _ :=
  rfl

/-- An abstract form of the naturality in `K` of `RSheafHom(K, G) ≅ G ⊗ K^∨ ≅ K^∨ ⊗ G ≅ P ⊗ G`:
given the naturality of the first isomorphism in `K` and a morphism `v : P' ⟶ P` compatible
with `RSheafHom(g, O)` under `dE`, `dE'`, the composites are natural. -/
theorem _root_.CategoryTheory.Functor.sheafHomTensorDual_naturality_aux {D : Type*} [Category D]
    (T : D ⥤ D ⥤ D) (R : Dᵒᵖ ⥤ D ⥤ D) (O : D) (br : T ≅ T.flip) {K K' : D} (g : K ⟶ K')
    (iE : ∀ G, (T.obj G).obj ((R.obj (op K)).obj O) ≅ (R.obj (op K)).obj G)
    (iE' : ∀ G, (T.obj G).obj ((R.obj (op K')).obj O) ≅ (R.obj (op K')).obj G)
    (hnat : ∀ G, (T.obj G).map ((R.map g.op).app O) ≫ (iE G).hom =
      (iE' G).hom ≫ (R.map g.op).app G)
    {P P' : D} (dE : P ≅ (R.obj (op K)).obj O) (dE' : P' ≅ (R.obj (op K')).obj O) (v : P' ⟶ P)
    (hv : v ≫ dE.hom = dE'.hom ≫ (R.map g.op).app O) (G : D) :
    (R.map g.op).app G ≫ (iE G).inv ≫ (br.inv.app ((R.obj (op K)).obj O)).app G ≫
        (T.map dE.inv).app G =
      ((iE' G).inv ≫ (br.inv.app ((R.obj (op K')).obj O)).app G ≫ (T.map dE'.inv).app G) ≫
        (T.map v).app G := by
  have h1 : (R.map g.op).app G ≫ (iE G).inv =
      (iE' G).inv ≫ (T.obj G).map ((R.map g.op).app O) := by
    rw [Iso.comp_inv_eq, Category.assoc, hnat, Iso.inv_hom_id_assoc]
  have h2 : (T.obj G).map ((R.map g.op).app O) ≫ (br.inv.app ((R.obj (op K)).obj O)).app G =
      (br.inv.app ((R.obj (op K')).obj O)).app G ≫ (T.map ((R.map g.op).app O)).app G :=
    congr_app (br.inv.naturality ((R.map g.op).app O)) G
  have h3 : (R.map g.op).app O ≫ dE.inv = dE'.inv ≫ v := by
    rw [Iso.comp_inv_eq, Category.assoc, hv, Iso.inv_hom_id_assoc]
  have h3' : (T.map ((R.map g.op).app O)).app G ≫ (T.map dE.inv).app G =
      (T.map dE'.inv).app G ≫ (T.map v).app G := by
    rw [← NatTrans.comp_app, ← T.map_comp, h3, T.map_comp, NatTrans.comp_app]
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc ((T.obj G).map _), h2,
    Category.assoc, h3']
  simp only [Category.assoc]

/-- An abstract form of the passage from the model to `X` in the naturality of
`RSheafHom(E, -) ≅ E^∨ ⊗^L -`. -/
theorem _root_.CategoryTheory.Equivalence.transportTensorObj_naturality_aux {C D : Type*}
    [Category C] [Category D] (e : C ≌ D) (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (τ : Functor.uncurry.obj T ⋙ e.functor ≅ e.functor.prod e.functor ⋙ Functor.uncurry.obj T')
    {P P' : C} (w : P' ⟶ P) (M : C) {Z Z' : D} (r : Z' ⟶ Z)
    (a : Z ⟶ (T'.obj (e.functor.obj P)).obj (e.functor.obj M))
    (a' : Z' ⟶ (T'.obj (e.functor.obj P')).obj (e.functor.obj M))
    (h : r ≫ a = a' ≫ (T'.map (e.functor.map w)).app (e.functor.obj M)) :
    e.inverse.map r ≫ e.inverse.map a ≫ e.inverse.map (τ.inv.app (P, M)) ≫ 𝟙 _ ≫
        e.unitIso.inv.app ((T.obj P).obj M) ≫ 𝟙 _ =
      (e.inverse.map a' ≫ e.inverse.map (τ.inv.app (P', M)) ≫ 𝟙 _ ≫
        e.unitIso.inv.app ((T.obj P').obj M) ≫ 𝟙 _) ≫ (T.map w).app M := by
  have hτ : (T'.map (e.functor.map w)).app (e.functor.obj M) ≫ τ.inv.app (P, M) =
      τ.inv.app (P', M) ≫ e.functor.map ((T.map w).app M) := by
    simpa using τ.inv.naturality (Prod.mkHom w (𝟙 M))
  have hu := e.unitIso.inv.naturality ((T.map w).app M)
  simp only [Functor.comp_map, Functor.id_map] at hu
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [← e.inverse.map_comp_assoc, h, e.inverse.map_comp_assoc,
    ← e.inverse.map_comp_assoc ((T'.map (e.functor.map w)).app (e.functor.obj M)), hτ,
    e.inverse.map_comp_assoc, hu]

/-- The model half of the naturality in `E` of `RSheafHom(E, -) ≅ E^∨ ⊗^L -`. -/
theorem smallEtaleModelSheafHomTensorDual_naturality
    {E E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hE' : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E')
    (u : E ⟶ E')
    (G : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O))) :
    ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.map u).op).app G ≫
        (RingedSite.derivedDualTensorSheafHomIso (smallEtaleModelRingedSite B S hS X.1 X.2)
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E) G
            (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE)).inv ≫
          ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
            (smallEtaleModelRingedSite B S hS X.1 X.2)
            (RingedSite.canonicalRingedSiteDerivedTensorProduct
              (smallEtaleModelRingedSite B S hS X.1 X.2))).inv.app
              (RingedSite.derivedDual (smallEtaleModelRingedSite B S hS X.1 X.2)
                ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E))).app G ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor
            (smallEtaleModelRingedSite B S hS X.1 X.2)).map
              (smallEtaleModelDerivedDualIso B S hS X E).inv).app G =
      ((RingedSite.derivedDualTensorSheafHomIso (smallEtaleModelRingedSite B S hS X.1 X.2)
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E') G
            (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E' hE')).inv ≫
          ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
            (smallEtaleModelRingedSite B S hS X.1 X.2)
            (RingedSite.canonicalRingedSiteDerivedTensorProduct
              (smallEtaleModelRingedSite B S hS X.1 X.2))).inv.app
              (RingedSite.derivedDual (smallEtaleModelRingedSite B S hS X.1 X.2)
                ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E'))).app G ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor
            (smallEtaleModelRingedSite B S hS X.1 X.2)).map
              (smallEtaleModelDerivedDualIso B S hS X E').inv).app G) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor
            (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.map
            (smallEtaleDerivedDualMap B S hS X u))).app G :=
  Functor.sheafHomTensorDual_naturality_aux
    (Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2))
    (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
      (smallEtaleModelRingedSite B S hS X.1 X.2)
      (RingedSite.canonicalRingedSiteDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2)))
    ((smallEtaleModelDerivedEquivalence B S hS X).functor.map u)
    (fun G => RingedSite.derivedDualTensorSheafHomIso (smallEtaleModelRingedSite B S hS X.1 X.2)
      _ G (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE))
    (fun G => RingedSite.derivedDualTensorSheafHomIso (smallEtaleModelRingedSite B S hS X.1 X.2)
      _ G (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E' hE'))
    (fun G => RingedSite.derivedDualTensorSheafHomIso_naturality_dual
      (smallEtaleModelRingedSite B S hS X.1 X.2)
      (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E' hE')
      (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE) G
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.map u))
    (smallEtaleModelDerivedDualIso B S hS X E) (smallEtaleModelDerivedDualIso B S hS X E')
    _ (smallEtaleModelDerivedDualIso_naturality B S hS X u) G

/-- **`RSheafHom(E, -) ≅ E^∨ ⊗^L -` is natural in `E`**: for `u : E ⟶ E'` of perfect objects,
`RSheafHom(u, M)` corresponds to `u^∨ ⊗^L M`. -/
theorem smallEtaleDerivedSheafHomTensorDualNatIso_naturality_left
    {E E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hE' : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E')
    (u : E ⟶ E')
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedSheafHom B S hS X).map u.op).app M ≫
        (smallEtaleDerivedSheafHomTensorDualNatIso B S hS X E hE).hom.app M =
      (smallEtaleDerivedSheafHomTensorDualNatIso B S hS X E' hE').hom.app M ≫
        ((smallEtaleDerivedTensor B S hS X).map (smallEtaleDerivedDualMap B S hS X u)).app M := by
  have h1 := smallEtaleDerivedSheafHomTensorDualNatIso_hom_app B S hS X E hE M
  have h2 := smallEtaleDerivedSheafHomTensorDualNatIso_hom_app B S hS X E' hE' M
  have h3 := smallEtaleDerivedSheafHom_map_app B S hS X u M
  have key := Equivalence.transportTensorObj_naturality_aux
    (smallEtaleModelDerivedEquivalence B S hS X) (smallEtaleDerivedTensor B S hS X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleModelDerivedTensorIso B S hS X) (smallEtaleDerivedDualMap B S hS X u) M _ _ _
    (smallEtaleModelSheafHomTensorDual_naturality B S hS X hE hE' u
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj M))
  exact (congrArg₂ (fun a b => a ≫ b) h3 h1).trans (key.trans (congrArg
    (fun a => a ≫ ((smallEtaleDerivedTensor B S hS X).map
      (smallEtaleDerivedDualMap B S hS X u)).app M) h2.symm))

/-- **`Hom(E, M) ≃+ Hom(𝒪_X, E^∨ ⊗^L M)` is natural in the perfect object `E`**: for
`u : E ⟶ E'` of perfect objects, precomposition with `u` corresponds to postcomposition with
`u^∨ ⊗^L M`. -/
theorem smallEtaleHomAddEquivUnitTensorDual_naturality_left
    {E E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hE' : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E')
    (u : E ⟶ E') {M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (g : E' ⟶ M) :
    smallEtaleHomAddEquivUnitTensorDual B S hS X E hE M (u ≫ g) =
      smallEtaleHomAddEquivUnitTensorDual B S hS X E' hE' M g ≫
        ((smallEtaleDerivedTensor B S hS X).map (smallEtaleDerivedDualMap B S hS X u)).app M := by
  have hl : ((smallEtaleDerivedTensorProduct B S hS X).leftUnitor.app E).hom ≫ u ≫ g =
      ((smallEtaleDerivedTensor B S hS X).obj (structureDerived X)).map u ≫
        ((smallEtaleDerivedTensorProduct B S hS X).leftUnitor.app E').hom ≫ g := by
    have h := (smallEtaleDerivedTensorProduct B S hS X).leftUnitor.hom.naturality u
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) h.symm).trans
      (Category.assoc _ _ _))
  have hd := smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinatural B S hS X
    (structureDerived X) M u
    (((smallEtaleDerivedTensorSheafHomAdjunction B S hS X E').homEquiv (structureDerived X) M)
      (((smallEtaleDerivedTensorProduct B S hS X).leftUnitor.app E').hom ≫ g))
  have hd' := hd.trans (congrArg (fun t =>
    ((smallEtaleDerivedTensor B S hS X).obj (structureDerived X)).map u ≫ t)
    (Equiv.symm_apply_apply _ _))
  have h2 : ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X E).homEquiv (structureDerived X) M)
        (((smallEtaleDerivedTensorProduct B S hS X).leftUnitor.app E).hom ≫ u ≫ g) =
      ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X E').homEquiv (structureDerived X) M)
          (((smallEtaleDerivedTensorProduct B S hS X).leftUnitor.app E').hom ≫ g) ≫
        ((smallEtaleDerivedSheafHom B S hS X).map u.op).app M :=
    (congrArg ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X E).homEquiv
      (structureDerived X) M) (hl.trans hd'.symm)).trans (Equiv.apply_symm_apply _ _)
  show ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X E).homEquiv (structureDerived X) M)
        (((smallEtaleDerivedTensorProduct B S hS X).leftUnitor.app E).hom ≫ u ≫ g) ≫
      (smallEtaleDerivedSheafHomTensorDualNatIso B S hS X E hE).hom.app M =
    (((smallEtaleDerivedTensorSheafHomAdjunction B S hS X E').homEquiv (structureDerived X) M)
        (((smallEtaleDerivedTensorProduct B S hS X).leftUnitor.app E').hom ≫ g) ≫
      (smallEtaleDerivedSheafHomTensorDualNatIso B S hS X E' hE').hom.app M) ≫
        ((smallEtaleDerivedTensor B S hS X).map (smallEtaleDerivedDualMap B S hS X u)).app M
  rw [h2, Category.assoc, Category.assoc,
    smallEtaleDerivedSheafHomTensorDualNatIso_naturality_left B S hS X hE hE' u M]

/-- **`Ext^i(E, M) ≃+ Hom(𝒪_X, (E^∨ ⊗^L M)[i])` is natural in the perfect object `E`.** -/
theorem smallEtaleExtAddEquivUnitTensorDual_naturality_left
    {E E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hE' : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E')
    (u : E ⟶ E') (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (i : ℤ) (g : E' ⟶ M⟦i⟧) :
    smallEtaleExtAddEquivUnitTensorDual B S hS X E hE M i (u ≫ g) =
      smallEtaleExtAddEquivUnitTensorDual B S hS X E' hE' M i g ≫
        (((smallEtaleDerivedTensor B S hS X).map
          (smallEtaleDerivedDualMap B S hS X u)).app M)⟦i⟧' := by
  have : NatTrans.CommShift ((smallEtaleDerivedTensor B S hS X).map
      (smallEtaleDerivedDualMap B S hS X u)) ℤ :=
    (smallEtaleDerivedTensorProduct B S hS X).commShift₂.commShift_map _
  show smallEtaleHomAddEquivUnitTensorDual B S hS X E hE (M⟦i⟧) (u ≫ g) ≫ _ =
    (smallEtaleHomAddEquivUnitTensorDual B S hS X E' hE' (M⟦i⟧) g ≫ _) ≫ _
  rw [smallEtaleHomAddEquivUnitTensorDual_naturality_left B S hS X hE hE' u g, Category.assoc,
    Category.assoc]
  congr 1
  exact (NatTrans.shift_app_comm ((smallEtaleDerivedTensor B S hS X).map
    (smallEtaleDerivedDualMap B S hS X u)) i M).symm

end AlgebraicGeometry.Space

end
