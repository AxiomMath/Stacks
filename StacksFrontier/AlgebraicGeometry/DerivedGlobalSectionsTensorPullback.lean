module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsLerayCocycle
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoCompositionLaw
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.Existence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect

/-!
# Pulling back derived global sections of a tensor product

Let `g : X' ⟶ X` be a morphism of schemes over a map of base rings `φ : A ⟶ B`, let `E` be an
object of `D(𝒪_X)`, and let `β : Lg^* G ⟶ K'` be a map in `D(𝒪_{X'})`. This file builds the map

`RΓ_A(X, G ⊗^L E) ⟶ RΓ_B(X', K' ⊗^L Lg^* E)`

of `D(A)`: pull derived global sections back along `g`, identify `Lg^*(G ⊗^L E)` with
`Lg^* G ⊗^L Lg^* E` ([Stacks, Tag 079U]) and apply `β`. It proves that these maps are compatible
with composition: for `X'' --j--> X' --i--> X` over `A ⟶ B ⟶ C` and the transition
`Ri_* K' ⟶ R(j ≫ i)_* K''` determined by `φ : Lj^* K' ⟶ K''`, composing the map along `i` with
the one along `j` built from `φ` is the map along `j ≫ i`.

## Main definitions

* `AlgebraicGeometry.LerayOver.pullbackTensorHom`: the comparison of [Stacks, Tag 079U].
* `AlgebraicGeometry.LerayOver.tensorPullbackMap`: the map displayed above.

## Main results

* `AlgebraicGeometry.LerayOver.tensorPullbackMap_comp`: the compatibility with composition.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0DID](https://stacks.math.columbia.edu/tag/0DID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPullback derivedAdjunction)

universe u

namespace AlgebraicGeometry.LerayOver

attribute [local instance] HasDerivedCategory.standard

/-- The derived tensor product `- ⊗^L -` on `D(𝒪_X)` of [Stacks, Tag 06YU]. -/
def tensor (X : Scheme.{u}) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
        DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.toRingedSpace.sheaf

section Abstract

variable {A B : Type*} [Category A] [Category B] (TA : A ⥤ A ⥤ A) (TB : B ⥤ B ⥤ B)
  (L : A ⥤ B) (α : Functor.uncurry.obj TA ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TB)

/-- Naturality in the first variable of a morphism of bifunctors
`(G, E) ↦ L(G ⊗ E) ⟶ L G ⊗ L E`. -/
theorem bifunctor_naturality_left {G₁ G₂ : A} (a : G₁ ⟶ G₂) (E : A) :
    L.map ((TA.map a).app E) ≫ α.app (G₂, E) =
      α.app (G₁, E) ≫ (TB.map (L.map a)).app (L.obj E) := by
  have h := α.naturality (Prod.mkHom a (𝟙 E))
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
    CategoryTheory.Functor.map_id, Category.comp_id, Functor.prod_obj] at h
  exact h

/-- Naturality in the second variable of a morphism of bifunctors
`(G, E) ↦ L(G ⊗ E) ⟶ L G ⊗ L E`. -/
theorem bifunctor_naturality_right (G : A) {E₁ E₂ : A} (b : E₁ ⟶ E₂) :
    L.map ((TA.obj G).map b) ≫ α.app (G, E₂) =
      α.app (G, E₁) ≫ (TB.obj (L.obj G)).map (L.map b) := by
  have h := α.naturality (Prod.mkHom (𝟙 G) b)
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Functor.prod_obj] at h
  exact h

/-- The pointwise form of a composition law for comparisons `L(G ⊗ E) ⟶ L G ⊗ L E` along a
composite `Lg ⋙ Lf ≅ Lfg`. -/
theorem bifunctor_comp_app {C : Type*} [Category C] (TC : C ⥤ C ⥤ C) (Lf : B ⥤ C) (Lfg : A ⥤ C)
    (pc : L ⋙ Lf ⟶ Lfg) (αf : Functor.uncurry.obj TB ⋙ Lf ⟶ Lf.prod Lf ⋙ Functor.uncurry.obj TC)
    (αfg : Functor.uncurry.obj TA ⋙ Lfg ⟶ Lfg.prod Lfg ⋙ Functor.uncurry.obj TC)
    (h : Functor.whiskerLeft (Functor.uncurry.obj TA) pc ≫ αfg =
      Functor.whiskerRight α Lf ≫ Functor.whiskerLeft (L.prod L) αf ≫
        Functor.whiskerRight (NatTrans.prod pc pc) (Functor.uncurry.obj TC)) (G E : A) :
    pc.app ((TA.obj G).obj E) ≫ αfg.app (G, E) =
      Lf.map (α.app (G, E)) ≫ αf.app (L.obj G, L.obj E) ≫
        (TC.map (pc.app G)).app (Lf.obj (L.obj E)) ≫ (TC.obj (Lfg.obj G)).map (pc.app E) := by
  have h' := congrArg (fun τ => NatTrans.app τ (G, E)) h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.uncurry_obj_map, Functor.prod_obj, Functor.uncurry_obj_obj] at h'
  rw [h']
  simp

/-- A diagram chase with every morphism a variable: from `P = p ≫ q` and the commuting squares
`hn`, `hcoc`, `hbif`, `hfun`, the composites `P ≫ r ≫ s ≫ t` and `c ≫ d ≫ e` agree. -/
theorem chase_five {C : Type*} [Category C] {W U U' U'' V V' V'' W' W'' Z : C}
    (P : W ⟶ V) (p : W ⟶ U) (q : U ⟶ V) (r : V ⟶ V') (s : V' ⟶ V'') (t : V'' ⟶ Z)
    (c : W ⟶ W') (d : W' ⟶ W'') (e : W'' ⟶ Z)
    (r' : U ⟶ U') (q' : U' ⟶ V') (m : U' ⟶ U'') (n : U'' ⟶ W'') (e' : U'' ⟶ V'')
    (hn : q ≫ r = r' ≫ q') (hcoc : c ≫ d = p ≫ r' ≫ m ≫ n) (hbif : n ≫ e = e' ≫ t)
    (hfun : m ≫ e' = q' ≫ s) (hP : P = p ≫ q) :
    P ≫ r ≫ s ≫ t = c ≫ d ≫ e := by
  rw [hP, Category.assoc, reassoc_of% hn, reassoc_of% hcoc, hbif, reassoc_of% hfun]

/-- A bifunctor carries an identity of composites in its first variable to the corresponding
identity of components. -/
theorem bifunctor_map_comp_app {C D : Type*} [Category C] [Category D] (T : C ⥤ C ⥤ D)
    {a b c d : C} (x : a ⟶ b) (y : b ⟶ c) (x' : a ⟶ d) (y' : d ⟶ c) (h : x ≫ y = x' ≫ y')
    (Z : C) : (T.map x).app Z ≫ (T.map y).app Z = (T.map x').app Z ≫ (T.map y').app Z := by
  rw [← NatTrans.comp_app, ← Functor.map_comp, h, Functor.map_comp, NatTrans.comp_app]

/-- A diagram chase with every object, functor and morphism a variable: from `F1`, `F2` and `hX`,
the composite `P ⟶ Rψ'.obj (Γ''.obj S3)` through `θi`, `θj` and `cmp.hom` equals the one through
`θh`. -/
theorem chase_transition {DA DB DC DXp DXpp : Type*} [Category DA] [Category DB] [Category DC]
    [Category DXp] [Category DXpp] (Rψ : DB ⥤ DA) (Rχ : DC ⥤ DB) (Rψ' : DC ⥤ DA)
    (cmp : Rχ ⋙ Rψ ≅ Rψ') (Γ' : DXp ⥤ DB) (Γ'' : DXpp ⥤ DC) (Lj : DXp ⥤ DXpp)
    {P : DA} {Q Q' : DXp} {S1 S2 S3 T0 T1 : DXpp}
    (θi : P ⟶ Rψ.obj (Γ'.obj Q)) (mm : Q ⟶ Q') (θj : Γ'.obj Q' ⟶ Rχ.obj (Γ''.obj (Lj.obj Q')))
    (θj₀ : Γ'.obj Q ⟶ Rχ.obj (Γ''.obj (Lj.obj Q)))
    (p1 : Lj.obj Q' ⟶ S1) (p2 : S1 ⟶ S2) (p3 : S2 ⟶ S3)
    (θh : P ⟶ Rψ'.obj (Γ''.obj T0)) (pc : Lj.obj Q ⟶ T0) (q1 : T0 ⟶ T1) (q2 : T1 ⟶ S3)
    (F1 : Γ'.map mm ≫ θj = θj₀ ≫ Rχ.map (Γ''.map (Lj.map mm)))
    (F2 : θh ≫ cmp.inv.app (Γ''.obj T0) = θi ≫ Rψ.map θj₀ ≫ Rψ.map (Rχ.map (Γ''.map pc)))
    (hX : Lj.map mm ≫ p1 ≫ p2 ≫ p3 = pc ≫ q1 ≫ q2) :
    (θi ≫ Rψ.map (Γ'.map mm)) ≫
        Rψ.map ((θj ≫ Rχ.map (Γ''.map (p1 ≫ p2))) ≫ Rχ.map (Γ''.map p3)) ≫
        cmp.hom.app (Γ''.obj S3) =
      θh ≫ Rψ'.map (Γ''.map (q1 ≫ q2)) := by
  have F2' : θh = (θi ≫ Rψ.map θj₀ ≫ Rψ.map (Rχ.map (Γ''.map pc))) ≫ cmp.hom.app (Γ''.obj T0) := by
    rw [← F2, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have key := congrArg (fun x => Rψ.map (Rχ.map (Γ''.map x)) ≫ cmp.hom.app (Γ''.obj S3)) hX
  simp only [Functor.map_comp, Category.assoc] at key
  have n1 := cmp.hom.naturality (Γ''.map q1)
  have n2 := cmp.hom.naturality (Γ''.map q2)
  simp only [Functor.comp_map] at n1 n2
  rw [F2']
  simp only [Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc Rψ (Γ'.map mm), F1, Functor.map_comp]
  simp only [Category.assoc]
  rw [key, ← reassoc_of% n1, ← n2]

/-- A naturality diagram chase, with every object, functor and morphism a variable: from the
squares `hθ`, `hp` and `q₁ ≫ q = r`, the two composites `F.obj P₁ ⟶ R.obj (Γ'.obj Z)` agree. -/
theorem chase_naturality {DA DB DX DX' : Type*} [Category DA] [Category DB] [Category DX]
    [Category DX'] (F : DX ⥤ DA) (R : DB ⥤ DA) (Γ' : DX' ⥤ DB) (Lg : DX ⥤ DX')
    {P₁ P₂ : DX} {T₁ T₂ Z : DX'} (x : P₁ ⟶ P₂)
    (θ₁ : F.obj P₁ ⟶ R.obj (Γ'.obj (Lg.obj P₁))) (θ₂ : F.obj P₂ ⟶ R.obj (Γ'.obj (Lg.obj P₂)))
    (p₁ : Lg.obj P₁ ⟶ T₁) (p₂ : Lg.obj P₂ ⟶ T₂) (q₁ : T₁ ⟶ T₂) (q : T₂ ⟶ Z) (r : T₁ ⟶ Z)
    (hθ : F.map x ≫ θ₂ = θ₁ ≫ R.map (Γ'.map (Lg.map x)))
    (hp : Lg.map x ≫ p₂ = p₁ ≫ q₁) (hq : q₁ ≫ q = r) :
    F.map x ≫ θ₂ ≫ R.map (Γ'.map (p₂ ≫ q)) = θ₁ ≫ R.map (Γ'.map (p₁ ≫ r)) := by
  rw [reassoc_of% hθ, ← R.map_comp, ← Γ'.map_comp, reassoc_of% hp, hq]

/-- The components of a bifunctor at a composite. -/
theorem map_app_comp_map_app {C D : Type*} [Category C] [Category D] (T : C ⥤ C ⥤ D)
    {a b c : C} (x : a ⟶ b) (y : b ⟶ c) (Z : C) :
    (T.map x).app Z ≫ (T.map y).app Z = (T.map (x ≫ y)).app Z := by
  rw [Functor.map_comp, NatTrans.comp_app]

/-- **Pulling back along a unit and pushing through a Leray isomorphism.** For an adjunction
`L ⊣ R`, a functor `Γ` out of the target of `R`, functors `Γ'`, `res` and an isomorphism
`Ler : Γ' ⋙ res ≅ R ⋙ Γ`, the composite `Γ(η) ≫ Ler⁻¹ ≫ res(Γ'(y))` is invertible as soon as the
adjoint `η ≫ R(y)` of `y` is. -/
theorem isIso_unit_comp_inv_comp_map {C D DA DB : Type*} [Category C] [Category D] [Category DA]
    [Category DB] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (Γ : C ⥤ DA) (Γ' : D ⥤ DB)
    (res : DB ⥤ DA) (Ler : Γ' ⋙ res ≅ R ⋙ Γ) {P : C} {Q : D} (y : L.obj P ⟶ Q)
    (hy : IsIso (adj.homEquiv _ _ y)) :
    IsIso ((Γ.map (adj.unit.app P) ≫ Ler.inv.app (L.obj P)) ≫ res.map (Γ'.map y)) := by
  have h := Ler.inv.naturality y
  simp only [Functor.comp_map] at h
  have h' : adj.unit.app P ≫ R.map y = adj.homEquiv _ _ y := (adj.homEquiv_unit _ _ _).symm
  rw [Category.assoc, ← h, ← Category.assoc, ← Functor.map_comp, h']
  infer_instance

/-- The action of an uncurried bifunctor on a morphism in the first variable. -/
theorem uncurry_map_prodMk_id {C D : Type*} [Category C] [Category D] (T : C ⥤ C ⥤ D)
    {a b : C} (x : a ⟶ b) (Z : C) :
    (Functor.uncurry.obj T).map (Prod.mkHom x (𝟙 Z)) = (T.map x).app Z := by
  simp

end Abstract

section Pullback

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- **The pullback-tensor comparison of [Stacks, Tag 079U]**,
`Lg^*(G ⊗^L E) ⟶ Lg^* G ⊗^L Lg^* E`. -/
def pullbackTensorHom
    (G E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (derivedPullback g.toLRSHom.toShHom).obj (((tensor X).obj G).obj E) ⟶
      ((tensor X').obj ((derivedPullback g.toLRSHom.toShHom).obj G)).obj
        ((derivedPullback g.toLRSHom.toShHom).obj E) :=
  (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g.toLRSHom.toShHom).hom.app
    (G, E)

/-- The pullback-tensor comparison `pullbackTensorHom` is an isomorphism. -/
instance (G E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    IsIso (pullbackTensorHom g G E) :=
  inferInstanceAs (IsIso ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
    g.toLRSHom.toShHom).hom.app (G, E)))

/-- Naturality of the pullback-tensor comparison in the first factor. -/
theorem pullbackTensorHom_naturality_left
    {G₁ G₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    (a : G₁ ⟶ G₂) (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (derivedPullback g.toLRSHom.toShHom).map (((tensor X).map a).app E) ≫
        pullbackTensorHom g G₂ E =
      pullbackTensorHom g G₁ E ≫
        ((tensor X').map ((derivedPullback g.toLRSHom.toShHom).map a)).app
          ((derivedPullback g.toLRSHom.toShHom).obj E) :=
  bifunctor_naturality_left _ _ _
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g.toLRSHom.toShHom).hom a E

/-- Naturality of the pullback-tensor comparison in the second factor. -/
theorem pullbackTensorHom_naturality_right
    (G : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    {E₁ E₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    (b : E₁ ⟶ E₂) :
    (derivedPullback g.toLRSHom.toShHom).map (((tensor X).obj G).map b) ≫
        pullbackTensorHom g G E₂ =
      pullbackTensorHom g G E₁ ≫
        ((tensor X').obj ((derivedPullback g.toLRSHom.toShHom).obj G)).map
          ((derivedPullback g.toLRSHom.toShHom).map b) :=
  bifunctor_naturality_right _ _ _
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g.toLRSHom.toShHom).hom G b

end Pullback

section Composite

variable {X X' X'' : Scheme.{u}} (i : X' ⟶ X) (j : X'' ⟶ X')

/-- **The pullback-tensor comparison is compatible with composition**
([Stacks, Tag 079U] and [Stacks, Tag 0D5S]). -/
theorem pullbackTensorHom_comp
    (G E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (pullbackCompHom i j).app (((tensor X).obj G).obj E) ≫ pullbackTensorHom (j ≫ i) G E =
      (derivedPullback j.toLRSHom.toShHom).map (pullbackTensorHom i G E) ≫
        pullbackTensorHom j ((derivedPullback i.toLRSHom.toShHom).obj G)
          ((derivedPullback i.toLRSHom.toShHom).obj E) ≫
        ((tensor X'').map ((pullbackCompHom i j).app G)).app
          ((derivedPullback j.toLRSHom.toShHom).obj ((derivedPullback i.toLRSHom.toShHom).obj E)) ≫
        ((tensor X'').obj ((derivedPullback (j ≫ i).toLRSHom.toShHom).obj G)).map
          ((pullbackCompHom i j).app E) :=
  bifunctor_comp_app _ _ _
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso i.toLRSHom.toShHom).hom _ _ _
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical j.toLRSHom.toShHom
      i.toLRSHom.toShHom).hom
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso j.toLRSHom.toShHom).hom
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
      (j.toLRSHom.toShHom ≫ i.toLRSHom.toShHom)).hom
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp j.toLRSHom.toShHom
      i.toLRSHom.toShHom) G E

/-- **The tensor-level identity behind the compatibility of the transition maps.** For
`a : G ⟶ Ri_* K'` with adjoint `β : Li^* G ⟶ K'` and `φ : Lj^* K' ⟶ K''`, the two ways from
`L(j ≫ i)^*(G ⊗ E)` to `K'' ⊗ L(j ≫ i)^* E` agree: through `Lj^*(Li^* G ⊗ Li^* E)` and `β`, `φ`,
or directly through the adjoint of `a` followed by the transition `Ri_* K' ⟶ R(j ≫ i)_* K''`. -/
theorem pullbackTensorHom_comp_transition
    (G E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)))
    (K'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace)))
    (φ : (derivedPullback j.toLRSHom.toShHom).obj K' ⟶ K'')
    (a : G ⟶ (derivedPushforward i.toLRSHom.toShHom).obj K') :
    (derivedPullback j.toLRSHom.toShHom).map (pullbackTensorHom i G E ≫
        ((tensor X').map (((derivedAdjunction i.toLRSHom.toShHom).homEquiv _ _).symm a)).app
          ((derivedPullback i.toLRSHom.toShHom).obj E)) ≫
      pullbackTensorHom j K' ((derivedPullback i.toLRSHom.toShHom).obj E) ≫
      ((tensor X'').map φ).app ((derivedPullback j.toLRSHom.toShHom).obj
        ((derivedPullback i.toLRSHom.toShHom).obj E)) ≫
      ((tensor X'').obj K'').map ((pullbackCompHom i j).app E) =
    (pullbackCompHom i j).app (((tensor X).obj G).obj E) ≫ pullbackTensorHom (j ≫ i) G E ≫
      ((tensor X'').map (((derivedAdjunction (j ≫ i).toLRSHom.toShHom).homEquiv _ _).symm
        (a ≫ GrothendieckExistence.pushforwardTransition j.toLRSHom.toShHom i.toLRSHom.toShHom
          (j ≫ i).toLRSHom.toShHom rfl φ))).app
        ((derivedPullback (j ≫ i).toLRSHom.toShHom).obj E) := by
  have h0 : (pullbackCompHom i j).app G ≫
      ((derivedAdjunction (j ≫ i).toLRSHom.toShHom).homEquiv _ _).symm
        (a ≫ GrothendieckExistence.pushforwardTransition j.toLRSHom.toShHom i.toLRSHom.toShHom
          (j ≫ i).toLRSHom.toShHom rfl φ) =
      (derivedPullback j.toLRSHom.toShHom).map
        (((derivedAdjunction i.toLRSHom.toShHom).homEquiv _ _).symm a) ≫ φ := by
    have h := GrothendieckExistence.derivedPullbackCompIso_hom_app_comp_homEquiv_symm
      j.toLRSHom.toShHom i.toLRSHom.toShHom (j.toLRSHom.toShHom ≫ i.toLRSHom.toShHom) rfl φ a _
      rfl
    rw [eqToHom_refl, Category.id_comp] at h
    exact h
  refine chase_five _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackTensorHom_naturality_left j
      (((derivedAdjunction i.toLRSHom.toShHom).homEquiv G K').symm a)
      ((derivedPullback i.toLRSHom.toShHom).obj E))
    (pullbackTensorHom_comp i j G E)
    (((tensor X'').map _).naturality ((pullbackCompHom i j).app E)) ?_
    (Functor.map_comp _ _ _)
  exact bifunctor_map_comp_app _ _ _ _ _ h0 _

end Composite

/-! ### The map on derived global sections -/

section Map

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X X' : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ X)
  (w : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))

/-- **The map `RΓ_A(X, G ⊗^L E) ⟶ RΓ_B(X', K' ⊗^L Lg^* E)` determined by `β : Lg^* G ⟶ K'`**:
pull derived global sections back along `g`, identify `Lg^*(G ⊗^L E)` with
`Lg^* G ⊗^L Lg^* E` ([Stacks, Tag 079U]) and apply `β`. -/
def tensorPullbackMap
    (E G : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)))
    (β : (derivedPullback g.toLRSHom.toShHom).obj G ⟶ K') :
    (sections f).obj (((tensor X).obj G).obj E) ⟶
      (ModuleCat.restrictScalars φ).mapDerivedCategory.obj
        ((sections f').obj (((tensor X').obj K').obj
          ((derivedPullback g.toLRSHom.toShHom).obj E))) :=
  pullbackSectionsMap φ f f' g w (((tensor X).obj G).obj E) ≫
    (ModuleCat.restrictScalars φ).mapDerivedCategory.map ((sections f').map
      (pullbackTensorHom g G E ≫
        ((tensor X').map β).app ((derivedPullback g.toLRSHom.toShHom).obj E)))

/-- **The map `RΓ_A(X, G ⊗^L E) ⟶ RΓ_B(X', K' ⊗^L Lg^* E)` is natural in `G`.** -/
theorem tensorPullbackMap_naturality
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    {G₁ G₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    (b : G₁ ⟶ G₂)
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)))
    (β : (derivedPullback g.toLRSHom.toShHom).obj G₂ ⟶ K') :
    (sections f).map (((tensor X).map b).app E) ≫ tensorPullbackMap φ f f' g w E G₂ K' β =
      tensorPullbackMap φ f f' g w E G₁ K' ((derivedPullback g.toLRSHom.toShHom).map b ≫ β) :=
  chase_naturality _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackSectionsMap_naturality φ f f' g w _)
    (pullbackTensorHom_naturality_left g b E) (map_app_comp_map_app _ _ _ _)

/-- **The map along the counit is invertible for a perfect `E`** ([Stacks, Tag 0B54]): the map
`RΓ_A(X, Rg_* K' ⊗^L E) ⟶ RΓ_B(X', K' ⊗^L Lg^* E)` determined by the counit
`Lg^* Rg_* K' ⟶ K'` is an isomorphism. -/
theorem isIso_tensorPullbackMap_counit
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))) :
    IsIso (tensorPullbackMap φ f f' g w E ((derivedPushforward g.toLRSHom.toShHom).obj K') K'
      ((derivedAdjunction g.toLRSHom.toShHom).counit.app K')) := by
  have hpf := Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isPerfect
    g.toLRSHom.toShHom K' E hE
  have hy : IsIso ((derivedAdjunction g.toLRSHom.toShHom).homEquiv _ _
      (pullbackTensorHom g ((derivedPushforward g.toLRSHom.toShHom).obj K') E ≫
        ((tensor X').map ((derivedAdjunction g.toLRSHom.toShHom).counit.app K')).app
          ((derivedPullback g.toLRSHom.toShHom).obj E))) := by
    rw [← uncurry_map_prodMk_id]
    exact hpf
  exact isIso_unit_comp_inv_comp_map (derivedAdjunction g.toLRSHom.toShHom) (sections f)
    (sections f') (ModuleCat.restrictScalars φ).mapDerivedCategory (lerayIso φ f f' g w) _ hy

end Map

section PullbackComp

variable {X X' X'' : Scheme.{u}} (i : X' ⟶ X) (j : X'' ⟶ X') (h : X'' ⟶ X) (hh : j ≫ i = h)

/-- `Lj^* Li^* E ⟶ Lh^* E` for `h = j ≫ i`, the composition isomorphism of derived pullbacks. -/
def pullbackCompMap
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (derivedPullback j.toLRSHom.toShHom).obj ((derivedPullback i.toLRSHom.toShHom).obj E) ⟶
      (derivedPullback h.toLRSHom.toShHom).obj E :=
  (pullbackCompHom i j).app E ≫ eqToHom (by subst hh; rfl)

/-- For `h = j ≫ i` by `rfl`, `pullbackCompMap` is the component of `pullbackCompHom i j`. -/
theorem pullbackCompMap_rfl
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    pullbackCompMap i j (j ≫ i) rfl E = (pullbackCompHom i j).app E := by
  simp [pullbackCompMap]

end PullbackComp

section MapComp

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (ψ : A →+* B) (χ : B →+* C)
  (ψ' : A →+* C) (hψ' : ψ' = χ.comp ψ)
  {X X' X'' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B))
  (f'' : X'' ⟶ Spec (CommRingCat.of C)) (i : X' ⟶ X) (j : X'' ⟶ X') (h : X'' ⟶ X)
  (hh : j ≫ i = h)
  (wi : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom ψ))
  (wj : j ≫ f' = f'' ≫ Spec.map (CommRingCat.ofHom χ))
  (wh : h ≫ f = f'' ≫ Spec.map (CommRingCat.ofHom ψ'))

/-- **The transition map** `RΓ_B(X', K' ⊗^L Li^* E) ⟶ RΓ_C(X'', K'' ⊗^L Lh^* E)` determined by
`φ : Lj^* K' ⟶ K''`, for `h = j ≫ i`. -/
def tensorTransitionMap
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)))
    (K'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace)))
    (φ : (derivedPullback j.toLRSHom.toShHom).obj K' ⟶ K'') :
    (sections f').obj (((tensor X').obj K').obj ((derivedPullback i.toLRSHom.toShHom).obj E)) ⟶
      (ModuleCat.restrictScalars χ).mapDerivedCategory.obj
        ((sections f'').obj (((tensor X'').obj K'').obj
          ((derivedPullback h.toLRSHom.toShHom).obj E))) :=
  tensorPullbackMap χ f' f'' j wj ((derivedPullback i.toLRSHom.toShHom).obj E) K' K'' φ ≫
    (ModuleCat.restrictScalars χ).mapDerivedCategory.map ((sections f'').map
      (((tensor X'').obj K'').map (pullbackCompMap i j h hh E)))

/-- **The maps along `i` and along `j` compose to the map along `j ≫ i`.** For `a : G ⟶ Ri_* K'`
and `φ : Lj^* K' ⟶ K''`, the map `RΓ_A(X, G ⊗^L E) ⟶ RΓ_B(X', K' ⊗^L Li^* E)` determined by the
adjoint of `a`, followed by the transition map determined by `φ`, is the map
`RΓ_A(X, G ⊗^L E) ⟶ RΓ_C(X'', K'' ⊗^L Lh^* E)` determined by the adjoint of `a` composed with
the transition `Ri_* K' ⟶ Rh_* K''` of `φ`. -/
theorem tensorPullbackMap_comp
    (E G : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)))
    (K'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace)))
    (φ : (derivedPullback j.toLRSHom.toShHom).obj K' ⟶ K'')
    (a : G ⟶ (derivedPushforward i.toLRSHom.toShHom).obj K') :
    tensorPullbackMap ψ f f' i wi E G K'
        (((derivedAdjunction i.toLRSHom.toShHom).homEquiv _ _).symm a) ≫
      (ModuleCat.restrictScalars ψ).mapDerivedCategory.map
        (tensorTransitionMap χ f' f'' i j h hh wj E K' K'' φ) ≫
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} ψ χ ψ' hψ').hom.app _ =
    tensorPullbackMap ψ' f f'' h wh E G K''
      (((derivedAdjunction h.toLRSHom.toShHom).homEquiv _ _).symm
        (a ≫ GrothendieckExistence.pushforwardTransition j.toLRSHom.toShHom i.toLRSHom.toShHom
          h.toLRSHom.toShHom (by subst hh; rfl) φ)) := by
  subst hψ' hh
  have hX := pullbackTensorHom_comp_transition i j G E K' K'' φ a
  rw [← pullbackCompMap_rfl i j E] at hX
  exact chase_transition _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackSectionsMap_naturality χ f' f'' j wj _)
    (pullbackSectionsMap_comp ψ χ f f' f'' i j wi wj (((tensor X).obj G).obj E)) hX

end MapComp

end AlgebraicGeometry.LerayOver

end
