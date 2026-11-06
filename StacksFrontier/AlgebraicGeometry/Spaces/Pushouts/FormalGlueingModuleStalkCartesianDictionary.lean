module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageStalkMapGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleSpacesAbelianSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DirectImageFiberMapGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModuleStalkCartesian

/-!
# Stacks 0AER on geometric module fibres, unconditionally

`AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_directImageFiberMap_of_compat` proves
that, in Situation 0AEV, the square of geometric module fibres
```
(f_*G)_x̄           --θ_G-->            G_ȳ
    |                                   |
(f_*(j'_*(G|_V)))_x̄  --θ-->  (j'_*(G|_V))_ȳ
```
is cartesian, given a dictionary: natural isomorphisms `α`, `β` identifying (after forgetting to
abelian groups and lifting to `u + 1`) the module fibres at `x̄ = f(ȳ)` of `f_*` and at `ȳ` with
abelian geometric stalks, which carry `θ = AlgebraicGeometry.Space.directImageFiberMap` to the
stalk comparison `AlgebraicGeometry.Space.smallEtaleAbelianDirectImageStalkMap`.  This file
constructs the dictionary for every morphism `f : Y ⟶ X` of algebraic spaces and removes the
hypothesis.

The two identifications are the fibre of the underlying abelian sheaf
(`Stacks.sheafModuleFiberOfCommRingForget₂Iso`, an identity) followed by the comparison of the
fibre at the point of Stacks 04K0 with the geometric stalk of Stacks 04JY, and, at `x̄`, by an
identification `ω` of the lifted abelian sheaf of `f_*M` with the abelian direct image of the
lifted abelian sheaf of `M`.  That `θ` is carried to the stalk comparison is checked on germs: a
germ at a lift `u` of `x̄` into a chart `U` of `X` is refined by a chart lift `(W, w, h)` of `ȳ`
(`AlgebraicGeometry.Space.exists_chart_lift`), and both maps send the germ of a section `t` to
the germ at `w` of its restriction along `h` read through the counit of the comparison
equivalence of Stacks 03G1 (`AlgebraicGeometry.Space.directImageFiberMap_germ` on the module side,
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImageStalkMap_germ` on the abelian side).

## Main definitions

* `AlgebraicGeometry.Space.moduleFiberStalkIso`,
  `AlgebraicGeometry.Space.directImageFiberStalkIso`: the two halves of the dictionary.
* `AlgebraicGeometry.Space.modulePushforwardUliftAbelianSheafIso`: the identification
  `ω : (f_*M)^{ab}↑ ≅ f_*(M^{ab}↑)` of the lifted abelian sheaf of the module direct image with
  the abelian direct image of the lifted abelian sheaf.
* `CategoryTheory.Functor.sheafComposeTransposeIso`: transposing an identification of a
  restriction across a change of coefficients, through the restriction equivalence.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_directImageFiberMap`: the cartesian
  square above, with no hypothesis beyond the situation, the geometric point and the module.
* `AlgebraicGeometry.Space.directImageFiberMap_compat_ulift`: the dictionary carries `θ` to the
  stalk comparison, for every morphism of algebraic spaces.
* `AlgebraicGeometry.Space.directImageFiberAbMap_compat_of_germ`: the same, on abelian fibres,
  from a germ formula for `θ` and a section-level description of `ω`.
* `AlgebraicGeometry.Space.toPresheafFiber_directImageFiberAbMap`: the germ formula of `θ` on
  abelian fibres.
* `AlgebraicGeometry.Space.exists_chart_lift`: every lift of a geometric point into a base change
  of a chart is refined by a lift into a chart.

## Implementation notes

The objects `(forget₂ _ Ab).obj ((restrictScalars ρ).obj (fib.obj M))` and
`Φ.sheafFiber.obj (toSheaf.obj M)` are definitionally but not syntactically equal, and comparing
them inside a larger unification problem times out (`obtain`/`rcases` in a hom-ext goal,
`congrArg uliftFunctor.map` of an equation between them, `rfl` for a component of a pasted
isomorphism).  They are therefore never compared outside the two isomorphisms
`Stacks.sheafModuleFiberOfCommRingForget₂Iso` and
`Stacks.sheafModuleFiberOfCommRingRestrictScalarsForget₂Iso`, whose components are `Iso.refl`:
`θ` is retyped between abelian fibres as `AlgebraicGeometry.Space.directImageFiberAbMap`, the
components of the dictionary keep these isomorphisms in front, and `β` is the generic paste
`CategoryTheory.Functor.whiskerRightLeftIso`, whose component lemma is proved once at abstract
categories and instantiated.

Elements of composites of the heavy comparison isomorphisms are never computed: the kernel
unfolds the isomorphisms when it has to reduce `(a ≫ b ≫ c) t`, and also when the same morphism
is applied to an element under two spellings of its source (such as
`((f_* ⋙ toSheaf).obj M).obj.obj (op U)` and `(toSheaf.obj (f_*.obj M)).obj.obj (op U)`).  The
germ formula is stated on elements only with every map applied under its own type, and passed to
the morphism level by `AddCommGrpCat.comp_eq_comp_comp_comp_of_apply`, where the three maps are
opaque; the restriction map is retyped once as `AlgebraicGeometry.Space.directImageRestrictionMap`
so that the three maps compose without any change of spelling.

## References

* [Stacks Project, Tag 0AER](https://stacks.math.columbia.edu/tag/0AER)
* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks

universe w v u

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- The fibre of a sheaf of modules over a sheaf of commutative rings, read over any ring
through a restriction of scalars and forgotten to abelian groups, is the fibre of the underlying
abelian sheaf: neither the restriction of scalars nor the module structure changes the
underlying abelian group. -/
def sheafModuleFiberOfCommRingRestrictScalarsForget₂Iso (Φ : J.Point.{w})
    (O : Sheaf J CommRingCat.{w}) {R : Type w} [Ring R]
    (ρ : R →+* (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj) :
    (sheafModuleFiberOfCommRing Φ O ⋙ ModuleCat.restrictScalars.{w} ρ) ⋙
        forget₂ _ AddCommGrpCat.{w} ≅
      SheafOfModules.toSheaf.{w} (commRingSheafToRingSheaf O) ⋙ Φ.sheafFiber :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The fibre of a sheaf of modules over a sheaf of commutative rings, forgotten to abelian
groups, is the fibre of the underlying abelian sheaf. -/
def sheafModuleFiberOfCommRingForget₂Iso (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w}) :
    sheafModuleFiberOfCommRing Φ O ⋙ forget₂ _ AddCommGrpCat.{w} ≅
      SheafOfModules.toSheaf.{w} (commRingSheafToRingSheaf O) ⋙ Φ.sheafFiber :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- Maps out of the image under a functor preserving filtered colimits of the fibre of a
presheaf at a point are determined by their composites with the images of the germ maps. -/
lemma presheafFiber_map_hom_ext {A' : Type*} [Category* A'] [HasColimitsOfSize.{w, w} A']
    {A'' : Type*} [Category* A''] [HasColimitsOfSize.{w, w} A''] (F : A' ⥤ A'')
    [PreservesFilteredColimitsOfSize.{w, w} F] (Φ : J.Point.{w}) (P : Cᵒᵖ ⥤ A') {T : A''}
    {φ ψ : F.obj (Φ.presheafFiber.obj P) ⟶ T}
    (H : ∀ (U : C) (x : Φ.fiber.obj U),
      F.map (Φ.toPresheafFiber U x P) ≫ φ = F.map (Φ.toPresheafFiber U x P) ≫ ψ) : φ = ψ := by
  refine (cancel_epi ((Φ.presheafFiberCompIso F).hom.app P)).1
    (Φ.presheafFiber_hom_ext (fun U x ↦ ?_))
  have e := Φ.toPresheafFiber_presheafFiberCompIso_hom_app F U x P
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) e).trans
    ((H U x).trans ((congrArg (· ≫ ψ) e).symm.trans (Category.assoc _ _ _))))

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- `Stacks.presheafFiber_map_hom_ext` for the fibre of a sheaf. -/
lemma sheafFiber_map_hom_ext {A' : Type*} [Category* A'] [HasColimitsOfSize.{w, w} A']
    {A'' : Type*} [Category* A''] [HasColimitsOfSize.{w, w} A''] (F : A' ⥤ A'')
    [PreservesFilteredColimitsOfSize.{w, w} F] (Φ : J.Point.{w}) (P : Sheaf J A') {T : A''}
    {φ ψ : F.obj (Φ.sheafFiber.obj P) ⟶ T}
    (H : ∀ (U : C) (x : Φ.fiber.obj U),
      F.map (Φ.toPresheafFiber U x P.obj) ≫ φ = F.map (Φ.toPresheafFiber U x P.obj) ≫ ψ) :
    φ = ψ :=
  presheafFiber_map_hom_ext F Φ P.obj H

end Stacks

/-- A composite `g ≫ d` of morphisms of abelian groups equals `(c₀ ≫ m ≫ r) ≫ g'` as soon
as the two agree on elements in the form `d (g t) = g' (r (m (c₀ t)))`. -/
lemma AddCommGrpCat.comp_eq_comp_comp_comp_of_apply.{v} {A B C D E F : AddCommGrpCat.{v}}
    (g : A ⟶ B) (d : B ⟶ F) (c₀ : A ⟶ C) (m : C ⟶ D) (r : D ⟶ E) (g' : E ⟶ F)
    (H : ∀ t, d (g t) = g' (r (m (c₀ t)))) : g ≫ d = (c₀ ≫ m ≫ r) ≫ g' :=
  AddCommGrpCat.ext fun t ↦ H t

namespace CategoryTheory.Functor

variable {𝒜₁ 𝒜₂ 𝒜₃ 𝒜₄ 𝒜₅ 𝒜₆ : Type*} [Category* 𝒜₁] [Category* 𝒜₂] [Category* 𝒜₃]
  [Category* 𝒜₄] [Category* 𝒜₅] [Category* 𝒜₆]

/-- Pasting a natural isomorphism `P ⋙ P' ≅ T ⋙ Φ` with a natural isomorphism
`Φ ⋙ V ≅ Q ⋙ Ψ`, whiskered by `V` and by `T`. -/
def whiskerRightLeftIso {P : 𝒜₁ ⥤ 𝒜₂} {P' : 𝒜₂ ⥤ 𝒜₃} {V : 𝒜₃ ⥤ 𝒜₄} {T : 𝒜₁ ⥤ 𝒜₅}
    {Φ : 𝒜₅ ⥤ 𝒜₃} {Q : 𝒜₅ ⥤ 𝒜₆} {Ψ : 𝒜₆ ⥤ 𝒜₄} (ι : P ⋙ P' ≅ T ⋙ Φ)
    (γ : Φ ⋙ V ≅ Q ⋙ Ψ) : P ⋙ P' ⋙ V ≅ (T ⋙ Q) ⋙ Ψ :=
  (associator _ _ _).symm ≪≫ isoWhiskerRight ι V ≪≫ associator _ _ _ ≪≫
    isoWhiskerLeft T γ ≪≫ (associator _ _ _).symm

/-- The component of `CategoryTheory.Functor.whiskerRightLeftIso`. -/
lemma whiskerRightLeftIso_hom_app {P : 𝒜₁ ⥤ 𝒜₂} {P' : 𝒜₂ ⥤ 𝒜₃} {V : 𝒜₃ ⥤ 𝒜₄}
    {T : 𝒜₁ ⥤ 𝒜₅} {Φ : 𝒜₅ ⥤ 𝒜₃} {Q : 𝒜₅ ⥤ 𝒜₆} {Ψ : 𝒜₆ ⥤ 𝒜₄} (ι : P ⋙ P' ≅ T ⋙ Φ)
    (γ : Φ ⋙ V ≅ Q ⋙ Ψ) (M : 𝒜₁) :
    (whiskerRightLeftIso ι γ).hom.app M = V.map (ι.hom.app M) ≫ γ.hom.app (T.obj M) := by
  simp [whiskerRightLeftIso]

end CategoryTheory.Functor

namespace CategoryTheory.Functor

universe w w' v v' vv uu vv' uu' v₀ u₀

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsContinuous J K]
  {A : Type w} [Category.{v} A] {A' : Type w'} [Category.{v'} A'] (F : A ⥤ A')
  [J.HasSheafCompose F] [K.HasSheafCompose F]
  [(G.sheafPushforwardContinuous A' J K).IsEquivalence]
  {𝒜 : Type u₀} [Category.{v₀} 𝒜] (H : 𝒜 ⥤ Sheaf K A) (T : 𝒜 ⥤ Sheaf J A)
  (κ : H ⋙ G.sheafPushforwardContinuous A J K ≅ T)

/-- `F` applied to the component of `κ`, typed as a morphism out of the restriction of `H` with
its coefficients changed (which it is, on the nose). -/
def sheafComposeRestrictionHom (M : 𝒜) :
    (G.sheafPushforwardContinuous A' J K).asEquivalence.functor.obj
        ((H ⋙ sheafCompose K F).obj M) ⟶ (sheafCompose J F).obj (T.obj M) :=
  (sheafCompose J F).map (κ.hom.app M)

/-- `CategoryTheory.Functor.sheafComposeRestrictionHom` is an isomorphism, being `F` applied to a
component of the isomorphism `κ`.  Stated as a lemma rather than an instance because instance
search does not see through the retyping of its source. -/
lemma isIso_sheafComposeRestrictionHom (M : 𝒜) :
    IsIso (sheafComposeRestrictionHom J K G F H T κ M) :=
  inferInstanceAs (IsIso ((sheafCompose J F).map (κ.hom.app M)))

/-- The morphism underlying `CategoryTheory.Functor.sheafComposeTransposeIso`: componentwise,
the transpose across the restriction equivalence at `A'` of `F` applied to the component of
`κ`. -/
def sheafComposeTransposeHom :
    H ⋙ sheafCompose K F ⟶ T ⋙ sheafCompose J F ⋙ (G.sheafPushforwardContinuous A' J K).inv where
  app M := (G.sheafPushforwardContinuous A' J K).asEquivalence.toAdjunction.homEquiv _ _
    (sheafComposeRestrictionHom J K G F H T κ M)
  naturality {M M'} g := by
    refine ((G.sheafPushforwardContinuous A' J K).asEquivalence.toAdjunction
      |>.homEquiv_naturality_left _ _).symm.trans (Eq.trans ?_
        ((G.sheafPushforwardContinuous A' J K).asEquivalence.toAdjunction.homEquiv_naturality_right
          _ _))
    congr 1
    exact ((sheafCompose J F).map_comp _ _).symm.trans
      ((congrArg (sheafCompose J F).map (κ.hom.naturality g)).trans
        ((sheafCompose J F).map_comp _ _))

/-- Each component of `CategoryTheory.Functor.sheafComposeTransposeHom` is an isomorphism: it is
the unit of an equivalence followed by the inverse equivalence applied to an isomorphism. -/
instance (M : 𝒜) : IsIso ((sheafComposeTransposeHom J K G F H T κ).app M) := by
  dsimp only [sheafComposeTransposeHom]
  rw [Adjunction.homEquiv_unit]
  have h1 : IsIso ((G.sheafPushforwardContinuous A' J K).asEquivalence.toAdjunction.unit.app
      ((H ⋙ sheafCompose K F).obj M)) :=
    inferInstanceAs (IsIso ((G.sheafPushforwardContinuous A' J K).asEquivalence.unitIso.hom.app _))
  have h2 : IsIso ((G.sheafPushforwardContinuous A' J K).asEquivalence.inverse.map
      (sheafComposeRestrictionHom J K G F H T κ M)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_sheafComposeRestrictionHom J K G F H T κ M)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- `CategoryTheory.Functor.sheafComposeTransposeHom` is an isomorphism, componentwise. -/
instance : IsIso (sheafComposeTransposeHom J K G F H T κ) :=
  NatIso.isIso_of_isIso_app _

/-- **Transposing a restriction comparison across a change of coefficients.**  If restricting
`H` along `G` is `T`, then `H` with its coefficients changed by `F` is the inverse of the
restriction equivalence at `A'` applied to `T` with its coefficients changed. -/
def sheafComposeTransposeIso :
    H ⋙ sheafCompose K F ≅ T ⋙ sheafCompose J F ⋙ (G.sheafPushforwardContinuous A' J K).inv :=
  asIso (sheafComposeTransposeHom J K G F H T κ)

/-- After restriction, `CategoryTheory.Functor.sheafComposeTransposeIso` followed by the counit
of the restriction equivalence at `A'` is `F` applied to `κ`. -/
lemma sheafPushforwardContinuous_map_sheafComposeTransposeIso_hom_app_comp (M : 𝒜) :
    (G.sheafPushforwardContinuous A' J K).map ((sheafComposeTransposeIso J K G F H T κ).hom.app M) ≫
        (G.sheafPushforwardContinuous A' J K).asEquivalence.counitIso.hom.app
          ((sheafCompose J F).obj (T.obj M)) =
      sheafComposeRestrictionHom J K G F H T κ M :=
  ((G.sheafPushforwardContinuous A' J K).asEquivalence.toAdjunction.homEquiv_counit
    _ _ _).symm.trans (Equiv.symm_apply_apply _ _)

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Every lift of a geometric point into a base change of a chart is refined by a lift into a
chart.**  For `f : Y ⟶ X`, a geometric point `ȳ` of `Y` and a lift `u` of its image into an
étale chart `U` of `X`, there are an étale chart `W` of `Y`, a lift `w` of `ȳ` into it and a
map `W ⟶ U ×_X Y` over `Y` carrying `w` to the lift of `ȳ` that the cartesian square of
Stacks 03G2, part (1) assigns to `u`.  This is the initiality of the small étale neighbourhoods
among all étale neighbourhoods. -/
lemma exists_chart_lift {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1) (U : SmallEtale B S hS X.1)
    (u : (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).fiber.obj U) :
    ∃ (W : SmallEtale B S hS Y.1) (w : (etaleSitePoint B S hS Y.1 y Y.2).fiber.obj W)
      (h : (comparisonFunctor B S hS Y).obj W ⟶
        (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U)),
      (spacesEtaleSitePoint y).fiber.map h w =
        (spacesBaseChangeFiberIso B S hS f y).inv.app ((comparisonFunctor B S hS X).obj U) u := by
  obtain ⟨⟨e, _, h⟩⟩ := (Functor.Initial.out (F := smallToSpacesFiberElements B S hS y)
    ((spacesGeometricFiber y).elementsMk
      ((spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))
      ((spacesBaseChangeFiberIso B S hS f y).inv.app ((comparisonFunctor B S hS X).obj U) u))).is_nonempty
  exact ⟨e.obj, e.val, h.hom, h.map_val⟩

/-! ### Geometric module fibres against geometric stalks of abelian sheaves -/

section FiberStalk

variable (Z : AlgebraicSpaces B S hS) (z : GeometricPoint B S hS Z.1)

/-- **The fibre of an abelian sheaf at `u`, lifted, is the geometric stalk of the lifted
sheaf.**  The fibre at the point of Stacks 04K0 commutes with the universe lift
(`CategoryTheory.GrothendieckTopology.Point.sheafFiberCompIso`), and is the geometric stalk of
Stacks 04JY by `AlgebraicGeometry.Space.etaleSitePointStalkFunctorIso`. -/
def abelianFiberStalkUliftIso :
    (etaleSitePoint B S hS Z.1 z Z.2).sheafFiber (A := AddCommGrpCat.{u}) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      sheafCompose (SmallEtale.topology B S hS Z.1) AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
        smallEtaleAbelianStalk B S hS z :=
  Functor.isoWhiskerLeft (sheafToPresheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u})
      ((etaleSitePoint B S hS Z.1 z Z.2).presheafFiberCompIso
        AddCommGrpCat.uliftFunctor.{u + 1, u}).symm ≪≫
    Functor.isoWhiskerLeft
      (sheafCompose (SmallEtale.topology B S hS Z.1) AddCommGrpCat.uliftFunctor.{u + 1, u})
      (Functor.isoWhiskerLeft
        (sheafToPresheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
        (etaleSitePointStalkFunctorIso B S hS Z.1 z Z.2))

/-- The germ formula for `AlgebraicGeometry.Space.abelianFiberStalkUliftIso`: the lift of the
germ of a section is carried to the germ of the lifted section. -/
@[reassoc]
lemma uliftFunctor_map_toPresheafFiber_abelianFiberStalkUliftIso_hom
    (P : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u})
    (U : SmallEtale B S hS Z.1) (x : (etaleSitePoint B S hS Z.1 z Z.2).fiber.obj U) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        ((etaleSitePoint B S hS Z.1 z Z.2).toPresheafFiber U x P.obj) ≫
      (abelianFiberStalkUliftIso B S hS Z z).hom.app P =
    (etaleSitePoint B S hS Z.1 z Z.2).toPresheafFiber U x
        ((sheafCompose (SmallEtale.topology B S hS Z.1)
          AddCommGrpCat.uliftFunctor.{u + 1, u}).obj P).obj ≫
      (etaleSitePointStalkFunctorIso B S hS Z.1 z Z.2).hom.app
        ((sheafCompose (SmallEtale.topology B S hS Z.1)
          AddCommGrpCat.uliftFunctor.{u + 1, u}).obj P).obj := by
  have h := (etaleSitePoint B S hS Z.1 z Z.2).toPresheafFiber_presheafFiberCompIso_hom_app
    AddCommGrpCat.uliftFunctor.{u + 1, u} U x P.obj
  have h' : AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        ((etaleSitePoint B S hS Z.1 z Z.2).toPresheafFiber U x P.obj) ≫
      ((etaleSitePoint B S hS Z.1 z Z.2).presheafFiberCompIso
        AddCommGrpCat.uliftFunctor.{u + 1, u}).inv.app P.obj =
      (etaleSitePoint B S hS Z.1 z Z.2).toPresheafFiber U x
        (P.obj ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) := by
    rw [← h, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h')

/-- **The dictionary on the target side.**  The geometric module fibre at `z`, read over any ring
through a restriction of scalars, forgotten to abelian groups and lifted, is the geometric stalk
of the lifted abelian sheaf underlying the module. -/
def moduleFiberStalkIso {R : Type u} [Ring R]
    (ρ : R →+* Stacks.ringFiber (etaleSitePoint B S hS Z.1 z Z.2)
      (smallEtaleRingedTopos B S hS Z).O.obj) :
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Z.1 z Z.2)
          (smallEtaleRingedTopos B S hS Z).O ⋙ ModuleCat.restrictScalars.{u} ρ) ⋙
        forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      moduleUliftAbelianSheaf B S hS Z ⋙ smallEtaleAbelianStalk B S hS z :=
  Functor.whiskerRightLeftIso
    (Stacks.sheafModuleFiberOfCommRingRestrictScalarsForget₂Iso
      (etaleSitePoint B S hS Z.1 z Z.2) (smallEtaleRingedTopos B S hS Z).O ρ)
    (abelianFiberStalkUliftIso B S hS Z z)

/-- **The dictionary on the source side, before the direct image.**  The geometric module fibre
at `z`, forgotten to abelian groups and lifted, is the geometric stalk of the lifted abelian sheaf
underlying the module. -/
def moduleFiberStalkIso' :
    Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Z.1 z Z.2)
          (smallEtaleRingedTopos B S hS Z).O ⋙
        forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      moduleUliftAbelianSheaf B S hS Z ⋙ smallEtaleAbelianStalk B S hS z :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.sheafModuleFiberOfCommRingForget₂Iso
        (etaleSitePoint B S hS Z.1 z Z.2) (smallEtaleRingedTopos B S hS Z).O)
      AddCommGrpCat.uliftFunctor.{u + 1, u} ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Z))
      (abelianFiberStalkUliftIso B S hS Z z) ≪≫
    (Functor.associator _ _ _).symm

/-- The component of `AlgebraicGeometry.Space.moduleFiberStalkIso`, with the identity
`Stacks.sheafModuleFiberOfCommRingRestrictScalarsForget₂Iso` kept in front. -/
lemma moduleFiberStalkIso_hom_app {R : Type u} [Ring R]
    (ρ : R →+* Stacks.ringFiber (etaleSitePoint B S hS Z.1 z Z.2)
      (smallEtaleRingedTopos B S hS Z).O.obj) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (moduleFiberStalkIso B S hS Z z ρ).hom.app M =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map
          ((Stacks.sheafModuleFiberOfCommRingRestrictScalarsForget₂Iso
            (etaleSitePoint B S hS Z.1 z Z.2) (smallEtaleRingedTopos B S hS Z).O ρ).hom.app M) ≫
        (abelianFiberStalkUliftIso B S hS Z z).hom.app
          ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Z)).obj M) :=
  CategoryTheory.Functor.whiskerRightLeftIso_hom_app _ _ M

set_option maxHeartbeats 1600000 in
/-- The component of `AlgebraicGeometry.Space.moduleFiberStalkIso'`. -/
lemma moduleFiberStalkIso'_hom_app (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (moduleFiberStalkIso' B S hS Z z).hom.app M =
      (abelianFiberStalkUliftIso B S hS Z z).hom.app
        ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Z)).obj M) := by
  rfl

end FiberStalk

/-! ### The dictionary carries `θ` to the stalk comparison -/

section Compat

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (y : GeometricPoint B S hS Y.1)
  (ω : modulePushforward B S hS f ⋙ moduleUliftAbelianSheaf B S hS X ≅
    moduleUliftAbelianSheaf B S hS Y ⋙ smallEtaleAbelianDirectImage B S hS f)

/-- The dictionary on the source side: the geometric module fibre at `x̄` of the direct image,
forgotten and lifted, is the geometric stalk at `x̄` of the abelian direct image of the lifted
abelian sheaf, through a given identification `ω` of the two direct images. -/
def directImageFiberStalkIso :
    (modulePushforward B S hS f ⋙
        Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          (smallEtaleRingedTopos B S hS X).O) ⋙
        forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      moduleUliftAbelianSheaf B S hS Y ⋙
        (smallEtaleAbelianDirectImage B S hS f ⋙
          smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (modulePushforward B S hS f)
      (moduleFiberStalkIso' B S hS X (geometricPointMap f.hom y)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ω (smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)) ≪≫
    Functor.associator _ _ _

/-- The component of `AlgebraicGeometry.Space.directImageFiberStalkIso`, with the identity
`Stacks.sheafModuleFiberOfCommRingForget₂Iso` kept in front. -/
lemma directImageFiberStalkIso_hom_app (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (directImageFiberStalkIso B S hS f y ω).hom.app M =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map
          ((Stacks.sheafModuleFiberOfCommRingForget₂Iso
            (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
            (smallEtaleRingedTopos B S hS X).O).hom.app ((modulePushforward B S hS f).obj M)) ≫
        (abelianFiberStalkUliftIso B S hS X (geometricPointMap f.hom y)).hom.app
          ((modulePushforward B S hS f ⋙
            SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M) ≫
        (smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map (ω.hom.app M) :=
  rfl

/-- **The comparison `θ` between the underlying abelian fibres.**  The map
`AlgebraicGeometry.Space.directImageFiberMap` forgotten to abelian groups, typed (through the
identity isomorphisms `Stacks.sheafModuleFiberOfCommRingForget₂Iso` and
`Stacks.sheafModuleFiberOfCommRingRestrictScalarsForget₂Iso`) as a map between the fibres of the
underlying abelian sheaves. -/
def directImageFiberAbMap (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).sheafFiber.obj
        ((modulePushforward B S hS f ⋙
          SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M) ⟶
      (etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.obj
        ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M) :=
  (Stacks.sheafModuleFiberOfCommRingForget₂Iso
      (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
      (smallEtaleRingedTopos B S hS X).O).inv.app ((modulePushforward B S hS f).obj M) ≫
    (forget₂ _ AddCommGrpCat.{u}).map ((directImageFiberMap B S hS f y).app M) ≫
    (Stacks.sheafModuleFiberOfCommRingRestrictScalarsForget₂Iso
      (etaleSitePoint B S hS Y.1 y Y.2) (smallEtaleRingedTopos B S hS Y).O
      (smallEtaleStalkPullbackRingMap B S hS f y)).hom.app M

/-- **The dictionary carries `θ` to the stalk comparison, on abelian fibres, from two germ
formulas.**  If `θ` sends the germ at `u` of a section `t` of `f_*M` over a chart `U` of `X` to
the germ at `w` of `ψ t`, for every chart lift `(W, w, h)` of `u`, and the lift of `ψ` is the
restriction along `h` of the section `ω t`, read on `W` through the counit of the comparison
equivalence, then `θ` is carried to the stalk comparison.  The abelian side is
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImageStalkMap_germ`. -/
theorem directImageFiberAbMap_compat_of_germ (M : Modules.{u, u} B S hS Y.1 Y.2)
    (ψ : ∀ (U : SmallEtale B S hS X.1) (W : SmallEtale B S hS Y.1)
      (_ : (comparisonFunctor B S hS Y).obj W ⟶
        (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U)),
      ((modulePushforward B S hS f ⋙
        SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M).obj.obj (op U) ⟶
        ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M).obj.obj (op W))
    (hB : ∀ (U : SmallEtale B S hS X.1)
      (u : (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).fiber.obj U)
      (W : SmallEtale B S hS Y.1) (w : (etaleSitePoint B S hS Y.1 y Y.2).fiber.obj W)
      (h : (comparisonFunctor B S hS Y).obj W ⟶
        (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))
      (_ : (spacesEtaleSitePoint y).fiber.map h w =
        (spacesBaseChangeFiberIso B S hS f y).inv.app ((comparisonFunctor B S hS X).obj U) u),
      (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).toPresheafFiber U u
          ((modulePushforward B S hS f ⋙
            SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M).obj ≫
        directImageFiberAbMap B S hS f y M =
      ψ U W h ≫ (etaleSitePoint B S hS Y.1 y Y.2).toPresheafFiber W w
        ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M).obj)
    (hC : ∀ (U : SmallEtale B S hS X.1) (W : SmallEtale B S hS Y.1)
      (h : (comparisonFunctor B S hS Y).obj W ⟶
        (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U)),
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map (ψ U W h) =
        (ω.hom.app M).hom.app (op U) ≫
          ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj
            ((moduleUliftAbelianSheaf B S hS Y).obj M)).obj.map h.op ≫
          ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counitIso.hom.app
            ((moduleUliftAbelianSheaf B S hS Y).obj M)).hom.app (op W)) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map (directImageFiberAbMap B S hS f y M) ≫
        (abelianFiberStalkUliftIso B S hS Y y).hom.app
          ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M) =
      (abelianFiberStalkUliftIso B S hS X (geometricPointMap f.hom y)).hom.app
          ((modulePushforward B S hS f ⋙
            SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M) ≫
        (smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map (ω.hom.app M) ≫
        (smallEtaleAbelianDirectImageStalkMap B S hS f y).app
          ((moduleUliftAbelianSheaf B S hS Y).obj M) := by
  refine Stacks.sheafFiber_map_hom_ext AddCommGrpCat.uliftFunctor.{u + 1, u}
    (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
    ((modulePushforward B S hS f ⋙
      SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M) (fun U u ↦ ?_)
  exact (exists_chart_lift B S hS f y U u).elim fun W hW ↦ hW.elim fun w hw' ↦ hw'.elim
    fun h hw ↦ by
      -- the module side: `θ` on the germ, then the germ formula of the abelian dictionary at `ȳ`
      have l1 := (Functor.map_comp_assoc AddCommGrpCat.uliftFunctor.{u + 1, u} _ _ _).symm.trans
        ((congrArg (fun k ↦ AddCommGrpCat.uliftFunctor.{u + 1, u}.map k ≫
          (abelianFiberStalkUliftIso B S hS Y y).hom.app
            ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M))
          (hB U u W w h hw)).trans
        ((Functor.map_comp_assoc AddCommGrpCat.uliftFunctor.{u + 1, u} _ _ _).trans
          ((congrArg (fun k ↦ AddCommGrpCat.uliftFunctor.{u + 1, u}.map (ψ U W h) ≫ k)
            (uliftFunctor_map_toPresheafFiber_abelianFiberStalkUliftIso_hom B S hS Y y
              ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M) W w)).trans
          ((congrArg (· ≫ _) (hC U W h)).trans
            ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))))))
      -- the abelian side: the germ formula at `x̄`, naturality, and the abelian germ formula
      have hA := smallEtaleAbelianDirectImageStalkMap_germ B S hS f y
        ((moduleUliftAbelianSheaf B S hS Y).obj M) U u W w h hw
      have n1 := (etaleSitePointStalkFunctorIso B S hS X.1 (geometricPointMap f.hom y)
        X.2).hom.naturality_assoc
          ((sheafToPresheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).map
            (ω.hom.app M))
          ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app
            ((moduleUliftAbelianSheaf B S hS Y).obj M))
      have n2 := GrothendieckTopology.Point.toPresheafFiber_naturality_assoc
          (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          ((sheafToPresheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).map
            (ω.hom.app M)) U u
          ((etaleSitePointStalkFunctorIso B S hS X.1 (geometricPointMap f.hom y) X.2).hom.app
              ((smallEtaleAbelianDirectImage B S hS f).obj
                ((moduleUliftAbelianSheaf B S hS Y).obj M)).obj ≫
            (smallEtaleAbelianDirectImageStalkMap B S hS f y).app
              ((moduleUliftAbelianSheaf B S hS Y).obj M))
      have l2 := ((uliftFunctor_map_toPresheafFiber_abelianFiberStalkUliftIso_hom_assoc B S hS X
        (geometricPointMap f.hom y)
        ((modulePushforward B S hS f ⋙
          SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M) U u _).trans
        (Category.assoc _ _ _)).trans
        ((congrArg (fun k ↦ (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y)
          X.2).toPresheafFiber U u _ ≫ k) n1.symm).trans
        (n2.trans (congrArg (fun k ↦ (ω.hom.app M).hom.app (op U) ≫ k) hA)))
      exact l1.trans l2.symm

/-- **The dictionary carries `θ` to the stalk comparison.**  The square of
`AlgebraicGeometry.Space.isPullback_directImageFiberMap_of_compat` at `M`, from its form on
abelian fibres. -/
theorem directImageFiberMap_compat (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : AddCommGrpCat.uliftFunctor.{u + 1, u}.map (directImageFiberAbMap B S hS f y M) ≫
        (abelianFiberStalkUliftIso B S hS Y y).hom.app
          ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M) =
      (abelianFiberStalkUliftIso B S hS X (geometricPointMap f.hom y)).hom.app
          ((modulePushforward B S hS f ⋙
            SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M) ≫
        (smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map (ω.hom.app M) ≫
        (smallEtaleAbelianDirectImageStalkMap B S hS f y).app
          ((moduleUliftAbelianSheaf B S hS Y).obj M)) :
    (forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).map
        ((directImageFiberMap B S hS f y).app M) ≫
      (moduleFiberStalkIso B S hS Y y (smallEtaleStalkPullbackRingMap B S hS f y)).hom.app M =
    (directImageFiberStalkIso B S hS f y ω).hom.app M ≫
      (smallEtaleAbelianDirectImageStalkMap B S hS f y).app
        ((moduleUliftAbelianSheaf B S hS Y).obj M) := by
  rw [moduleFiberStalkIso_hom_app, directImageFiberStalkIso_hom_app, Functor.comp_map]
  have key := (AddCommGrpCat.uliftFunctor.{u + 1, u}.map_comp _ _).symm.trans
    ((congrArg AddCommGrpCat.uliftFunctor.{u + 1, u}.map
      (Iso.hom_inv_id_app_assoc (Stacks.sheafModuleFiberOfCommRingForget₂Iso
        (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
        (smallEtaleRingedTopos B S hS X).O) ((modulePushforward B S hS f).obj M)
        ((forget₂ _ AddCommGrpCat.{u}).map ((directImageFiberMap B S hS f y).app M) ≫
          (Stacks.sheafModuleFiberOfCommRingRestrictScalarsForget₂Iso
            (etaleSitePoint B S hS Y.1 y Y.2) (smallEtaleRingedTopos B S hS Y).O
            (smallEtaleStalkPullbackRingMap B S hS f y)).hom.app M))).trans
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.map_comp _ _))
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) key.symm)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hM).trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)))

end Compat

/-! ### The identification `ω` of the two direct images, and the unconditional dictionary -/

section Omega

/-- The restriction equivalence of Stacks 03G1 at lifted abelian coefficients, as an instance
(instance search for it times out). -/
local instance (priority := high) isEquivalence_comparisonPushforward_dictionary
    (Y : AlgebraicSpaces B S hS) :
    ((comparisonFunctor B S hS Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).IsEquivalence :=
  (smallEtaleAbelianSheafComparisonEquiv B S hS Y).isEquivalence_functor

/-- The abelian sheaf on the spaces-étale site underlying an `𝒪_Y`-module, with its coefficients
lifted, is the inverse of the comparison equivalence of Stacks 03G1 (at `u + 1`) applied to the
lifted abelian sheaf underlying the module: `CategoryTheory.Functor.sheafComposeTransposeIso` at
`AlgebraicGeometry.Space.moduleSpacesAbelianSheafRestrictionIso`. -/
def moduleSpacesUliftTransposeIso (Y : AlgebraicSpaces B S hS) :
    moduleSpacesAbelianSheaf B S hS Y ⋙
        sheafCompose (SpacesEtale.topology B S hS Y) AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y) ⋙
        sheafCompose (SmallEtale.topology B S hS Y.1) AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
        ((comparisonFunctor B S hS Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).inv :=
  Functor.sheafComposeTransposeIso (SmallEtale.topology B S hS Y.1)
    (SpacesEtale.topology B S hS Y) (comparisonFunctor B S hS Y)
    AddCommGrpCat.uliftFunctor.{u + 1, u} (moduleSpacesAbelianSheaf B S hS Y)
    (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y))
    (moduleSpacesAbelianSheafRestrictionIso B S hS Y)

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)

/-- **The two direct images agree on lifted abelian sheaves.**  The lifted abelian sheaf
underlying the module direct image `f_*M` is the abelian direct image of the lifted abelian sheaf
underlying `M`: the abelian sheaf underlying `f_*M` is the restriction of the spaces-étale
abelian sheaf of `M` along base change and the comparison functor
(`AlgebraicGeometry.Space.modulePushforwardSpacesAbelianSheafIso`), restriction commutes with
lifting on the nose, and the spaces-étale sheaf of `M`, lifted, is the inverse comparison
equivalence of the lift (`AlgebraicGeometry.Space.moduleSpacesUliftTransposeIso`). -/
def modulePushforwardUliftAbelianSheafIso :
    modulePushforward B S hS f ⋙ moduleUliftAbelianSheaf B S hS X ≅
      moduleUliftAbelianSheaf B S hS Y ⋙ smallEtaleAbelianDirectImage B S hS f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (modulePushforwardSpacesAbelianSheafIso B S hS f)
      (sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u}) ≪≫
    Functor.isoWhiskerRight (moduleSpacesUliftTransposeIso B S hS Y)
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
        (comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X))

/-- The component of `AlgebraicGeometry.Space.modulePushforwardUliftAbelianSheafIso` on the
sections over a chart `U` of `X`. -/
lemma modulePushforwardUliftAbelianSheafIso_hom_app_hom_app (M : Modules.{u, u} B S hS Y.1 Y.2)
    (U : SmallEtale B S hS X.1) :
    ((modulePushforwardUliftAbelianSheafIso B S hS f).hom.app M).hom.app (op U) =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map
          (((modulePushforwardSpacesAbelianSheafIso B S hS f).hom.app M).hom.app (op U)) ≫
        ((moduleSpacesUliftTransposeIso B S hS Y).hom.app M).hom.app
          (op ((spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))) :=
  Category.id_comp _

/-- The restriction along `h : W ⟶ U ×_X Y` of the spaces-étale abelian sheaf of `M`, typed
between the sections over `U` of its direct image and the sections over `W` of its restriction. -/
def directImageRestrictionMap (M : Modules.{u, u} B S hS Y.1 Y.2) (U : SmallEtale B S hS X.1)
    (W : SmallEtale B S hS Y.1)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U)) :
    ((moduleSpacesAbelianSheaf B S hS Y ⋙
        (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u}
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
        (comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).obj M).obj.obj
        (op U) ⟶
      ((moduleSpacesAbelianSheaf B S hS Y ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).obj M).obj.obj
        (op W) :=
  ((moduleSpacesAbelianSheaf B S hS Y).obj M).obj.map h.op

/-- **The section map `ψ` of the germ formula.**  A section of `f_*M` over a chart `U` of `X` is
a section of the spaces-étale abelian sheaf of `M` over `U ×_X Y`; restricted along
`h : W ⟶ U ×_X Y` and read on `W` through the counit of the comparison equivalence, it is a
section of `M` over `W`. -/
def directImageSectionMap (M : Modules.{u, u} B S hS Y.1 Y.2) (U : SmallEtale B S hS X.1)
    (W : SmallEtale B S hS Y.1)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U)) :
    ((modulePushforward B S hS f ⋙ SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj
        M).obj.obj (op U) ⟶
      ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M).obj.obj (op W) :=
  ((modulePushforwardSpacesAbelianSheafIso B S hS f).hom.app M).hom.app (op U) ≫
    directImageRestrictionMap B S hS f M U W h ≫
    ((moduleSpacesAbelianSheafRestrictionIso B S hS Y).hom.app M).hom.app (op W)

/-- **The section map `ψ` against `ω`.**  The lift of `ψ` is the component of `ω` followed by the
restriction along `h` and the counit of the comparison equivalence: naturality of
`AlgebraicGeometry.Space.moduleSpacesUliftTransposeIso` along `h`, and
`CategoryTheory.Functor.sheafPushforwardContinuous_map_sheafComposeTransposeIso_hom_app_comp`. -/
lemma uliftFunctor_map_directImageSectionMap (M : Modules.{u, u} B S hS Y.1 Y.2)
    (U : SmallEtale B S hS X.1) (W : SmallEtale B S hS Y.1)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U)) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map (directImageSectionMap B S hS f M U W h) =
      ((modulePushforwardUliftAbelianSheafIso B S hS f).hom.app M).hom.app (op U) ≫
        ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj
          ((moduleUliftAbelianSheaf B S hS Y).obj M)).obj.map h.op ≫
        ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counitIso.hom.app
          ((moduleUliftAbelianSheaf B S hS Y).obj M)).hom.app (op W) := by
  have e1 : AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        (((moduleSpacesAbelianSheafRestrictionIso B S hS Y).hom.app M).hom.app (op W)) =
      ((moduleSpacesUliftTransposeIso B S hS Y).hom.app M).hom.app
          (op ((comparisonFunctor B S hS Y).obj W)) ≫
        ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counitIso.hom.app
          ((moduleUliftAbelianSheaf B S hS Y).obj M)).hom.app (op W) :=
    (congrArg (fun k ↦ k.hom.app (op W))
      (Functor.sheafPushforwardContinuous_map_sheafComposeTransposeIso_hom_app_comp
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)
        (comparisonFunctor B S hS Y) AddCommGrpCat.uliftFunctor.{u + 1, u}
        (moduleSpacesAbelianSheaf B S hS Y)
        (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y))
        (moduleSpacesAbelianSheafRestrictionIso B S hS Y) M)).symm
  have e2 : AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        (directImageRestrictionMap B S hS f M U W h) ≫
        ((moduleSpacesUliftTransposeIso B S hS Y).hom.app M).hom.app
          (op ((comparisonFunctor B S hS Y).obj W)) =
      ((moduleSpacesUliftTransposeIso B S hS Y).hom.app M).hom.app
          (op ((spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))) ≫
        ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj
          ((moduleUliftAbelianSheaf B S hS Y).obj M)).obj.map h.op :=
    ((moduleSpacesUliftTransposeIso B S hS Y).hom.app M).hom.naturality h.op
  exact ((AddCommGrpCat.uliftFunctor.{u + 1, u}.map_comp _ _).trans
      (congrArg (_ ≫ ·) (AddCommGrpCat.uliftFunctor.{u + 1, u}.map_comp _ _))).trans
    ((congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) e1).trans (Category.assoc _ _ _).symm)).trans
      ((congrArg (_ ≫ ·) ((congrArg (· ≫ _) e2).trans (Category.assoc _ _ _))).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
          (modulePushforwardUliftAbelianSheafIso_hom_app_hom_app B S hS f M U).symm))))

/-- The germ of a section of `f_*M`, then `θ` on abelian fibres: the identity isomorphisms
around `θ` are the identity on elements. -/
lemma directImageFiberAbMap_toPresheafFiber_apply (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (U : SmallEtale B S hS X.1)
    (u : (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).fiber.obj U)
    (t : ((modulePushforward B S hS f ⋙
          SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M).obj.obj (op U)) :
    directImageFiberAbMap B S hS f y M
        ((etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).toPresheafFiber U u
          ((modulePushforward B S hS f ⋙
            SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M).obj t) =
      ((directImageFiberMap B S hS f y).app M).hom
        (Stacks.toPresheafModuleFiber (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          ((modulePushforward B S hS f).obj M).val U u t) :=
  rfl

/-- The germ map of the sheaf of modules `M` is the germ map of its underlying abelian sheaf. -/
lemma toPresheafModuleFiber_eq_toPresheafFiber (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (W : SmallEtale B S hS Y.1) (w : (etaleSitePoint B S hS Y.1 y Y.2).fiber.obj W)
    (x : ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M).obj.obj (op W)) :
    Stacks.toPresheafModuleFiber (etaleSitePoint B S hS Y.1 y Y.2) M.val W w x =
      (etaleSitePoint B S hS Y.1 y Y.2).toPresheafFiber W w
        ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M).obj x :=
  rfl

/-- The restriction maps of `AlgebraicGeometry.Space.moduleSpacesAbelianSheaf`, on elements, are
those of the inverse comparison equivalence applied to the sheaf of sets underlying the module. -/
lemma moduleSpacesAbelianSheaf_obj_map_apply (M : Modules.{u, u} B S hS Y.1 Y.2)
    (U : SmallEtale B S hS X.1)
    (W : SmallEtale B S hS Y.1)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))
    (z : ((moduleSpacesAbelianSheaf B S hS Y).obj M).obj.obj
      (op ((spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U)))) :
    ((moduleSpacesAbelianSheaf B S hS Y).obj M).obj.map h.op z =
      ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.map h.op z :=
  (rfl : ((moduleSpacesAbelianSheaf B S hS Y).obj M).obj.map h.op z =
      ((sheafCompose (SpacesEtale.topology B S hS Y) (forget AddCommGrpCat.{u})).obj
        ((moduleSpacesAbelianSheaf B S hS Y).obj M)).obj.map h.op z).trans rfl

/-- `AlgebraicGeometry.Space.directImageSectionMap` on elements, in the spelling of
`AlgebraicGeometry.Space.directImageFiberMap_germ`: the comparison of
`AlgebraicGeometry.Space.modulePushforwardSpacesAbelianSheafIso` is the identity on sections, and
`AlgebraicGeometry.Space.moduleSpacesAbelianSheafRestrictionIso` is the counit of the comparison
equivalence on sections. -/
lemma counit_inverse_map_apply_eq (M : Modules.{u, u} B S hS Y.1 Y.2)
    (U : SmallEtale B S hS X.1)
    (W : SmallEtale B S hS Y.1)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))
    (t : ((modulePushforward B S hS f).obj M).val.obj (op U)) :
    ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app
          (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).hom.app (op W)
        (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.map h.op t) =
      ((moduleSpacesAbelianSheafRestrictionIso B S hS Y).hom.app M).hom.app (op W)
        (directImageRestrictionMap B S hS f M U W h
          (((modulePushforwardSpacesAbelianSheafIso B S hS f).hom.app M).hom.app (op U) t)) :=
  (congrArg (fun x ↦ ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).hom.app (op W) x)
    (moduleSpacesAbelianSheaf_obj_map_apply B S hS f M U W h t)).symm.trans
  ((congrArg (fun x ↦ ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).hom.app (op W)
        (directImageRestrictionMap B S hS f M U W h x))
    (modulePushforwardSpacesAbelianSheafIso_hom_app_apply B S hS f M U t)).symm.trans
    (moduleSpacesAbelianSheafRestrictionIso_hom_app_apply B S hS Y M W
      (directImageRestrictionMap B S hS f M U W h
        (((modulePushforwardSpacesAbelianSheafIso B S hS f).hom.app M).hom.app (op U) t))).symm)

/-- The germ formula of `θ` on abelian fibres, on elements. -/
lemma directImageFiberAbMap_toPresheafFiber_apply_eq (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (U : SmallEtale B S hS X.1)
    (u : (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).fiber.obj U)
    (W : SmallEtale B S hS Y.1) (w : (etaleSitePoint B S hS Y.1 y Y.2).fiber.obj W)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))
    (hw : (spacesEtaleSitePoint y).fiber.map h w =
      (spacesBaseChangeFiberIso B S hS f y).inv.app ((comparisonFunctor B S hS X).obj U) u)
    (t : ((modulePushforward B S hS f ⋙
          SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M).obj.obj (op U)) :
    directImageFiberAbMap B S hS f y M
        ((etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).toPresheafFiber U u
          ((modulePushforward B S hS f ⋙
            SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M).obj t) =
      (etaleSitePoint B S hS Y.1 y Y.2).toPresheafFiber W w
        ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M).obj
        (((moduleSpacesAbelianSheafRestrictionIso B S hS Y).hom.app M).hom.app (op W)
          (directImageRestrictionMap B S hS f M U W h
            (((modulePushforwardSpacesAbelianSheafIso B S hS f).hom.app M).hom.app (op U) t))) :=
  (directImageFiberAbMap_toPresheafFiber_apply B S hS f y M U u t).trans
      ((directImageFiberMap_germ B S hS f y M U u W w h hw t).trans
        ((congrArg (Stacks.toPresheafModuleFiber (etaleSitePoint B S hS Y.1 y Y.2) M.val W w)
          (counit_inverse_map_apply_eq B S hS f M U W h t)).trans
          (toPresheafModuleFiber_eq_toPresheafFiber B S hS y M W w _)))

/-- **The germ formula of `θ` on abelian fibres.**  `θ` sends the germ at `u` of a section `t`
of `f_*M` over a chart `U` of `X` to the germ at `w` of `ψ t`, for every chart lift `(W, w, h)`
of `u`: `AlgebraicGeometry.Space.directImageFiberMap_germ`, with `ψ` read on sections by
`AlgebraicGeometry.Space.counit_inverse_map_apply_eq`.  The three maps composing `ψ` are passed
to `AddCommGrpCat.comp_eq_comp_comp_comp_of_apply` as opaque morphisms, so that no element of a
composite of them is ever computed. -/
lemma toPresheafFiber_directImageFiberAbMap (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (U : SmallEtale B S hS X.1)
    (u : (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).fiber.obj U)
    (W : SmallEtale B S hS Y.1) (w : (etaleSitePoint B S hS Y.1 y Y.2).fiber.obj W)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))
    (hw : (spacesEtaleSitePoint y).fiber.map h w =
      (spacesBaseChangeFiberIso B S hS f y).inv.app ((comparisonFunctor B S hS X).obj U) u) :
    (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).toPresheafFiber U u
          ((modulePushforward B S hS f ⋙
            SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj M).obj ≫
        directImageFiberAbMap B S hS f y M =
      directImageSectionMap B S hS f M U W h ≫ (etaleSitePoint B S hS Y.1 y Y.2).toPresheafFiber W w
        ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M).obj :=
  AddCommGrpCat.comp_eq_comp_comp_comp_of_apply
    ((etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).toPresheafFiber U u
      ((modulePushforward B S hS f ⋙ SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)).obj
        M).obj)
    (directImageFiberAbMap B S hS f y M)
    (((modulePushforwardSpacesAbelianSheafIso B S hS f).hom.app M).hom.app (op U))
    (directImageRestrictionMap B S hS f M U W h)
    (((moduleSpacesAbelianSheafRestrictionIso B S hS Y).hom.app M).hom.app (op W))
    ((etaleSitePoint B S hS Y.1 y Y.2).toPresheafFiber W w
      ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M).obj)
    (directImageFiberAbMap_toPresheafFiber_apply_eq B S hS f y M U u W w h hw)

/-- **The dictionary carries `θ` to the stalk comparison, unconditionally.**  For every
morphism `f : Y ⟶ X`, geometric point `ȳ` of `Y` and `𝒪_Y`-module `M`, the identifications
`AlgebraicGeometry.Space.directImageFiberStalkIso` (at
`AlgebraicGeometry.Space.modulePushforwardUliftAbelianSheafIso`) and
`AlgebraicGeometry.Space.moduleFiberStalkIso` carry
`θ = AlgebraicGeometry.Space.directImageFiberMap` to
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImageStalkMap`. -/
theorem directImageFiberMap_compat_ulift (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).map
        ((directImageFiberMap B S hS f y).app M) ≫
      (moduleFiberStalkIso B S hS Y y (smallEtaleStalkPullbackRingMap B S hS f y)).hom.app M =
    (directImageFiberStalkIso B S hS f y (modulePushforwardUliftAbelianSheafIso B S hS f)).hom.app
        M ≫
      (smallEtaleAbelianDirectImageStalkMap B S hS f y).app
        ((moduleUliftAbelianSheaf B S hS Y).obj M) :=
  directImageFiberMap_compat B S hS f y _ M
    (directImageFiberAbMap_compat_of_germ B S hS f y _ M (directImageSectionMap B S hS f M)
      (fun U u W w h hw ↦ toPresheafFiber_directImageFiberAbMap B S hS f y M U u W w h hw)
      (uliftFunctor_map_directImageSectionMap B S hS f M))

end Omega

namespace FormalGlueingSituation

variable {B S hS} (D : FormalGlueingSituation B S hS)

/-- **Stacks 0AER on geometric module fibres.**  Let `ȳ` be a geometric point of `Y` with image
`x̄`.  For every `𝒪_Y`-module `G` the square of geometric module fibres
```
(f_*G)_x̄           --θ_G-->            G_ȳ
    |                                   |
(f_*(j'_*(G|_V)))_x̄  --θ-->  (j'_*(G|_V))_ȳ
```
is cartesian, `θ = AlgebraicGeometry.Space.directImageFiberMap` and the vertical maps the fibres
of the unit `G ⟶ j'_*j'^*G` of the module adjunction along `j' = D.openImmersionOver`.

This is `AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_directImageFiberMap_of_compat`
with its dictionary supplied by `AlgebraicGeometry.Space.directImageFiberMap_compat_ulift`. -/
theorem isPullback_directImageFiberMap (y : GeometricPoint B S hS D.spaceY.1)
    (G : Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2) :
    IsPullback ((directImageFiberMap B S hS D.ambientMorphism y).app G)
      ((modulePushforward B S hS D.ambientMorphism ⋙
          Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y)
              D.spaceX.2) (smallEtaleRingedTopos B S hS D.spaceX).O).map
        ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app G))
      ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS D.spaceY.1 y D.spaceY.2)
            (smallEtaleRingedTopos B S hS D.spaceY).O ⋙
          ModuleCat.restrictScalars (smallEtaleStalkPullbackRingMap B S hS D.ambientMorphism y)).map
        ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app G))
      ((directImageFiberMap B S hS D.ambientMorphism y).app
        ((modulePullback B S hS D.openImmersionOver ⋙
          modulePushforward B S hS D.openImmersionOver).obj G)) :=
  D.isPullback_directImageFiberMap_of_compat y
    (directImageFiberStalkIso B S hS D.ambientMorphism y
      (modulePushforwardUliftAbelianSheafIso B S hS D.ambientMorphism))
    (moduleFiberStalkIso B S hS D.spaceY y
      (smallEtaleStalkPullbackRingMap B S hS D.ambientMorphism y))
    (directImageFiberMap_compat_ulift B S hS D.ambientMorphism y) G

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
