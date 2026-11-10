module

public import StacksFrontier.Algebra.Homology.RelativePullbackDerived
public import StacksFrontier.Algebra.Homology.RelativePullbackForget
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.BaseVanishingCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.LowDegreeSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiQuasicoherentSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology over a flat affine base change, as sections of the higher direct images

Let `f : T ⟶ S` be a quasi-compact and quasi-separated morphism of schemes, `𝓕` a
quasi-coherent `𝒪_T`-module, and

```
T_V --v'--> T
 |          |
 f_V        f
 v          v
 V  --v-->  S
```

a cartesian square with `V` affine and `v` flat. Then

`Hᵖ(T_V, v'^* 𝓕) ≅ Γ(V, R^p f_{V,*} v'^* 𝓕) ≅ Γ(V, v^* R^p f_* 𝓕)`,

the first isomorphism by [Stacks, Tag 01F4] part (2), the higher direct images of a
quasi-coherent module being quasi-coherent ([Stacks, Tag 01XJ]) and an affine scheme having no
higher cohomology of quasi-coherent modules ([Stacks, Tag 01XB]), and the second by flat base
change ([Stacks, Tag 02KH]). Both isomorphisms are given by explicit maps on injective
resolutions, `Stacks.Cohomology.RelativePullback.map`, and they are compatible with the pullback
maps along morphisms of such squares.

## Main definitions

* `Stacks.AlgebraicGeometry.HigherDirectImageSections.restriction`: the map
  `R^p f_* 𝓕 ⟶ v_* R^p f_{V,*} v'^* 𝓕` induced by the unit of `v'^* ⊣ v'_*`.
* `Stacks.AlgebraicGeometry.HigherDirectImageSections.baseChange`: its adjoint, the base change
  map `v^* R^p f_* 𝓕 ⟶ R^p f_{V,*} v'^* 𝓕` of [Stacks, Tag 02N7] in degree `p`.
* `Stacks.AlgebraicGeometry.HigherDirectImageSections.edge`: the edge map
  `Hᵖ(X, 𝓜) ⟶ Γ(Y, R^p a_* 𝓜)` of [Stacks, Tag 01F4].
* `Stacks.AlgebraicGeometry.HigherDirectImageSections.pullbackMap` and `directImageMap`: the
  pullback maps on cohomology and on higher direct images along a morphism of squares.
* `Stacks.AlgebraicGeometry.HigherDirectImageSections.pullbackModuleMap`: the `h`-map
  `v'₂^* 𝓕 ⟶ h_* v'₁^* 𝓕` of a pullback.
* `Stacks.AlgebraicGeometry.HigherDirectImageSections.cohomologyIso` and
  `abelianCohomologyIso`: `Hᵖ(T_V, v'^* 𝓕) ≅ Γ(V, v^* R^p f_* 𝓕)`, the second with the
  cohomology of the underlying abelian sheaf on the left.

## Main results

* `Stacks.AlgebraicGeometry.HigherDirectImageSections.isIso_baseChange`: the base change map is
  invertible for a cartesian square with `v` flat and `f` quasi-compact and quasi-separated,
  and `𝓕` quasi-coherent.
* `Stacks.AlgebraicGeometry.HigherDirectImageSections.isIso_edge`: the edge map is invertible
  over an affine base, for `a` quasi-compact and quasi-separated and `𝓜` quasi-coherent.
* `Stacks.AlgebraicGeometry.HigherDirectImageSections.pullbackMap_comp_edge`,
  `restriction_comp_directImageMap`, `baseChange_comp_directImageMap`: the compatibilities of
  the edge, restriction and base change maps with the pullback maps.
* `Stacks.AlgebraicGeometry.HigherDirectImageSections.pullbackMap_comp_cohomologyIso_hom` and
  `abelianPullback_comp_abelianCohomologyIso_hom`: **naturality** of the two isomorphisms with
  respect to morphisms of cartesian squares, against the pullback maps of [Stacks, Tag 01FA].

## Implementation notes

The pushforward and pullback functors of sheaves of modules on schemes,
`AlgebraicGeometry.Scheme.Modules.pushforward` and `AlgebraicGeometry.Scheme.Modules.pullback`,
are definitionally the ones of the underlying ringed spaces used by [Stacks, Tag 02KH]
(`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_baseChangeMap_of_flat`), adjunctions
included. The identification of the cohomology of a sheaf of modules with that of its underlying
abelian sheaf is `Stacks.Cohomology.RelativePullback.forgetMap`, computed on injective
resolutions, so that it is compatible with the pullback maps.

## References

* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry RingedSpaceModuleAdjunction
  Stacks.Cohomology.RelativePullback

universe u

namespace Stacks.AlgebraicGeometry.HigherDirectImageSections

attribute [local instance] HasDerivedCategory.standard

variable {T S V TV : Scheme.{u}}

/-- The pushforward of sheaves of modules along a flat morphism of schemes preserves injective
objects. -/
instance preservesInjectiveObjects_pushforward (g : TV ⟶ T) [Flat g] :
    (Scheme.Modules.pushforward g).PreservesInjectiveObjects :=
  have := preservesFiniteLimits_modulesPullback_of_flat g
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Scheme.Modules.pullbackPushforwardAdjunction g)

variable (f : T ⟶ S) (v : V ⟶ S) (v' : TV ⟶ T) (fV : TV ⟶ V)

/-- The identification of the two composite direct images of a commutative square,
`Stacks.Cohomology.FlatBaseChange.squarePushforwardIso`. -/
abbrev squareIso (w : v' ≫ f = fV ≫ v) :
    Scheme.Modules.pushforward v' ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward fV ⋙ Scheme.Modules.pushforward v :=
  Stacks.Cohomology.FlatBaseChange.squarePushforwardIso f.toLRSHom.toShHom fV.toLRSHom.toShHom
    v.toLRSHom.toShHom v'.toLRSHom.toShHom (congrArg (fun h => h.toLRSHom.toShHom) w)

/-- The transport of the pushforward along an equality of morphisms of schemes, read on the
underlying morphisms of ringed spaces, is `AlgebraicGeometry.Scheme.Modules.pushforwardCongr`. -/
theorem eqToIso_pushforward {X Y : Scheme.{u}} {a b : X ⟶ Y} (w : a = b) :
    eqToIso (congrArg (fun k : X ⟶ Y => Scheme.Modules.pushforward k) w) =
      Scheme.Modules.pushforwardCongr w := by
  subst w
  ext M U
  simp

/-- `Stacks.AlgebraicGeometry.HigherDirectImageSections.squareIso` in terms of the comparisons of
`AlgebraicGeometry.Scheme.Modules`. -/
theorem squareIso_eq (w : v' ≫ f = fV ≫ v) :
    squareIso f v v' fV w = Scheme.Modules.pushforwardComp v' f ≪≫
      Scheme.Modules.pushforwardCongr w ≪≫ (Scheme.Modules.pushforwardComp fV v).symm := by
  rw [← eqToIso_pushforward]
  rfl

variable [Flat v']

/-- **The restriction of the higher direct images to a base change**, `R^p f_* 𝓕 ⟶
v_* R^p f_{V,*} v'^* 𝓕`: the map of `Stacks.Cohomology.RelativePullback.map` attached to the unit
`𝓕 ⟶ v'_* v'^* 𝓕`. -/
def restriction (w : v' ≫ f = fV ≫ v) (F : T.Modules) (p : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerived p).obj F ⟶
      (Scheme.Modules.pushforward v).obj
        (((Scheme.Modules.pushforward fV).rightDerived p).obj
          ((Scheme.Modules.pullback v').obj F)) :=
  map (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward fV)
    (Scheme.Modules.pushforward v') (Scheme.Modules.pushforward v) (squareIso f v v' fV w)
    ((Scheme.Modules.pullbackPushforwardAdjunction v').unit.app F) p

/-- **The base change map in degree `p`**, `v^* R^p f_* 𝓕 ⟶ R^p f_{V,*} v'^* 𝓕`: the adjoint of
`Stacks.AlgebraicGeometry.HigherDirectImageSections.restriction`. -/
def baseChange (w : v' ≫ f = fV ≫ v) (F : T.Modules) (p : ℕ) :
    (Scheme.Modules.pullback v).obj (((Scheme.Modules.pushforward f).rightDerived p).obj F) ⟶
      ((Scheme.Modules.pushforward fV).rightDerived p).obj ((Scheme.Modules.pullback v').obj F) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction v).homEquiv _ _).symm
    (restriction f v v' fV w F p)

/-- The unit of `v^* ⊣ v_*` followed by `v_*` of the base change map is the restriction map. -/
private theorem unit_comp_map_baseChange (w : v' ≫ f = fV ≫ v) (F : T.Modules) (p : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction v).unit.app _ ≫
      (Scheme.Modules.pushforward v).map (baseChange f v v' fV w F p) =
        restriction f v v' fV w F p :=
  ((Scheme.Modules.pullbackPushforwardAdjunction v).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- **Flat base change in degree `p`** ([Stacks, Tag 02KH]): for a cartesian square with `v`
flat and `f` quasi-compact and quasi-separated, the base change map of a quasi-coherent module is
an isomorphism. -/
theorem isIso_baseChange (H : IsPullback v' fV f v) [Flat v] [QuasiCompact f] [QuasiSeparated f]
    (F : T.Modules) [F.IsQuasicoherent] (p : ℕ) :
    IsIso (baseChange f v v' fV H.w F p) := by
  have : (Scheme.Modules.pushforward f).Additive := Scheme.Modules.instAdditivePushforward f
  have : (Scheme.Modules.pushforward fV).Additive := Scheme.Modules.instAdditivePushforward fV
  have := preservesFiniteLimits_modulesPullback_of_flat v
  have := preservesFiniteLimits_modulesPullback_of_flat v'
  have : PreservesFiniteColimits (Scheme.Modules.pullback v) :=
    preservesFiniteColimits_modulePullback v.toLRSHom.toShHom
  have : PreservesFiniteColimits (Scheme.Modules.pullback v') :=
    preservesFiniteColimits_modulePullback v'.toLRSHom.toShHom
  refine isIso_homEquiv_symm_map_unit (A := T.Modules) (B := S.Modules) (C := TV.Modules)
    (D := V.Modules) (Scheme.Modules.pushforward f)
    (Scheme.Modules.pushforward fV) (Scheme.Modules.pullback v) (Scheme.Modules.pullback v')
    (Scheme.Modules.pullbackPushforwardAdjunction v)
    (Scheme.Modules.pullbackPushforwardAdjunction v') (squareIso f v v' fV H.w)
    (Stacks.Cohomology.FlatBaseChange.flatPullbackComparison v.toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isFlat_toShHom v)) F ?_ p
  exact Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_baseChangeMap_of_flat H F

section Sections

/-- The underlying abelian sheaf of a sheaf of modules on a scheme, as a functor out of the
category of `𝒪_X`-modules. -/
abbrev forget (X : Scheme.{u}) :
    X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf

/-- The underlying abelian sheaf functor of a scheme is additive. -/
instance (X : Scheme.{u}) : (forget X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

/-- The underlying abelian sheaf functor of a scheme preserves finite limits. -/
instance (X : Scheme.{u}) : PreservesFiniteLimits (forget X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))

/-- The underlying abelian sheaf functor of a scheme preserves finite colimits. -/
instance (X : Scheme.{u}) : PreservesFiniteColimits (forget X) :=
  Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits _ X.ringCatSheaf

/-- Global sections of an abelian sheaf on a scheme. -/
abbrev abSections (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)

/-- Global sections of a sheaf of modules on a scheme, as an abelian group. -/
abbrev sections (X : Scheme.{u}) : X.Modules ⥤ AddCommGrpCat.{u} := forget X ⋙ abSections X

end Sections

section Edge

variable {X Y : Scheme.{u}} (a : X ⟶ Y)

/-- **The edge map** `Hᵖ(X, 𝓜) ⟶ Γ(Y, R^p a_* 𝓜)` of [Stacks, Tag 01F4], as the map of
`Stacks.Cohomology.RelativePullback.map` attached to the identity of `𝓜`. -/
def edge (M : X.Modules) (p : ℕ) :
    ((sections X).rightDerived p).obj M ⟶
      (sections Y).obj (((Scheme.Modules.pushforward a).rightDerived p).obj M) :=
  map (sections X) (Scheme.Modules.pushforward a) (𝟭 _) (sections Y) (Iso.refl _) (𝟙 M) p

/-- **[Stacks, Tag 01F4] part (2) over an affine base**: for `a` quasi-compact and
quasi-separated with affine target and `𝓜` quasi-coherent, the edge map is an isomorphism. -/
@[sga "6 XII 3.3" "more general"]
theorem isIso_edge [IsAffine Y] [QuasiCompact a] [QuasiSeparated a] (M : X.Modules)
    [M.IsQuasicoherent] (p : ℕ) : IsIso (edge a M p) := by
  have hc := Stacks.Cohomology.LerayModules.isIso_cohomologyToSectionsHigherDirectImage_of_vanishing
    a.toLRSHom.toShHom M (fun q r hq => Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen Y
      (((Scheme.Modules.pushforward a).rightDerived r).obj M) ⊤ (isAffineOpen_top Y) q hq) p
  unfold Stacks.Cohomology.LerayModules.cohomologyToSectionsHigherDirectImage at hc
  have h₁ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (Iso.isIso_hom _) hc
  have h₂ := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom _) h₁
  have hφ : IsIso ((NatTrans.mapHomologicalComplex
      (Iso.refl _ : 𝟭 X.Modules ⋙ sections X ≅ Scheme.Modules.pushforward a ⋙ sections Y).hom
      (ComplexShape.up ℕ)).app (injectiveResolution M).cocomplex) :=
    Iso.isIso_hom ((NatIso.mapHomologicalComplex _ (ComplexShape.up ℕ)).app _)
  have h := map_id_eq (sections X) (Scheme.Modules.pushforward a) (sections Y) (Iso.refl _) M p
  unfold edge
  rw [h]
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso'
    (@Functor.map_isIso _ _ _ _ _ _ (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p)
      _ hφ)
    (IsIso.comp_isIso' h₂ inferInstance))

end Edge

section Naturality

variable {V₁ V₂ T₁ T₂ : Scheme.{u}} (φ : V₁ ⟶ V₂) (h : T₁ ⟶ T₂) (f₁ : T₁ ⟶ V₁) (f₂ : T₂ ⟶ V₂)

/-- Global sections over the target of the comparison of the two composite direct images of a
commutative square of ringed spaces are the identity. -/
theorem _root_.Stacks.Cohomology.FlatBaseChange.secF_map_squarePushforwardIso_hom_app
    {X X' S S' : RingedSpace.{u, u}}
    [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X))]
    [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X'))]
    [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing S))]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g)
    (Z : _root_.SheafOfModules.{u} (structureSheafRing X')) :
    (secF (structureSheafRing S) ⊤).map
      ((Stacks.Cohomology.FlatBaseChange.squarePushforwardIso f f' g g' comm).hom.app Z) = 𝟙 _ := by
  have L : ∀ {k₁ k₂ : X' ⟶ S} (hk : k₁ = k₂),
      (secF (structureSheafRing S) ⊤).map ((eqToHom (congrArg modulePushforward hk)).app Z) =
        𝟙 _ := by
    intro k₁ k₂ hk
    subst hk
    simp
  unfold Stacks.Cohomology.FlatBaseChange.squarePushforwardIso
  rw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    modulePushforwardComp_hom_app, Iso.symm_hom, modulePushforwardComp_inv_app, eqToIso.hom,
    L comm]
  exact ConcreteCategory.hom_ext _ _ (fun _ => rfl)

/-- Global sections over `V₂` of the comparison `squareIso` of the two composite direct images
of a commutative square of schemes are the identity. -/
theorem sections_map_squareIso_hom_app (w : h ≫ f₂ = f₁ ≫ φ) (Z : T₁.Modules) :
    (sections V₂).map ((squareIso f₂ φ h f₁ w).hom.app Z) = 𝟙 _ :=
  Stacks.Cohomology.FlatBaseChange.secF_map_squarePushforwardIso_hom_app _ _ _ _ _ Z

variable [Flat h]

/-- **The pullback map on cohomology** `Hᵖ(T₂, 𝓜) ⟶ Hᵖ(T₁, 𝓝)` along `h : T₁ ⟶ T₂` attached to
`ψ : 𝓜 ⟶ h_* 𝓝`, [Stacks, Tag 01FA], as the map of `Stacks.Cohomology.RelativePullback.map`. -/
def pullbackMap {M : T₂.Modules} {N : T₁.Modules} (ψ : M ⟶ (Scheme.Modules.pushforward h).obj N)
    (p : ℕ) : ((sections T₂).rightDerived p).obj M ⟶ ((sections T₁).rightDerived p).obj N :=
  map (sections T₂) (sections T₁) (Scheme.Modules.pushforward h) (𝟭 _) (Iso.refl _) ψ p

/-- **The relative pullback map on higher direct images** `R^p f_{2,*} 𝓜 ⟶ φ_* R^p f_{1,*} 𝓝`
attached to `ψ : 𝓜 ⟶ h_* 𝓝`, for a commutative square `h ≫ f₂ = f₁ ≫ φ`. -/
def directImageMap (w : h ≫ f₂ = f₁ ≫ φ) {M : T₂.Modules} {N : T₁.Modules}
    (ψ : M ⟶ (Scheme.Modules.pushforward h).obj N) (p : ℕ) :
    ((Scheme.Modules.pushforward f₂).rightDerived p).obj M ⟶
      (Scheme.Modules.pushforward φ).obj (((Scheme.Modules.pushforward f₁).rightDerived p).obj N) :=
  map (Scheme.Modules.pushforward f₂) (Scheme.Modules.pushforward f₁)
    (Scheme.Modules.pushforward h) (Scheme.Modules.pushforward φ) (squareIso f₂ φ h f₁ w) ψ p

/-- **The edge maps are compatible with the pullback maps**: pulling a class back along `h` and
then taking its section of `R^p f_{1,*}` is taking its section of `R^p f_{2,*}` and then applying
the relative pullback map. -/
theorem pullbackMap_comp_edge (w : h ≫ f₂ = f₁ ≫ φ) {M : T₂.Modules} {N : T₁.Modules}
    (ψ : M ⟶ (Scheme.Modules.pushforward h).obj N) (p : ℕ) :
    pullbackMap h ψ p ≫ edge f₁ N p =
      edge f₂ M p ≫ (sections V₂).map (directImageMap φ h f₁ f₂ w ψ p) := by
  have hA := map_comp (sections T₂) (sections T₁) (Scheme.Modules.pushforward f₁)
    (Scheme.Modules.pushforward h) (𝟭 _) (𝟭 _) (sections V₁) (Scheme.Modules.pushforward h)
    (sections V₁) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (fun Z => ConcreteCategory.hom_ext _ _ (fun _ => rfl)) ψ (𝟙 N) p
  have hB := map_comp (sections T₂) (Scheme.Modules.pushforward f₂)
    (Scheme.Modules.pushforward f₁) (𝟭 _) (sections V₂) (Scheme.Modules.pushforward h)
    (Scheme.Modules.pushforward φ) (Scheme.Modules.pushforward h) (sections V₁) (Iso.refl _)
    (squareIso f₂ φ h f₁ w) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (fun Z => by
      rw [sections_map_squareIso_hom_app]
      exact ConcreteCategory.hom_ext _ _ (fun _ => rfl))
    (𝟙 M) ψ p
  have hu₁ : ψ ≫ (Scheme.Modules.pushforward h).map (𝟙 N) ≫
      (Iso.refl (𝟭 T₁.Modules ⋙ Scheme.Modules.pushforward h)).hom.app N = ψ := by
    simp
  have hu₂ : 𝟙 M ≫ (𝟭 T₂.Modules).map ψ ≫
      (Iso.refl (Scheme.Modules.pushforward h ⋙ 𝟭 T₂.Modules)).hom.app N = ψ := by
    simp
  rw [hu₁] at hA
  rw [hu₂] at hB
  refine Eq.trans ?_ (hA.symm.trans (hB.trans ?_))
  · simp only [Functor.id_map, Iso.refl_hom, NatTrans.id_app]
    rfl
  · exact congrArg (fun t => edge f₂ M p ≫ t) (Category.comp_id _)

end Naturality

section BaseChangeNaturality

variable {T S V₁ V₂ T₁ T₂ : Scheme.{u}} (f : T ⟶ S) (v₁ : V₁ ⟶ S) (v₂ : V₂ ⟶ S)
  (v'₁ : T₁ ⟶ T) (v'₂ : T₂ ⟶ T) (f₁ : T₁ ⟶ V₁) (f₂ : T₂ ⟶ V₂) (φ : V₁ ⟶ V₂) (h : T₁ ⟶ T₂)

/-- **The `h`-map of a pullback**, `v'₂^* 𝓕 ⟶ h_* v'₁^* 𝓕` for `h ≫ v'₂ = v'₁`: the unit of
`h^* ⊣ h_*` followed by the identification `h^* v'₂^* 𝓕 ≅ v'₁^* 𝓕`. -/
def pullbackModuleMap (hh : h ≫ v'₂ = v'₁) (F : T.Modules) :
    (Scheme.Modules.pullback v'₂).obj F ⟶
      (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pullback v'₁).obj F) :=
  (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app _ ≫
    (Scheme.Modules.pushforward h).map (Stacks.Sites.pullbackCompIso F h v'₂ v'₁ hh).hom

/-- The units of the pullback-pushforward adjunctions along `v'₂` and along `v'₁ = h ≫ v'₂` are
related by the `h`-map. -/
theorem unit_comp_pushforward_map_pullbackModuleMap (hh : h ≫ v'₂ = v'₁) (F : T.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction v'₂).unit.app F ≫
        (Scheme.Modules.pushforward v'₂).map (pullbackModuleMap v'₁ v'₂ h hh F) ≫
          (Scheme.Modules.pushforwardComp h v'₂ ≪≫ Scheme.Modules.pushforwardCongr hh).hom.app _ =
      (Scheme.Modules.pullbackPushforwardAdjunction v'₁).unit.app F := by
  subst hh
  have hu := AlgebraicGeometry.pullbackComp_unit h v'₂ F
  have hc : (Scheme.Modules.pushforwardCongr (rfl : h ≫ v'₂ = h ≫ v'₂)).hom = 𝟙 _ := by
    ext M U
    simp only [Scheme.Modules.pushforwardCongr_hom_app_app, eqToHom_refl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  have : Mono ((Scheme.Modules.pushforward (h ≫ v'₂)).map
      ((Scheme.Modules.pullbackComp h v'₂).inv.app F)) :=
    inferInstanceAs (Mono ((Scheme.Modules.pushforward (h ≫ v'₂)).mapIso
      ((Scheme.Modules.pullbackComp h v'₂).app F)).symm.hom)
  rw [Iso.trans_hom, hc, Category.comp_id, ← cancel_mono ((Scheme.Modules.pushforward
    (h ≫ v'₂)).map ((Scheme.Modules.pullbackComp h v'₂).inv.app F)), hu]
  simp only [pullbackModuleMap, Stacks.Sites.pullbackCompIso_hom, CategoryTheory.Functor.map_comp,
    Category.assoc]
  congr 2
  have hn := (Scheme.Modules.pushforwardComp h v'₂).hom.naturality
    ((Scheme.Modules.pullbackComp h v'₂).inv.app F)
  simp only [Functor.comp_map] at hn
  rw [← hn, Stacks.Sites.pullbackCongr_rfl_hom_app, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
  simp

variable [Flat h] [Flat v'₁] [Flat v'₂]

/-- **The restriction maps compose**: for a morphism `(h, φ)` of cartesian squares over `f`,
restricting `R^p f_* 𝓕` to `V₂` and then along `φ` is restricting it to `V₁`. -/
theorem restriction_comp_directImageMap (w₁ : v'₁ ≫ f = f₁ ≫ v₁) (w₂ : v'₂ ≫ f = f₂ ≫ v₂)
    (hφ : h ≫ f₂ = f₁ ≫ φ) (hv : φ ≫ v₂ = v₁) (hh : h ≫ v'₂ = v'₁) (F : T.Modules) (p : ℕ) :
    restriction f v₂ v'₂ f₂ w₂ F p ≫
        (Scheme.Modules.pushforward v₂).map
          (directImageMap φ h f₁ f₂ hφ (pullbackModuleMap v'₁ v'₂ h hh F) p) ≫
        (Scheme.Modules.pushforwardComp φ v₂ ≪≫ Scheme.Modules.pushforwardCongr hv).hom.app _ =
      restriction f v₁ v'₁ f₁ w₁ F p := by
  have hc := map_comp (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward f₂)
    (Scheme.Modules.pushforward f₁) (Scheme.Modules.pushforward v'₂)
    (Scheme.Modules.pushforward v₂) (Scheme.Modules.pushforward h)
    (Scheme.Modules.pushforward φ) (Scheme.Modules.pushforward v'₁)
    (Scheme.Modules.pushforward v₁) (squareIso f v₂ v'₂ f₂ w₂) (squareIso f₂ φ h f₁ hφ)
    (squareIso f v₁ v'₁ f₁ w₁)
    (Scheme.Modules.pushforwardComp h v'₂ ≪≫ Scheme.Modules.pushforwardCongr hh)
    (Scheme.Modules.pushforwardComp φ v₂ ≪≫ Scheme.Modules.pushforwardCongr hv)
    (fun Z => by
      rw [squareIso_eq, squareIso_eq, squareIso_eq]
      ext U
      simp only [Functor.comp_obj, Scheme.Modules.pushforward_obj_obj, Iso.trans_hom,
        Iso.symm_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app, Scheme.Hom.comp_base,
        TopologicalSpace.Opens.map_comp_obj, Scheme.Modules.pushforwardComp_hom_app_app,
        Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
        Category.comp_id, Category.id_comp, Iso.trans_inv, Functor.map_comp, Category.assoc,
        Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardCongr_inv_app_app,
        Scheme.Modules.pushforward_obj_presheaf_map, AddCommGrpCat.hom_comp]
      rename_i x
      simp only [← AddCommGrpCat.hom_comp, ← CategoryTheory.Functor.map_comp, ← op_comp]
      congr 3)
    ((Scheme.Modules.pullbackPushforwardAdjunction v'₂).unit.app F)
    (pullbackModuleMap v'₁ v'₂ h hh F) p
  rw [unit_comp_pushforward_map_pullbackModuleMap] at hc
  exact hc.symm

/-- **The base change maps are compatible with the relative pullback maps**: for a morphism
`(h, φ)` of cartesian squares over `f`, the base change map over `V₂` followed by the relative
pullback map along `(h, φ)` is the `φ`-map of `R^p f_* 𝓕` followed by `φ_*` of the base change map
over `V₁`. -/
theorem baseChange_comp_directImageMap (w₁ : v'₁ ≫ f = f₁ ≫ v₁) (w₂ : v'₂ ≫ f = f₂ ≫ v₂)
    (hφ : h ≫ f₂ = f₁ ≫ φ) (hv : φ ≫ v₂ = v₁) (hh : h ≫ v'₂ = v'₁) (F : T.Modules) (p : ℕ) :
    baseChange f v₂ v'₂ f₂ w₂ F p ≫
        directImageMap φ h f₁ f₂ hφ (pullbackModuleMap v'₁ v'₂ h hh F) p =
      pullbackModuleMap v₁ v₂ φ hv (((Scheme.Modules.pushforward f).rightDerived p).obj F) ≫
        (Scheme.Modules.pushforward φ).map (baseChange f v₁ v'₁ f₁ w₁ F p) := by
  let adj₂ := Scheme.Modules.pullbackPushforwardAdjunction v₂
  let ηK := Scheme.Modules.pushforwardComp φ v₂ ≪≫ Scheme.Modules.pushforwardCongr hv
  have hR := restriction_comp_directImageMap f v₁ v₂ v'₁ v'₂ f₁ f₂ φ h w₁ w₂ hφ hv hh F p
  have hU := unit_comp_pushforward_map_pullbackModuleMap v₁ v₂ φ hv
    (((Scheme.Modules.pushforward f).rightDerived p).obj F)
  have : ∀ X, Mono (ηK.hom.app X) := fun X => inferInstanceAs (Mono (ηK.app X).hom)
  apply (adj₂.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
    ← Category.assoc, unit_comp_map_baseChange, CategoryTheory.Functor.map_comp,
    ← cancel_mono (ηK.hom.app _),
    Category.assoc, Category.assoc, hR]
  have hn := ηK.hom.naturality (baseChange f v₁ v'₁ f₁ w₁ F p)
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [hn, reassoc_of% hU, unit_comp_map_baseChange]

end BaseChangeNaturality

section Assembly

variable {T S V TV : Scheme.{u}} {f : T ⟶ S} {v : V ⟶ S} {v' : TV ⟶ T} {fV : TV ⟶ V}

/-- **Cohomology over a flat affine base change is sections of the higher direct images.** For a
cartesian square with `v` flat and `V` affine, `f` quasi-compact and quasi-separated, and `𝓕`
quasi-coherent, `Hᵖ(T_V, v'^* 𝓕) ≅ Γ(V, v^* R^p f_* 𝓕)`: the edge map of [Stacks, Tag 01F4]
followed by the inverse of the base change map of [Stacks, Tag 02KH]. -/
def cohomologyIso (H : IsPullback v' fV f v) [Flat v] [IsAffine V] [QuasiCompact f]
    [QuasiSeparated f] (F : T.Modules) [F.IsQuasicoherent] (p : ℕ) :
    ((sections TV).rightDerived p).obj ((Scheme.Modules.pullback v').obj F) ≅
      (sections V).obj ((Scheme.Modules.pullback v).obj
        (((Scheme.Modules.pushforward f).rightDerived p).obj F)) :=
  haveI : Flat v' := MorphismProperty.of_isPullback H.flip inferInstance
  haveI : QuasiCompact fV := MorphismProperty.of_isPullback H inferInstance
  haveI : QuasiSeparated fV := MorphismProperty.of_isPullback H inferInstance
  haveI := isIso_edge fV ((Scheme.Modules.pullback v').obj F) p
  haveI := isIso_baseChange f v v' fV H F p
  asIso (edge fV ((Scheme.Modules.pullback v').obj F) p) ≪≫
    (sections V).mapIso (asIso (baseChange f v v' fV H.w F p)).symm

/-- The forward map of `cohomologyIso` is the edge map followed by the sections of the inverse
of the base change map. -/
theorem cohomologyIso_hom (H : IsPullback v' fV f v) [Flat v] [IsAffine V] [QuasiCompact f]
    [QuasiSeparated f] (F : T.Modules) [F.IsQuasicoherent] (p : ℕ) :
    haveI : Flat v' := MorphismProperty.of_isPullback H.flip inferInstance
    haveI := isIso_baseChange f v v' fV H F p
    (cohomologyIso H F p).hom = edge fV ((Scheme.Modules.pullback v').obj F) p ≫
      (sections V).map (inv (baseChange f v v' fV H.w F p)) := by
  simp [cohomologyIso]

end Assembly

section AssemblyNaturality

variable {T S V₁ V₂ T₁ T₂ : Scheme.{u}} {f : T ⟶ S} {v₁ : V₁ ⟶ S} {v₂ : V₂ ⟶ S}
  {v'₁ : T₁ ⟶ T} {v'₂ : T₂ ⟶ T} {f₁ : T₁ ⟶ V₁} {f₂ : T₂ ⟶ V₂} {φ : V₁ ⟶ V₂} {h : T₁ ⟶ T₂}

/-- **`Stacks.AlgebraicGeometry.HigherDirectImageSections.cohomologyIso` is natural**: for a
morphism `(h, φ)` of cartesian squares over `f`, it carries the pullback map on cohomology along
`h` ([Stacks, Tag 01FA]) to the pullback of sections of `v^* R^p f_* 𝓕` along `φ`. -/
theorem pullbackMap_comp_cohomologyIso_hom (H₁ : IsPullback v'₁ f₁ f v₁)
    (H₂ : IsPullback v'₂ f₂ f v₂) [Flat v₁] [Flat v₂] [IsAffine V₁] [IsAffine V₂]
    [QuasiCompact f] [QuasiSeparated f] [Flat h] (hφ : h ≫ f₂ = f₁ ≫ φ) (hv : φ ≫ v₂ = v₁)
    (hh : h ≫ v'₂ = v'₁) (F : T.Modules) [F.IsQuasicoherent] (p : ℕ) :
    pullbackMap h (pullbackModuleMap v'₁ v'₂ h hh F) p ≫ (cohomologyIso H₁ F p).hom =
      (cohomologyIso H₂ F p).hom ≫ (sections V₂).map
        (pullbackModuleMap v₁ v₂ φ hv (((Scheme.Modules.pushforward f).rightDerived p).obj F)) := by
  have : Flat v'₁ := MorphismProperty.of_isPullback H₁.flip inferInstance
  have : Flat v'₂ := MorphismProperty.of_isPullback H₂.flip inferInstance
  have := isIso_baseChange f v₁ v'₁ f₁ H₁ F p
  have := isIso_baseChange f v₂ v'₂ f₂ H₂ F p
  have hN := baseChange_comp_directImageMap f v₁ v₂ v'₁ v'₂ f₁ f₂ φ h H₁.w H₂.w hφ hv hh F p
  have hD : directImageMap φ h f₁ f₂ hφ (pullbackModuleMap v'₁ v'₂ h hh F) p ≫
      (Scheme.Modules.pushforward φ).map (inv (baseChange f v₁ v'₁ f₁ H₁.w F p)) =
      inv (baseChange f v₂ v'₂ f₂ H₂.w F p) ≫
        pullbackModuleMap v₁ v₂ φ hv (((Scheme.Modules.pushforward f).rightDerived p).obj F) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hN, Category.assoc,
      ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  simp only [cohomologyIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom,
    asIso_inv]
  rw [← Category.assoc, pullbackMap_comp_edge φ h f₁ f₂ hφ]
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine congrArg (edge f₂ ((Scheme.Modules.pullback v'₂).obj F) p ≫ ·) ?_
  exact ((sections V₂).map_comp _ _).symm.trans
    ((congrArg (sections V₂).map hD).trans ((sections V₂).map_comp _ _))

end AssemblyNaturality

section Abelian

attribute [local instance] HasDerivedCategory.standard in
/-- The cohomology of a sheaf of modules on a scheme agrees with the cohomology of its underlying
abelian sheaf ([Stacks, Tag 03FD]), through the comparison of resolutions
`Stacks.Cohomology.RelativePullback.forgetMap`. -/
instance isIso_forgetMap (X : Scheme.{u}) (M : X.Modules) (p : ℕ) :
    IsIso (forgetMap (forget X) (abSections X) M p) :=
  Stacks.Cohomology.RelativePullback.isIso_forgetMap (forget X) (abSections X)
    (fun I hI =>
      Stacks.Cohomology.ModulePushforwardComparison.rightAcyclic_sections_toSheaf_obj_of_injective
        (X := X.toRingedSpace) ⊤ I hI) M p

variable {T S V TV : Scheme.{u}} {f : T ⟶ S} {v : V ⟶ S} {v' : TV ⟶ T} {fV : TV ⟶ V}

/-- **Cohomology over a flat affine base change is sections of the higher direct images**, with
abelian sheaf cohomology on the source: `Hᵖ(T_V, v'^* 𝓕) ≅ Γ(V, v^* R^p f_* 𝓕)`, where the
left side is the cohomology of the underlying abelian sheaf of `v'^* 𝓕`. -/
def abelianCohomologyIso (H : IsPullback v' fV f v) [Flat v] [IsAffine V] [QuasiCompact f]
    [QuasiSeparated f] (F : T.Modules) [F.IsQuasicoherent] (p : ℕ) :
    ((abSections TV).rightDerived p).obj ((forget TV).obj ((Scheme.Modules.pullback v').obj F)) ≅
      (sections V).obj ((Scheme.Modules.pullback v).obj
        (((Scheme.Modules.pushforward f).rightDerived p).obj F)) :=
  (asIso (forgetMap (forget TV) (abSections TV) ((Scheme.Modules.pullback v').obj F) p)).symm ≪≫
    cohomologyIso H F p

variable {V₁ V₂ T₁ T₂ : Scheme.{u}} {v₁ : V₁ ⟶ S} {v₂ : V₂ ⟶ S}
  {v'₁ : T₁ ⟶ T} {v'₂ : T₂ ⟶ T} {f₁ : T₁ ⟶ V₁} {f₂ : T₂ ⟶ V₂} {φ : V₁ ⟶ V₂} {h : T₁ ⟶ T₂}

/-- **`Stacks.AlgebraicGeometry.HigherDirectImageSections.abelianCohomologyIso` is natural**: for
a morphism `(h, φ)` of cartesian squares over `f`, it carries the pullback map of [Stacks,
Tag 01FA] on abelian sheaf cohomology along `h`, attached to the `h`-map of `𝓕`, to the pullback
of sections of `v^* R^p f_* 𝓕` along `φ`. -/
theorem abelianPullback_comp_abelianCohomologyIso_hom (H₁ : IsPullback v'₁ f₁ f v₁)
    (H₂ : IsPullback v'₂ f₂ f v₂) [Flat v₁] [Flat v₂] [IsAffine V₁] [IsAffine V₂]
    [QuasiCompact f] [QuasiSeparated f] [Flat h] (hφ : h ≫ f₂ = f₁ ≫ φ) (hv : φ ≫ v₂ = v₁)
    (hh : h ≫ v'₂ = v'₁) (F : T.Modules) [F.IsQuasicoherent] (p : ℕ) :
    ((abSections T₂).rightDerived p).map
        ((forget T₂).map (pullbackModuleMap v'₁ v'₂ h hh F)) ≫
      (Stacks.Cohomology.LerayLowDegree.abelianEdgeMap.{u, 0} h.base p).app
        ((forget T₁).obj ((Scheme.Modules.pullback v'₁).obj F)) ≫
      (abelianCohomologyIso H₁ F p).hom =
    (abelianCohomologyIso H₂ F p).hom ≫ (sections V₂).map
      (pullbackModuleMap v₁ v₂ φ hv (((Scheme.Modules.pushforward f).rightDerived p).obj F)) := by
  have hc := map_comp_forgetMap (forget T₁) (forget T₂) (Scheme.Modules.pushforward h)
    (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} h.base) (Iso.refl _)
    (abSections T₂) (Iso.refl _) (fun _ => rfl) (pullbackModuleMap v'₁ v'₂ h hh F) p
  have hn := pullbackMap_comp_cohomologyIso_hom H₁ H₂ hφ hv hh F p
  have hc' : pullbackMap h (pullbackModuleMap v'₁ v'₂ h hh F) p ≫
      forgetMap (forget T₁) (abSections T₁) ((Scheme.Modules.pullback v'₁).obj F) p =
      forgetMap (forget T₂) (abSections T₂) ((Scheme.Modules.pullback v'₂).obj F) p ≫
        ((abSections T₂).rightDerived p).map
          ((forget T₂).map (pullbackModuleMap v'₁ v'₂ h hh F)) ≫
        (Stacks.Cohomology.LerayLowDegree.abelianEdgeMap.{u, 0} h.base p).app
          ((forget T₁).obj ((Scheme.Modules.pullback v'₁).obj F)) := by
    simp only [Iso.refl_hom, NatTrans.id_app] at hc
    exact hc
  have key : ∀ {C : Type (u + 1)} [Category.{u} C] {P Q R S' W Z : C} (pb : P ⟶ R)
      (A : P ⟶ Q) (B : R ⟶ S') [IsIso A] [IsIso B] (X : Q ⟶ S') (c₁ : R ⟶ W) (c₂ : P ⟶ Z)
      (g : Z ⟶ W), pb ≫ B = A ≫ X → pb ≫ c₁ = c₂ ≫ g → X ≫ inv B ≫ c₁ = inv A ≫ c₂ ≫ g := by
    intro C _ P Q R S' W Z pb A B _ _ X c₁ c₂ g h₁ h₂
    rw [IsIso.eq_inv_comp, ← reassoc_of% h₁, IsIso.hom_inv_id_assoc, h₂]
  simp only [abelianCohomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  exact key _ _ _ _ _ _ _ hc' hn

end Abelian

end Stacks.AlgebraicGeometry.HigherDirectImageSections
