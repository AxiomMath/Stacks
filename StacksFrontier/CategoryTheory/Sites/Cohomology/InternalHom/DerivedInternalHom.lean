module

public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Localization.Opposite
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelianSmall
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.QuasiIsoInvariance
import StacksCore.Tactic.StacksAttribute

/-! # The derived internal Hom on a ringed site

Let `(C, O)` be a ringed site. This file constructs the derived internal Hom bifunctor

`RSheafHom(-, -) : D(Mod(O))ᵒᵖ ⥤ D(Mod(O)) ⥤ D(Mod(O))`

together with the isomorphism identifying its value at `(K, M)` with the class of the ordinary
internal Hom complex `SheafHom(K, M)` whenever the *target* `M` is K-injective — for an
arbitrary source — naturally in both variables.

The construction is the one of the Stacks project: a complex of `O`-modules has a functorial
K-injective resolution, because sheaves of `O`-modules form a Grothendieck abelian category
(Stacks 079P, `Stacks.Injectives.kInjectiveResolutionFunctor`), and the internal Hom complex
into a K-injective complex takes quasi-isomorphisms in either variable to
quasi-isomorphisms (Stacks 0A95, `AlgebraicGeometry.RingedSite.homMap_quasiIso`). So the
bifunctor `(K, M) ↦ Q(SheafHom(K, R M))`, with `R` the resolution functor, inverts
quasi-isomorphisms in both variables simultaneously and descends along the pair of
localization functors `Q.op` and `Q`. The comparison isomorphism is the lifting datum of that
descent, composed with the resolution augmentation in the target, which is invertible in the
derived category precisely because the target is K-injective.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedSheafHomModel`: the internal Hom complex into a
  K-injective resolution of the target, pushed into the derived category.
* `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`: the bifunctor
  `RSheafHom(-, -)`.
* `AlgebraicGeometry.RingedSite.derivedSheafHomResolutionComparison` and
  `AlgebraicGeometry.RingedSite.derivedSheafHomComparison`: the comparison with the internal
  Hom complex of the chosen resolution of the target, and of a K-injective target itself.
* `AlgebraicGeometry.RingedSite.DerivedInternalHom`: the data of a derived internal Hom
  bifunctor together with its K-injective model comparison and the naturality of that
  comparison.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomModel_inverts`: the inverting property that
  makes the descent possible.
* `AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality`: the comparison is
  natural in the arbitrary source and in the K-injective target at once.
* `AlgebraicGeometry.RingedSite.exists_derivedInternalHom`: the derived internal Hom exists.

## Implementation notes

The resolution enters only in the second variable, and only through its universal properties:
the augmentation `M ⟶ R M` is a quasi-isomorphism and `R M` is K-injective. Nothing below
unfolds `R`, and nothing below unfolds `homMap`, which is used only through `homMap_id`,
`homMap_comp` and `homMap_quasiIso`.

That `R` preserves quasi-isomorphisms is not part of its interface and is deduced from the
naturality of the augmentation, by the two-out-of-three property of quasi-isomorphisms.

`AlgebraicGeometry.RingedSite.DerivedInternalHom` is the ringed-site notion and is unrelated to
the namesake `StacksDraft.DerivedHom.DerivedInternalHom.Model` of
`StacksFrontier.Homology.HomComplex.DerivedInternalHom`, which is the derived internal Hom of
modules over a commutative ring, obtained there from the derived tensor–Hom adjunction rather
than from K-injective resolutions.

`kInjectiveResolution` and `kInjectiveAugmentation` are the site-specialised spellings of
`Stacks.Injectives.kInjectiveResolutionFunctor` and
`Stacks.Injectives.kInjectiveResolutionInclusion`; they name no new construction.

The universes are all equal. That is not a choice: the functorial K-injective resolution needs
sheaves of `O`-modules to be Grothendieck abelian *in the module universe*, which
`Stacks.SheafOfModules.Small.isGrothendieckAbelian_sheafOfModules` supplies in `UnivLE` form,
and the internal Hom complex of Stacks 0A8Z raises the module universe to `max u v m`, so an
iterated internal Hom forces the three site universes and the module universe together. The
universe `d` of the localization stays independent, as it does for the derived tensor product.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

/-- The chosen functorial K-injective resolution of complexes of `O`-modules, which exists
because sheaves of `O`-modules form a Grothendieck abelian category. -/
abbrev kInjectiveResolution :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  Stacks.Injectives.kInjectiveResolutionFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The augmentation of a complex of `O`-modules into its chosen K-injective resolution. -/
abbrev kInjectiveAugmentation :
    Functor.id
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) ⟶
      kInjectiveResolution X :=
  Stacks.Injectives.kInjectiveResolutionInclusion
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The augmentation into the chosen K-injective resolution is natural. -/
private theorem kInjectiveAugmentation_app_comp_map
    {M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (m : M ⟶ M') :
    (kInjectiveAugmentation X).app M ≫ (kInjectiveResolution X).map m =
      m ≫ (kInjectiveAugmentation X).app M' :=
  ((kInjectiveAugmentation X).naturality m).symm

/-- The chosen K-injective resolution preserves quasi-isomorphisms. This is not part of the
interface of the resolution functor; it follows from the naturality of the augmentation and
the two-out-of-three property of quasi-isomorphisms. -/
theorem quasiIso_kInjectiveResolution_map
    {M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (m : M ⟶ M') [QuasiIso m] :
    QuasiIso ((kInjectiveResolution X).map m) := by
  have : QuasiIso ((kInjectiveAugmentation X).app M ≫ (kInjectiveResolution X).map m) := by
    rw [kInjectiveAugmentation_app_comp_map]; infer_instance
  exact quasiIso_of_comp_left ((kInjectiveAugmentation X).app M)
    ((kInjectiveResolution X).map m)

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The internal Hom complex into the chosen K-injective resolution of the target, pushed into
the derived category. This is the bifunctor whose descent is the derived internal Hom. -/
abbrev derivedSheafHomModel :
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  sheafHomComplexBifunctor X ⋙
    (Functor.whiskeringLeft _ _ _).obj (kInjectiveResolution X) ⋙
      (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q

/-- `derivedSheafHomModel` acts on a morphism of sources by precomposition into the resolved
target. -/
theorem derivedSheafHomModel_map_app
    {K K' : (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ}
    (k : K ⟶ K')
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedSheafHomModel X).map k).app M =
      DerivedCategory.Q.map
        (homMap X k.unop (𝟙 ((kInjectiveResolution X).obj M))) := rfl

/-- `derivedSheafHomModel` acts on a morphism of targets by postcomposition with its
resolution. -/
theorem derivedSheafHomModel_obj_map
    (K : (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ)
    {M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (m : M ⟶ M') :
    ((derivedSheafHomModel X).obj K).map m =
      DerivedCategory.Q.map
        (homMap X (𝟙 K.unop) ((kInjectiveResolution X).map m)) := rfl

/-- The class in the derived category of `homMap` between K-injective targets and
quasi-isomorphic sources is invertible. -/
private theorem isIso_Q_map_homMap
    {I I' L L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (i : I' ⟶ I) [QuasiIso i] [I'.IsKInjective] [I.IsKInjective] (l : L' ⟶ L) [QuasiIso l] :
    IsIso (DerivedCategory.Q.map (homMap X l i)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (homMap_quasiIso X i l)

/-- `derivedSheafHomModel` inverts quasi-isomorphisms in the source and in the target
simultaneously. Both halves are Stacks 0A95, applied with an identity in the other variable:
the resolution of the target is K-injective, and it preserves quasi-isomorphisms. -/
theorem derivedSheafHomModel_inverts :
    MorphismProperty.IsInvertedBy₂
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).op
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (derivedSheafHomModel X) := by
  rintro ⟨K, M⟩ ⟨K', M'⟩ ⟨k, m⟩ ⟨hk, hm⟩
  have hk' : QuasiIso k.unop := (HomologicalComplex.mem_quasiIso_iff k.unop).1 hk
  have hm' : QuasiIso m := (HomologicalComplex.mem_quasiIso_iff m).1 hm
  have hRm : QuasiIso ((kInjectiveResolution X).map m) :=
    quasiIso_kInjectiveResolution_map X m
  have e1 : IsIso (((derivedSheafHomModel X).map k).app M) := by
    rw [derivedSheafHomModel_map_app]
    exact isIso_Q_map_homMap X (𝟙 ((kInjectiveResolution X).obj M)) k.unop
  have e2 : IsIso (((derivedSheafHomModel X).obj K').map m) := by
    rw [derivedSheafHomModel_obj_map]
    exact isIso_Q_map_homMap X ((kInjectiveResolution X).map m) (𝟙 K'.unop)
  rw [Functor.uncurry_obj_map]
  infer_instance

/-- The derived internal Hom bifunctor on the derived category of sheaves of modules on a
ringed site, contravariant in its source. -/
def derivedSheafHomBifunctor :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Localization.lift₂ (derivedSheafHomModel X) (derivedSheafHomModel_inverts X)
    DerivedCategory.Q.op DerivedCategory.Q

/-- `derivedSheafHomBifunctor` descends `derivedSheafHomModel` along the two localizations. -/
@[instance_reducible]
def derivedSheafHomBifunctorLifting :
    Localization.Lifting₂ DerivedCategory.Q.op DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).op
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (derivedSheafHomModel X) (derivedSheafHomBifunctor X) := by
  unfold derivedSheafHomBifunctor
  infer_instance

attribute [local instance] derivedSheafHomBifunctorLifting

/-- The comparison isomorphism of bifunctors: on an arbitrary source and the chosen
K-injective resolution of the target, the derived internal Hom is the ordinary internal Hom
complex. -/
abbrev derivedSheafHomNatIso :
    (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q.op).obj
        DerivedCategory.Q).obj (derivedSheafHomBifunctor X) ≅
      derivedSheafHomModel X :=
  Localization.Lifting₂.iso DerivedCategory.Q.op DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).op
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (derivedSheafHomModel X) (derivedSheafHomBifunctor X)

/-- For arbitrary complexes `K` and `M`, the derived internal Hom of their classes is the
class of the internal Hom complex from `K` into the chosen K-injective resolution of `M`. -/
def derivedSheafHomResolutionComparison
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).obj
        (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj
        (sheafHomComplex X K ((kInjectiveResolution X).obj M)).obj :=
  ((derivedSheafHomNatIso X).app (op K)).app M

/-- The augmentation of a K-injective target into its chosen resolution induces an
isomorphism of internal Hom complexes in the derived category. -/
instance isIso_Q_map_homMap_kInjectiveAugmentation
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [M.IsKInjective] :
    IsIso (DerivedCategory.Q.map
      (homMap X (𝟙 K) ((kInjectiveAugmentation X).app M))) := by
  have : ((Functor.id
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)).obj
        M).IsKInjective :=
    inferInstanceAs M.IsKInjective
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (homMap_quasiIso X ((kInjectiveAugmentation X).app M) (𝟙 K))

/-- **The K-injective model of the derived internal Hom.** If the target `M` is K-injective
then the derived internal Hom of the classes of `K` and `M` is the class of the ordinary
internal Hom complex `SheafHom(K, M)`. -/
def derivedSheafHomComparison
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [M.IsKInjective] :
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).obj
        (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (sheafHomComplex X K M).obj :=
  derivedSheafHomResolutionComparison X K M ≪≫
    (asIso (DerivedCategory.Q.map
      (homMap X (𝟙 K) ((kInjectiveAugmentation X).app M)))).symm

/-- The comparison with the chosen resolution is natural in the source and in the target at
once: it is the lifting datum of the descent, so this is the naturality of that datum. -/
theorem derivedSheafHomResolutionComparison_naturality
    {K K' M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : K' ⟶ K) (g : M ⟶ M') :
    ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map f).op).app
          (DerivedCategory.Q.obj M) ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K'))).map
          (DerivedCategory.Q.map g) ≫
        (derivedSheafHomResolutionComparison X K' M').hom =
      (derivedSheafHomResolutionComparison X K M).hom ≫
        DerivedCategory.Q.map
          (homMap X f ((kInjectiveResolution X).map g)) := by
  have h := (Functor.uncurry.map (derivedSheafHomNatIso X).hom).naturality
    ((⟨f.op, g⟩ : ((op K, M) : _ × _) ⟶ (op K', M')))
  simp only [Functor.uncurry_obj_map, Functor.uncurry_map_app, Category.assoc] at h
  have h' : ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map f).op).app
          (DerivedCategory.Q.obj M) ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K'))).map
          (DerivedCategory.Q.map g) ≫
        (derivedSheafHomResolutionComparison X K' M').hom =
      (derivedSheafHomResolutionComparison X K M).hom ≫
        DerivedCategory.Q.map
          (homMap X f (𝟙 ((kInjectiveResolution X).obj M))) ≫
        DerivedCategory.Q.map
          (homMap X (𝟙 K') ((kInjectiveResolution X).map g)) := h
  rw [h', ← Functor.map_comp, homMap_comp, Category.id_comp, Category.id_comp]

/-- **The K-injective model comparison is natural.** It intertwines the maps induced on derived
internal Hom with the maps `homMap` of internal Hom complexes, in the source and in the
K-injective target at once. -/
theorem derivedSheafHomComparison_naturality
    {K K' M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [M.IsKInjective] [M'.IsKInjective] (f : K' ⟶ K) (g : M ⟶ M') :
    ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map f).op).app
          (DerivedCategory.Q.obj M) ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K'))).map
          (DerivedCategory.Q.map g) ≫
        (derivedSheafHomComparison X K' M').hom =
      (derivedSheafHomComparison X K M).hom ≫
        DerivedCategory.Q.map (homMap X f g) := by
  have key : homMap X (𝟙 K) ((kInjectiveAugmentation X).app M) ≫
      homMap X f ((kInjectiveResolution X).map g) =
        homMap X f g ≫ homMap X (𝟙 K') ((kInjectiveAugmentation X).app M') := by
    rw [homMap_comp, homMap_comp, Category.comp_id, Category.id_comp,
      kInjectiveAugmentation_app_comp_map]
  have h := derivedSheafHomResolutionComparison_naturality X f g
  dsimp only [derivedSheafHomComparison, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  simp only [← Category.assoc] at h ⊢
  rw [IsIso.comp_inv_eq, h]
  simp only [Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← Functor.map_comp, ← Functor.map_comp, key]

/-- Data characterizing the derived internal Hom: a bifunctor on the derived category,
contravariant in its source, whose value on a K-injective target is the class of the ordinary
internal Hom complex, naturally in both variables. -/
structure DerivedInternalHom where
  /-- The derived internal Hom bifunctor, contravariant in its first argument. -/
  hom : (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  /-- A K-injective target computes the derived internal Hom. -/
  homComparison
      (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      [B.IsKInjective] :
    (hom.obj (op (DerivedCategory.Q.obj A))).obj (DerivedCategory.Q.obj B) ≅
      DerivedCategory.Q.obj (sheafHomComplex X A B).obj
  /-- The model comparison intertwines both variables with the canonical pre- and
  postcomposition maps on internal Hom complexes. -/
  homComparison_natural
      {A A' B B' :
        CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
      [B.IsKInjective] [B'.IsKInjective] (f : A' ⟶ A) (g : B ⟶ B') :
    (hom.map (DerivedCategory.Q.map f).op).app (DerivedCategory.Q.obj B) ≫
        (hom.obj (op (DerivedCategory.Q.obj A'))).map (DerivedCategory.Q.map g) ≫
        (homComparison A' B').hom =
      (homComparison A B).hom ≫ DerivedCategory.Q.map (homMap X f g)

/-- **The derived internal Hom of sheaves of modules on a ringed site exists**, with its
K-injective model comparison and the naturality of that comparison. -/
theorem exists_derivedInternalHom : Nonempty (DerivedInternalHom.{u, d} X) :=
  ⟨{ hom := derivedSheafHomBifunctor X
     homComparison := fun A B _ => derivedSheafHomComparison X A B
     homComparison_natural := fun f g => derivedSheafHomComparison_naturality X f g }⟩

/-- The canonical derived internal Hom of sheaves of modules on a ringed site. -/
def canonicalDerivedInternalHom : DerivedInternalHom.{u, d} X :=
  Classical.choice (exists_derivedInternalHom X)

/-- The derived internal Hom bifunctor on the derived category of `X`. -/
abbrev derivedInternalHomFunctor := (canonicalDerivedInternalHom.{u, d} X).hom

end AlgebraicGeometry.RingedSite

end
