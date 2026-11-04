module

public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Localization.Opposite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallHomComplex

/-! # The derived internal Hom on an essentially small ringed site

Let `(C, O)` be a ringed site whose objects form a type in a universe `c` while its morphisms,
its structure sheaf and its modules live in `u`, and assume `C` is essentially `u`-small. This
is the shape of the small étale ringed site of a scheme or of an algebraic space, a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`. This file constructs the derived internal Hom
bifunctor

`RSheafHom(-, -) : D(Mod(O))ᵒᵖ ⥤ D(Mod(O)) ⥤ D(Mod(O))`

on the derived category of `O`-modules *with sections in `Type u`*, together with the
isomorphism identifying its value at `(K, M)` with the class of the internal Hom complex
`SheafHom(K, M)` whenever the target `M` is K-injective, naturally in both variables.

The construction is the one of `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`, which
is stated for a `AlgebraicGeometry.RingedSite.{u, u, u}`. Two inputs of that construction pinned
the universes together there, and both are available on an essentially small site:

* a functorial K-injective resolution (Stacks 079P) needs `O`-modules to form a Grothendieck
  abelian category in the module universe, and on an essentially `u`-small site they do,
  `SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`;
* the internal Hom complex has its sections in `Type (max c u)`, but on an essentially
  `u`-small site it descends to the module universe as
  `AlgebraicGeometry.RingedSite.sheafHomComplexSmall`, for which Stacks 0A95 is
  `AlgebraicGeometry.RingedSite.homMapSmall_quasiIso`.

## Main definitions

* `AlgebraicGeometry.RingedSite.sheafHomComplexSmallBifunctor`: the internal Hom complex at the
  module universe as a bifunctor.
* `AlgebraicGeometry.RingedSite.derivedSheafHomSmallBifunctor`: the bifunctor `RSheafHom(-, -)`.
* `AlgebraicGeometry.RingedSite.derivedSheafHomSmallComparison`: its comparison with the
  internal Hom complex into a K-injective target.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomSmallModel_inverts`: the inverting property that
  makes the descent possible.
* `AlgebraicGeometry.RingedSite.derivedSheafHomSmallComparison_naturality`: the comparison is
  natural in the arbitrary source and in the K-injective target at once.

## Implementation notes

As in the collapsed construction, the resolution enters only in the second variable and only
through its universal properties, and `homMapSmall` is used only through `homMapSmall_id`,
`homMapSmall_comp` and `homMapSmall_quasiIso`.

No tag is placed. Stacks 0A97 is the derived internal Hom; this is that object on a ringed site
whose objects need not lie in the universe of its modules, and the tag is carried where the
derived internal Hom is consumed.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]

/-- The internal Hom complex at the module universe of an essentially small ringed site, as a
bifunctor, contravariant in its source and covariant in its target. -/
def sheafHomComplexSmallBifunctor :
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
        CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ where
  obj K :=
    { obj := fun M => sheafHomComplexSmall X K.unop M
      map := fun m => homMapSmall X (𝟙 K.unop) m
      map_id := fun M => homMapSmall_id X K.unop M
      map_comp := fun m m' => by rw [← homMapSmall_comp, Category.comp_id] }
  map k :=
    { app := fun M => homMapSmall X k.unop (𝟙 M)
      naturality := fun M M' m => by
        change homMapSmall X (𝟙 _) m ≫ homMapSmall X k.unop (𝟙 M') =
          homMapSmall X k.unop (𝟙 M) ≫ homMapSmall X (𝟙 _) m
        rw [← homMapSmall_comp, ← homMapSmall_comp, Category.comp_id, Category.id_comp,
          Category.comp_id, Category.id_comp] }
  map_id K := NatTrans.ext (funext fun M => homMapSmall_id X K.unop M)
  map_comp k k' := NatTrans.ext (funext fun M => by
    change homMapSmall X (k'.unop ≫ k.unop) (𝟙 M) =
      homMapSmall X k.unop (𝟙 M) ≫ homMapSmall X k'.unop (𝟙 M)
    rw [← homMapSmall_comp, Category.comp_id])

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `O`-modules with sections in `Type u` on an essentially `u`-small ringed site form a
Grothendieck abelian category at the universe `u`. -/
instance isGrothendieckAbelian_sheafOfModules_essentiallySmall :
    IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- The chosen functorial K-injective resolution of complexes of `O`-modules on an essentially
small ringed site. -/
abbrev kInjectiveResolutionSmall :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  Stacks.Injectives.kInjectiveResolutionFunctor.{u}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The augmentation of a complex of `O`-modules into its chosen K-injective resolution. -/
abbrev kInjectiveAugmentationSmall :
    Functor.id (CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) ⟶
      kInjectiveResolutionSmall X :=
  Stacks.Injectives.kInjectiveResolutionInclusion.{u}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- Naturality of the augmentation into the chosen K-injective resolution. -/
private theorem kInjectiveAugmentationSmall_comp_map
    {M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (m : M ⟶ M') :
    (kInjectiveAugmentationSmall X).app M ≫ (kInjectiveResolutionSmall X).map m =
      m ≫ (kInjectiveAugmentationSmall X).app M' :=
  ((kInjectiveAugmentationSmall X).naturality m).symm

/-- The chosen K-injective resolution preserves quasi-isomorphisms, by naturality of the
augmentation and two-out-of-three. -/
theorem quasiIso_kInjectiveResolutionSmall_map
    {M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (m : M ⟶ M') [QuasiIso m] :
    QuasiIso ((kInjectiveResolutionSmall X).map m) := by
  have : QuasiIso ((kInjectiveAugmentationSmall X).app M ≫
      (kInjectiveResolutionSmall X).map m) := by
    rw [kInjectiveAugmentationSmall_comp_map]; infer_instance
  exact quasiIso_of_comp_left ((kInjectiveAugmentationSmall X).app M)
    ((kInjectiveResolutionSmall X).map m)

variable [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{max c u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The internal Hom complex into the chosen K-injective resolution of the target, pushed into
the derived category. -/
abbrev derivedSheafHomSmallModel :
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  sheafHomComplexSmallBifunctor X ⋙
    (Functor.whiskeringLeft _ _ _).obj (kInjectiveResolutionSmall X) ⋙
      (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q

/-- The class in the derived category of an internal Hom map along a quasi-isomorphism of sources
and a quasi-isomorphism of K-injective targets is invertible. -/
private theorem isIso_Q_map_homMapSmall_of_quasiIso
    {K K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (l : K' ⟶ K) [QuasiIso l] (i : I' ⟶ I) [QuasiIso i] [I'.IsKInjective] [I.IsKInjective] :
    IsIso (DerivedCategory.Q.map (homMapSmall X l i)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (homMapSmall_quasiIso X i l)

omit [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{max c u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}] in
/-- `derivedSheafHomSmallModel` on a morphism `k` of sources, at a target `M`: the map of
internal Hom complexes along `k` into the chosen K-injective resolution of `M`, pushed into the
derived category. -/
theorem derivedSheafHomSmallModel_map_app
    {K K' : (CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ} (k : K ⟶ K')
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedSheafHomSmallModel X).map k).app M =
      DerivedCategory.Q.map
        (homMapSmall X k.unop (𝟙 ((kInjectiveResolutionSmall X).obj M))) := rfl

omit [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{max c u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}] in
/-- `derivedSheafHomSmallModel` at a source `K`, on a morphism `m` of targets: the map of
internal Hom complexes out of `K` along the chosen K-injective resolution of `m`, pushed into the
derived category. -/
theorem derivedSheafHomSmallModel_obj_map
    (K : (CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ)
    {M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (m : M ⟶ M') :
    ((derivedSheafHomSmallModel X).obj K).map m =
      DerivedCategory.Q.map
        (homMapSmall X (𝟙 K.unop) ((kInjectiveResolutionSmall X).map m)) := rfl

/-- `derivedSheafHomSmallModel` inverts quasi-isomorphisms in the source and in the target
simultaneously; both halves are Stacks 0A95 at the module universe. -/
theorem derivedSheafHomSmallModel_inverts :
    MorphismProperty.IsInvertedBy₂
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).op
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (derivedSheafHomSmallModel X) := by
  rintro ⟨K, M⟩ ⟨K', M'⟩ ⟨k, m⟩ ⟨hk, hm⟩
  have hk' : QuasiIso k.unop := (HomologicalComplex.mem_quasiIso_iff k.unop).1 hk
  have hm' : QuasiIso m := (HomologicalComplex.mem_quasiIso_iff m).1 hm
  have hRm : QuasiIso ((kInjectiveResolutionSmall X).map m) :=
    quasiIso_kInjectiveResolutionSmall_map X m
  have e1 : IsIso (((derivedSheafHomSmallModel X).map k).app M) := by
    rw [derivedSheafHomSmallModel_map_app]
    exact isIso_Q_map_homMapSmall_of_quasiIso X k.unop _
  have e2 : IsIso (((derivedSheafHomSmallModel X).obj K').map m) := by
    rw [derivedSheafHomSmallModel_obj_map]
    exact isIso_Q_map_homMapSmall_of_quasiIso X _ _
  rw [Functor.uncurry_obj_map]
  infer_instance

/-- **The derived internal Hom on an essentially small ringed site**, on the derived category
of `O`-modules with sections in the universe of the morphisms of the site, contravariant in its
source. -/
def derivedSheafHomSmallBifunctor :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Localization.lift₂ (derivedSheafHomSmallModel X) (derivedSheafHomSmallModel_inverts X)
    DerivedCategory.Q.op DerivedCategory.Q

/-- `derivedSheafHomSmallBifunctor` descends `derivedSheafHomSmallModel` along the two
localizations. -/
@[instance_reducible]
def derivedSheafHomSmallBifunctorLifting :
    Localization.Lifting₂ DerivedCategory.Q.op DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).op
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (derivedSheafHomSmallModel X) (derivedSheafHomSmallBifunctor X) := by
  unfold derivedSheafHomSmallBifunctor
  infer_instance

attribute [local instance] derivedSheafHomSmallBifunctorLifting

/-- The comparison isomorphism of bifunctors with the model. -/
abbrev derivedSheafHomSmallNatIso :
    (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q.op).obj
        DerivedCategory.Q).obj (derivedSheafHomSmallBifunctor X) ≅
      derivedSheafHomSmallModel X :=
  Localization.Lifting₂.iso DerivedCategory.Q.op DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).op
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (derivedSheafHomSmallModel X) (derivedSheafHomSmallBifunctor X)

/-- For arbitrary complexes `K` and `M`, the derived internal Hom of their classes is the class
of the internal Hom complex from `K` into the chosen K-injective resolution of `M`. -/
def derivedSheafHomSmallResolutionComparison
    (K M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedSheafHomSmallBifunctor X).obj (op (DerivedCategory.Q.obj K))).obj
        (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (sheafHomComplexSmall X K ((kInjectiveResolutionSmall X).obj M)) :=
  ((derivedSheafHomSmallNatIso X).app (op K)).app M

/-- The augmentation of a K-injective target into its chosen resolution induces an
isomorphism of internal Hom complexes in the derived category. -/
instance isIso_Q_map_homMapSmall_kInjectiveAugmentation
    (K M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) [M.IsKInjective] :
    IsIso (DerivedCategory.Q.map
      (homMapSmall X (𝟙 K) ((kInjectiveAugmentationSmall X).app M))) := by
  have : ((Functor.id (CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)).obj M).IsKInjective :=
    inferInstanceAs M.IsKInjective
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (homMapSmall_quasiIso X ((kInjectiveAugmentationSmall X).app M) (𝟙 K))

/-- **The K-injective model of the derived internal Hom.** If the target `M` is K-injective
then the derived internal Hom of the classes of `K` and `M` is the class of the internal Hom
complex `SheafHom(K, M)`. -/
def derivedSheafHomSmallComparison
    (K M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) [M.IsKInjective] :
    ((derivedSheafHomSmallBifunctor X).obj (op (DerivedCategory.Q.obj K))).obj
        (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (sheafHomComplexSmall X K M) :=
  derivedSheafHomSmallResolutionComparison X K M ≪≫
    (asIso (DerivedCategory.Q.map
      (homMapSmall X (𝟙 K) ((kInjectiveAugmentationSmall X).app M)))).symm

/-- The comparison with the chosen resolution is natural in the source and in the target. -/
theorem derivedSheafHomSmallResolutionComparison_naturality
    {K K' M M' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : K' ⟶ K) (g : M ⟶ M') :
    ((derivedSheafHomSmallBifunctor X).map (DerivedCategory.Q.map f).op).app
          (DerivedCategory.Q.obj M) ≫
        ((derivedSheafHomSmallBifunctor X).obj (op (DerivedCategory.Q.obj K'))).map
          (DerivedCategory.Q.map g) ≫
        (derivedSheafHomSmallResolutionComparison X K' M').hom =
      (derivedSheafHomSmallResolutionComparison X K M).hom ≫
        DerivedCategory.Q.map
          (homMapSmall X f ((kInjectiveResolutionSmall X).map g)) := by
  have h := (Functor.uncurry.map (derivedSheafHomSmallNatIso X).hom).naturality
    ((⟨f.op, g⟩ : ((op K, M) : _ × _) ⟶ (op K', M')))
  simp only [Functor.uncurry_obj_map, Functor.uncurry_map_app, Category.assoc] at h
  have h' : ((derivedSheafHomSmallBifunctor X).map (DerivedCategory.Q.map f).op).app
          (DerivedCategory.Q.obj M) ≫
        ((derivedSheafHomSmallBifunctor X).obj (op (DerivedCategory.Q.obj K'))).map
          (DerivedCategory.Q.map g) ≫
        (derivedSheafHomSmallResolutionComparison X K' M').hom =
      (derivedSheafHomSmallResolutionComparison X K M).hom ≫
        DerivedCategory.Q.map
          (homMapSmall X f (𝟙 ((kInjectiveResolutionSmall X).obj M))) ≫
        DerivedCategory.Q.map
          (homMapSmall X (𝟙 K') ((kInjectiveResolutionSmall X).map g)) := h
  rw [h', ← Functor.map_comp, ← homMapSmall_comp, Category.id_comp, Category.id_comp]

/-- **The K-injective model comparison is natural**, in the source and in the K-injective
target at once. -/
theorem derivedSheafHomSmallComparison_naturality
    {K K' M M' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [M.IsKInjective] [M'.IsKInjective] (f : K' ⟶ K) (g : M ⟶ M') :
    ((derivedSheafHomSmallBifunctor X).map (DerivedCategory.Q.map f).op).app
          (DerivedCategory.Q.obj M) ≫
        ((derivedSheafHomSmallBifunctor X).obj (op (DerivedCategory.Q.obj K'))).map
          (DerivedCategory.Q.map g) ≫
        (derivedSheafHomSmallComparison X K' M').hom =
      (derivedSheafHomSmallComparison X K M).hom ≫
        DerivedCategory.Q.map (homMapSmall X f g) := by
  have key : homMapSmall X (𝟙 K) ((kInjectiveAugmentationSmall X).app M) ≫
      homMapSmall X f ((kInjectiveResolutionSmall X).map g) =
        homMapSmall X f g ≫ homMapSmall X (𝟙 K') ((kInjectiveAugmentationSmall X).app M') := by
    rw [← homMapSmall_comp, ← homMapSmall_comp, Category.comp_id, Category.id_comp,
      kInjectiveAugmentationSmall_comp_map]
  have h := derivedSheafHomSmallResolutionComparison_naturality X f g
  dsimp only [derivedSheafHomSmallComparison, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  simp only [← Category.assoc] at h ⊢
  rw [IsIso.comp_inv_eq, h]
  simp only [Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← Functor.map_comp, ← Functor.map_comp, key]

end AlgebraicGeometry.RingedSite

end
