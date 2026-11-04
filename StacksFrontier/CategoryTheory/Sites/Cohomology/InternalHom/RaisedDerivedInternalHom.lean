module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.RaisedQuasiIsoInvariance
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.RaisedInternalHomBifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom

/-! # The derived internal Hom on a ringed site with large objects

`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` is the derived internal Hom

`RSheafHom(-, -) : D(Mod(O))ᵒᵖ ⥤ D(Mod(O)) ⥤ D(Mod(O))`

of a `AlgebraicGeometry.RingedSite.{u, u, u}`. This file constructs it for a
`AlgebraicGeometry.RingedSite.{c, u, u}` whose underlying category is essentially `u`-small:
objects in an arbitrary universe `c`, morphisms, structure sheaf and modules in `u`.

The universes cannot all stay in `u` there, and that is not a defect of the spelling. The
internal Hom complex of Stacks 0A8X of two complexes of `SheafOfModules.{u}` is a complex of
`SheafOfModules.{max c u}` — its sections over `U` are maps of presheaves on the slice site
`C/U`, a family indexed by the objects of that slice, which lie in `max c u`. So the honest
statement of the derived internal Hom here is a bifunctor

`D(Mod_u(O))ᵒᵖ ⥤ D(Mod_u(O)) ⥤ D(Mod_{max c u}(O))`

landing one universe up from its arguments, and that is what
`AlgebraicGeometry.RingedSite.Raised.mixedDerivedSheafHomBifunctor` is. When `c = u` the three
coincide and it is `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`
(`AlgebraicGeometry.RingedSite.Raised.mixedDerivedSheafHomBifunctor_eq`).

The construction is the one of `DerivedInternalHom.lean`, unchanged: the bifunctor
`(K, M) ↦ Q(SheafHom(K, R M))`, with `R` the functorial K-injective resolution of complexes of
`SheafOfModules.{u}`, inverts quasi-isomorphisms in both variables at once by Stacks 0A95 and so
descends along `DerivedCategory.Q.op` and `DerivedCategory.Q`. What made it unavailable at these
universes was Stacks 0A95 itself, and that is now
`AlgebraicGeometry.RingedSite.Raised.homMap_quasiIso`.

## Main definitions

* `AlgebraicGeometry.RingedSite.Raised.mixedSheafHomComplexBifunctor`: the internal Hom complex
  of complexes of `SheafOfModules.{u}`, as a bifunctor into complexes of
  `SheafOfModules.{max c u}`.
* `AlgebraicGeometry.RingedSite.Raised.mixedDerivedSheafHomModel`: that bifunctor composed with
  the K-injective resolution of the target and with `DerivedCategory.Q`.
* `AlgebraicGeometry.RingedSite.Raised.mixedDerivedSheafHomBifunctor`: **the derived internal
  Hom.**

## Main results

* `AlgebraicGeometry.RingedSite.Raised.mixedDerivedSheafHomModel_inverts`: the inverting
  property that makes the descent possible.
* `AlgebraicGeometry.RingedSite.Raised.mixedDerivedSheafHomResolutionComparison`: the value of
  the derived internal Hom on the classes of `K` and `M` is the class of `SheafHom(K, R M)`.
* `AlgebraicGeometry.RingedSite.Raised.mixedSheafHomComplexBifunctor_eq` and
  `AlgebraicGeometry.RingedSite.Raised.mixedDerivedSheafHomBifunctor_eq`: at
  `RingedSite.{u, u, u}` these *are* the declarations of `Bifunctor.lean` and
  `DerivedInternalHom.lean`, so the generalisation names the same objects.

## Implementation notes

`quasiIso_kInjectiveResolutionFunctor_map` is stated for an arbitrary Grothendieck abelian
category rather than for sheaves of modules on a site, which is the generality its proof has;
`AlgebraicGeometry.RingedSite.quasiIso_kInjectiveResolution_map` is its specialisation at the
collapsed universes.

The Grothendieck abelian structure on `SheafOfModules.{u} X.ringSheaf` is a hypothesis. On the
small étale ringed site it is discharged by
`AlgebraicGeometry.smallEtaleRingedSite_isGrothendieckAbelian`, which comes from
`SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`; `CategoryTheory.IsGrothendieckAbelian`
is a `Prop`, so taking it as a hypothesis cannot create a diamond with any other route to it.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c u d e

namespace AlgebraicGeometry.RingedSite.Raised

/-- The chosen functorial K-injective resolution preserves quasi-isomorphisms, in any
Grothendieck abelian category. This is not part of the interface of the resolution functor; it
follows from the naturality of the augmentation and the two-out-of-three property of
quasi-isomorphisms. -/
theorem quasiIso_kInjectiveResolutionFunctor_map (A : Type*) [Category A] [Abelian A]
    [IsGrothendieckAbelian A] {M M' : CochainComplex A ℤ} (f : M ⟶ M') [QuasiIso f] :
    QuasiIso ((Stacks.Injectives.kInjectiveResolutionFunctor A).map f) := by
  have h : (Stacks.Injectives.kInjectiveResolutionInclusion A).app M ≫
      (Stacks.Injectives.kInjectiveResolutionFunctor A).map f =
      f ≫ (Stacks.Injectives.kInjectiveResolutionInclusion A).app M' :=
    ((Stacks.Injectives.kInjectiveResolutionInclusion A).naturality f).symm
  have : QuasiIso ((Stacks.Injectives.kInjectiveResolutionInclusion A).app M ≫
      (Stacks.Injectives.kInjectiveResolutionFunctor A).map f) := by
    rw [h]; infer_instance
  exact quasiIso_of_comp_left ((Stacks.Injectives.kInjectiveResolutionInclusion A).app M)
    ((Stacks.Injectives.kInjectiveResolutionFunctor A).map f)

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{max c u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}]
  [IsGrothendieckAbelian.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-! ### The internal Hom complex as a bifunctor into the raised module universe -/

/-- **The internal Hom complex of complexes of `O`-modules with sections in `u`, as a
bifunctor**, contravariant in its source. Its values are complexes of `O`-modules with sections
in `max c u`, which is where the internal Hom complex of Stacks 0A8X lands.

For `c = u` this is `AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor`
(`AlgebraicGeometry.RingedSite.Raised.mixedSheafHomComplexBifunctor_eq`). -/
def mixedSheafHomComplexBifunctor :
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
        CochainComplex
          (SheafOfModules.{max c u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ where
  obj K :=
    { obj := fun M => (sheafHomComplex X K.unop M).obj
      map := fun m => homMap X (𝟙 K.unop) m
      map_id := fun M => homMap_id X K.unop M
      map_comp := fun m m' => by rw [homMap_comp, Category.comp_id] }
  map k :=
    { app := fun M => homMap X k.unop (𝟙 M)
      naturality := fun M M' m => by
        change homMap X (𝟙 _) m ≫ homMap X k.unop (𝟙 M') =
          homMap X k.unop (𝟙 M) ≫ homMap X (𝟙 _) m
        rw [homMap_comp, homMap_comp, Category.comp_id, Category.id_comp, Category.comp_id,
          Category.id_comp] }
  map_id K := NatTrans.ext (funext fun M => homMap_id X K.unop M)
  map_comp k k' := NatTrans.ext (funext fun M => by
    change homMap X (k'.unop ≫ k.unop) (𝟙 M) =
      homMap X k.unop (𝟙 M) ≫ homMap X k'.unop (𝟙 M)
    rw [homMap_comp, Category.comp_id])

/-! ### The K-injective model and its descent -/

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{e} (SheafOfModules.{max c u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The internal Hom complex into the chosen K-injective resolution of the target, pushed into
the derived category of the raised module universe. This is the bifunctor whose descent is the
derived internal Hom. -/
abbrev mixedDerivedSheafHomModel :
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
        DerivedCategory (SheafOfModules.{max c u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  mixedSheafHomComplexBifunctor X ⋙
    (Functor.whiskeringLeft _ _ _).obj
        (Stacks.Injectives.kInjectiveResolutionFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⋙
      (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q

omit [EssentiallySmall.{u} X.C] [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- `mixedDerivedSheafHomModel` acts on a morphism of sources by precomposition into the
resolved target. -/
theorem mixedDerivedSheafHomModel_map_app
    {K K' : (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ}
    (k : K ⟶ K')
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((mixedDerivedSheafHomModel X).map k).app M =
      DerivedCategory.Q.map (homMap X k.unop
        (𝟙 ((Stacks.Injectives.kInjectiveResolutionFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).obj M))) := rfl

omit [EssentiallySmall.{u} X.C] [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- `mixedDerivedSheafHomModel` acts on a morphism of targets by postcomposition with its
resolution. -/
theorem mixedDerivedSheafHomModel_obj_map
    (K : (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ)
    {M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : M ⟶ M') :
    ((mixedDerivedSheafHomModel X).obj K).map f =
      DerivedCategory.Q.map (homMap X (𝟙 K.unop)
        ((Stacks.Injectives.kInjectiveResolutionFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map f)) := rfl

omit [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- **The model inverts quasi-isomorphisms in the source and in the target simultaneously.**
Both halves are Stacks 0A95 over a ringed site with large objects
(`AlgebraicGeometry.RingedSite.Raised.homMap_quasiIso`), applied with an identity in the other
variable: the resolution of the target is K-injective, and it preserves
quasi-isomorphisms. -/
theorem mixedDerivedSheafHomModel_inverts :
    MorphismProperty.IsInvertedBy₂
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).op
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (mixedDerivedSheafHomModel X) := by
  rintro ⟨K, M⟩ ⟨K', M'⟩ ⟨k, f⟩ ⟨hk, hf⟩
  have hk' : QuasiIso k.unop := (HomologicalComplex.mem_quasiIso_iff k.unop).1 hk
  have hf' : QuasiIso f := (HomologicalComplex.mem_quasiIso_iff f).1 hf
  have hRf : QuasiIso ((Stacks.Injectives.kInjectiveResolutionFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map f) :=
    quasiIso_kInjectiveResolutionFunctor_map
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) f
  have e1 : IsIso (((mixedDerivedSheafHomModel X).map k).app M) := by
    rw [mixedDerivedSheafHomModel_map_app]
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (homMap_quasiIso X (𝟙 ((Stacks.Injectives.kInjectiveResolutionFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).obj M)) k.unop)
  have e2 : IsIso (((mixedDerivedSheafHomModel X).obj K').map f) := by
    rw [mixedDerivedSheafHomModel_obj_map]
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (homMap_quasiIso X ((Stacks.Injectives.kInjectiveResolutionFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map f) (𝟙 K'.unop))
  rw [Functor.uncurry_obj_map]
  infer_instance

/-- **The derived internal Hom bifunctor of a ringed site with large objects.**

`RSheafHom(-, -) : D(Mod_u(O))ᵒᵖ ⥤ D(Mod_u(O)) ⥤ D(Mod_{max c u}(O))`, contravariant in its
source. For `c = u` this is `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`
(`AlgebraicGeometry.RingedSite.Raised.mixedDerivedSheafHomBifunctor_eq`). -/
def mixedDerivedSheafHomBifunctor :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
        DerivedCategory (SheafOfModules.{max c u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Localization.lift₂ (mixedDerivedSheafHomModel X)
    (mixedDerivedSheafHomModel_inverts X) DerivedCategory.Q.op DerivedCategory.Q

/-- `mixedDerivedSheafHomBifunctor` descends `mixedDerivedSheafHomModel` along the two
localizations. -/
@[instance_reducible]
def mixedDerivedSheafHomBifunctorLifting :
    Localization.Lifting₂ DerivedCategory.Q.op DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).op
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (mixedDerivedSheafHomModel X)
      (mixedDerivedSheafHomBifunctor X) := by
  unfold mixedDerivedSheafHomBifunctor
  infer_instance

attribute [local instance] mixedDerivedSheafHomBifunctorLifting

/-- The comparison isomorphism of bifunctors: on an arbitrary source and the chosen K-injective
resolution of the target, the derived internal Hom is the ordinary internal Hom complex. -/
abbrev mixedDerivedSheafHomNatIso :
    (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q.op).obj
        DerivedCategory.Q).obj (mixedDerivedSheafHomBifunctor X) ≅
      mixedDerivedSheafHomModel X :=
  Localization.Lifting₂.iso DerivedCategory.Q.op DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).op
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (mixedDerivedSheafHomModel X) (mixedDerivedSheafHomBifunctor X)

/-- **For arbitrary complexes `K` and `M` of `O`-modules with sections in `u`, the derived
internal Hom of their classes is the class of the internal Hom complex from `K` into the chosen
K-injective resolution of `M`.** -/
def mixedDerivedSheafHomResolutionComparison
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((mixedDerivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).obj
        (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj
        (sheafHomComplex X K ((Stacks.Injectives.kInjectiveResolutionFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).obj M)).obj :=
  ((mixedDerivedSheafHomNatIso X).app (op K)).app M

/-! ### Agreement with the collapsed statement -/

section Agreement

variable (Y : RingedSite.{u, u, u})
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

omit [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **The generalised internal Hom bifunctor is the one of `Bifunctor.lean`.** -/
theorem mixedSheafHomComplexBifunctor_eq :
    mixedSheafHomComplexBifunctor Y =
      AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor Y :=
  rfl

/-- **The generalised model bifunctor is the one of `DerivedInternalHom.lean`.** -/
theorem mixedDerivedSheafHomModel_eq :
    mixedDerivedSheafHomModel Y =
      AlgebraicGeometry.RingedSite.derivedSheafHomModel.{u, d} Y :=
  rfl

/-- **The generalised derived internal Hom is the one of `DerivedInternalHom.lean`.**

So freeing the universe of the objects of the site has not replaced `RSheafHom` by a parallel
construction; at the collapsed universes it is that bifunctor, on the nose. -/
theorem mixedDerivedSheafHomBifunctor_eq :
    mixedDerivedSheafHomBifunctor Y =
      AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor.{u, d} Y :=
  rfl

end Agreement

end AlgebraicGeometry.RingedSite.Raised

end
