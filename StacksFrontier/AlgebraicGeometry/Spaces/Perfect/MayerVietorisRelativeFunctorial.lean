module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRelative
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality in `E` of the relative Mayer–Vietoris triangle

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let
`(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square on `X`, with intersection
`P = U ×_X V`.  Write `a = f|_U`, `b = f|_V` and `c = f|_P`.  Stacks 08JK asserts two things:
that every object `E` of `D(𝒪_X)` sits in a distinguished triangle

`Rf_*E ⟶ Ra_*(E|_U) ⊕ Rb_*(E|_V) ⟶ Rc_*(E|_{U ×_X V}) ⟶ (Rf_*E)[1]`

in `D(𝒪_Y)`, and that this triangle is **functorial in `E`**.  The first assertion is in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRelative`.  This module proves the
second: the five morphisms are *natural transformations* of the four derived functors, and the
triangle they assemble is distinguished at every object, so that a morphism `φ : E ⟶ E'` of
`D(𝒪_X)` induces a morphism of the two triangles, with components `Rf_*φ`, `Ra_*φ ⊕ Rb_*φ` and
`Rc_*φ`.

## Main results

* `CategoryTheory.PushforwardMayerVietoris.mapRightDerivedComparison`: the comparison
  `Ψ(-) ⟶ RΨ(Q -)` of a right derived functor with the functor applied degreewise to a cochain
  complex, as a natural transformation; it is invertible at a K-injective complex, which is
  Stacks 070K read naturally rather than at one object.
* `CategoryTheory.PushforwardMayerVietoris.mapMayerVietorisShortComplex` and
  `…shortExact_mapMayerVietorisShortComplex`: the Mayer–Vietoris short exact sequence of
  cochain complexes at a termwise injective complex, together with the morphism of short
  complexes `…mapMayerVietorisShortComplexMap` induced by a map of cochain complexes.
* `CategoryTheory.PushforwardMayerVietoris`
  `.exists_natTrans_mem_distTriang_mapMayerVietoris_of_functorialResolution`:
  the abstract form.  Natural transformations `R_X ⟶ R_U`, `R_X ⟶ R_V`, `R_U ⟶ R_P`,
  `R_V ⟶ R_P` and `R_P ⟶ R_X ⋙ (-)[1]` whose triangle is distinguished at *every* object of
  `D(A)`.
* `AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsRelativeMayerVietoris_`
  `unconditional`: **Stacks 08JK**, the functoriality in `E`.
* `AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsRelativeMayerVietoris`: the same
  conclusion, with the direct-image Mayer–Vietoris sequence `hMV` (part (1) of Stacks 08GW) as a
  hypothesis at every module.

## Implementation notes

The triangle at `E` is built from a K-injective, termwise injective representative of `E`.  The
K-injective resolution of Stacks 079P is taken *functorial*
(`Stacks.Injectives.FunctorialKInjectiveResolution`), so that each of the five morphisms is a
natural transformation of functors on `CochainComplex A ℤ` — the connecting one by
`DerivedCategory.triangleOfSESδ_naturality` — and these descend to the derived category through
the localization `DerivedCategory.Q` (`CategoryTheory.Localization.liftNatTrans`), with the
lifting data `…derivedResolutionLiftingIso`.

No exactness of `G` is used: the Mayer–Vietoris sequence at an injective object splits, and a
split short exact sequence survives any additive functor.

Since the functorial resolution is termwise injective, the direct-image Mayer–Vietoris sequence

`0 ⟶ M ⟶ j_{U,*}M|_U ⊕ j_{V,*}M|_V ⟶ j_{P,*}M|_P ⟶ 0`

of part (1) of Stacks 08GW is needed only at injective modules, where it is
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris_of_injective`.  That rests on
part (1) of Stacks 08GV, the extension-by-zero short exact sequence
`0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`, for the extension functors
`AlgebraicGeometry.Space.etaleModuleLowerShriek` (Stacks 03DI) and the stalk computation of
Equation 08GU.

## References

* [Stacks Project, Tag 08JK](https://stacks.math.columbia.edu/tag/08JK)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 0152](https://stacks.math.columbia.edu/tag/0152)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe w w' v v' u u'

namespace CategoryTheory.PushforwardMayerVietoris

/-! ### The Mayer–Vietoris short exact sequence of cochain complexes -/

section Cochain

variable {A : Type u} [Category.{v} A] [Abelian A] {C : Type u'} [Category.{v'} C] [Abelian C]
  {ΦU ΦV ΦP : A ⥤ A} [ΦU.Additive] [ΦV.Additive] [ΦP.Additive]
  (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV) (dU : ΦU ⟶ ΦP) (dV : ΦV ⟶ ΦP)
  (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
    biprod.desc (dU.app M) (-(dV.app M)) = 0)
  (G : A ⥤ C) [G.Additive]

/-- The natural transformation `G(-) ⟶ G(Φ(-))` of functors on cochain complexes obtained by
applying the additive functor `G` to a natural transformation `η : 𝟭 ⟶ Φ` degreewise.  Its
component at `K` is `CategoryTheory.PushforwardMayerVietoris.mapUnitCochainMap`. -/
def mapUnitNatTrans {Φ : A ⥤ A} [Φ.Additive] (η : 𝟭 A ⟶ Φ) :
    G.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (Φ ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) where
  app K := mapUnitCochainMap G η K
  naturality K K' ψ := by
    ext n
    dsimp
    rw [← G.map_comp, ← G.map_comp]
    exact congrArg G.map (η.naturality (ψ.f n))

/-- The component of `mapUnitNatTrans G η` at a cochain complex `K`. -/
@[simp]
lemma mapUnitNatTrans_app {Φ : A ⥤ A} [Φ.Additive] (η : 𝟭 A ⟶ Φ) (K : CochainComplex A ℤ) :
    (mapUnitNatTrans G η).app K = mapUnitCochainMap G η K :=
  rfl

section Eval

variable (K : CochainComplex A ℤ)

/-- An additive functor carries `biprod.lift` to the `biprod.lift` of the images, up to the
canonical isomorphism. -/
private lemma map_biprod_lift_eq_comp_inv {P Q : Type*} [Category* P] [Category* Q] [Preadditive P]
    [Preadditive Q] [HasBinaryBiproducts P] [HasBinaryBiproducts Q] (F : P ⥤ Q) [F.Additive]
    {X Y Z : P} (f : Z ⟶ X) (g : Z ⟶ Y) :
    F.map (biprod.lift f g) =
      biprod.lift (F.map f) (F.map g) ≫ (F.biprodIsoOfAdditive X Y).inv := by
  rw [Iso.eq_comp_inv, Functor.biprodIsoOfAdditive_hom_map_lift]

/-- An additive functor carries `biprod.desc f (-g)` to the `biprod.desc` of the images, up to the
canonical isomorphism. -/
private lemma biprodIsoOfAdditive_inv_comp_map_desc {P Q : Type*} [Category* P] [Category* Q]
    [Preadditive P] [Preadditive Q] [HasBinaryBiproducts P] [HasBinaryBiproducts Q]
    (F : P ⥤ Q) [F.Additive] {X Y Z : P} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (F.biprodIsoOfAdditive X Y).inv ≫ F.map (biprod.desc f (-g)) =
      biprod.desc (F.map f) (-F.map g) := by
  rw [Functor.biprodIsoOfAdditive_inv_map_desc, F.map_neg]

/-- The degreewise evaluation of a cochain complex of objects of `C`. -/
private abbrev evAt (n : ℤ) : CochainComplex C ℤ ⥤ C :=
  HomologicalComplex.eval C (ComplexShape.up ℤ) n

include hzero in
/-- The Mayer–Vietoris sequence of cochain complexes is a complex. -/
lemma zero_mapMayerVietorisCochain :
    biprod.lift (mapUnitCochainMap G ηU K) (mapUnitCochainMap G ηV K) ≫
      biprod.desc ((NatTrans.mapHomologicalComplex (Functor.whiskerRight dU G)
          (ComplexShape.up ℤ)).app K)
        (-((NatTrans.mapHomologicalComplex (Functor.whiskerRight dV G)
          (ComplexShape.up ℤ)).app K)) = 0 := by
  ext n
  change (evAt (C := C) n).map (_ ≫ _) = 0
  rw [(evAt (C := C) n).map_comp, map_biprod_lift_eq_comp_inv, assoc,
    biprodIsoOfAdditive_inv_comp_map_desc]
  exact zero_map_mayerVietoris ηU ηV dU dV hzero G (K.X n)

include hzero in
/-- **The Mayer–Vietoris short complex of cochain complexes**: the image under an additive
functor `G` of the Mayer–Vietoris sequence of `Φ_U`, `Φ_V`, `Φ_P`, taken degreewise at a
cochain complex `K`. -/
abbrev mapMayerVietorisShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (biprod.lift (mapUnitCochainMap G ηU K) (mapUnitCochainMap G ηV K))
    (biprod.desc ((NatTrans.mapHomologicalComplex (Functor.whiskerRight dU G)
        (ComplexShape.up ℤ)).app K)
      (-((NatTrans.mapHomologicalComplex (Functor.whiskerRight dV G)
        (ComplexShape.up ℤ)).app K)))
    (zero_mapMayerVietorisCochain ηU ηV dU dV hzero G K)

include hzero in
/-- **The Mayer–Vietoris short complex of cochain complexes is short exact at a termwise
injective complex.**  The Mayer–Vietoris sequence is demanded at the *injective* objects only. -/
lemma shortExact_mapMayerVietorisShortComplex
    (hMV : ∀ M, Injective M → (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (hinj : ∀ n, Injective (K.X n)) :
    (mapMayerVietorisShortComplex ηU ηV dU dV hzero G K).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
  refine ShortComplex.shortExact_of_iso ?_
    (shortExact_map_mayerVietoris_at_injective ηU ηV dU dV hzero G (K.X n) (hinj n)
      (hMV (K.X n) (hinj n)))
  refine ShortComplex.isoMk (Iso.refl _)
    ((evAt (C := C) n).biprodIsoOfAdditive
      (((ΦU ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      (((ΦV ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm (Iso.refl _) ?_ ?_
  · dsimp
    rw [id_comp]
    exact map_biprod_lift_eq_comp_inv (evAt (C := C) n) _ _
  · dsimp
    rw [comp_id]
    exact biprodIsoOfAdditive_inv_comp_map_desc (evAt (C := C) n) _ _

end Eval

include hzero in
/-- **The Mayer–Vietoris short complex of cochain complexes is functorial.**  A map of cochain
complexes induces a morphism of the two short complexes. -/
def mapMayerVietorisShortComplexMap {K K' : CochainComplex A ℤ} (ψ : K ⟶ K') :
    mapMayerVietorisShortComplex ηU ηV dU dV hzero G K ⟶
      mapMayerVietorisShortComplex ηU ηV dU dV hzero G K' where
  τ₁ := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ
  τ₂ := biprod.map (((ΦU ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)
    (((ΦV ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)
  τ₃ := ((ΦP ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ
  comm₁₂ := by
    dsimp [mapMayerVietorisShortComplex]
    refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp only [assoc, biprod.lift_fst, biprod.lift_snd, biprod.map_fst, biprod.map_snd,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc] <;>
      exact (mapUnitNatTrans G _).naturality ψ
  comm₂₃ := by
    dsimp [mapMayerVietorisShortComplex]
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp only [biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc]
      exact (NatTrans.mapHomologicalComplex (Functor.whiskerRight dU G)
        (ComplexShape.up ℤ)).naturality ψ
    · simp only [biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc,
        Preadditive.neg_comp, Preadditive.comp_neg, neg_inj]
      exact (NatTrans.mapHomologicalComplex (Functor.whiskerRight dV G)
        (ComplexShape.up ℤ)).naturality ψ

variable [HasDerivedCategory.{w'} C]

include hzero in
/-- **The Mayer–Vietoris triangle of a cochain complex, with its connecting morphism named.**
This is `CategoryTheory.PushforwardMayerVietoris`
`.mem_distTriang_mapMayerVietoris_of_degreewise_shortExact` with the existential witness
replaced by the connecting morphism `DerivedCategory.triangleOfSESδ` of the short exact
sequence itself. -/
theorem mem_distTriang_mapMayerVietorisTriangle (K : CochainComplex A ℤ)
    (hS : (mapMayerVietorisShortComplex ηU ηV dU dV hzero G K).ShortExact) :
    Triangle.mk
        (biprod.lift (DerivedCategory.Q.map (mapUnitCochainMap G ηU K))
          (DerivedCategory.Q.map (mapUnitCochainMap G ηV K)))
        (biprod.desc
          (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (Functor.whiskerRight dU G) (ComplexShape.up ℤ)).app K))
          (-(DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (Functor.whiskerRight dV G) (ComplexShape.up ℤ)).app K))))
        (DerivedCategory.triangleOfSESδ hS) ∈ distTriang (DerivedCategory C) := by
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ (Iso.refl _)
      (DerivedCategory.Q.biprodIsoOfAdditive
        (((ΦU ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ΦV ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm
      (Iso.refl _) ?_ ?_ ?_)
  · exact ((map_biprod_lift_eq_comp_inv (DerivedCategory.Q (C := C)) _ _).symm.trans
      (id_comp _).symm :)
  · exact ((comp_id _).trans
      (biprodIsoOfAdditive_inv_comp_map_desc (DerivedCategory.Q (C := C)) _ _).symm :)
  · change DerivedCategory.triangleOfSESδ hS ≫
        (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
          (𝟙 (DerivedCategory.Q.obj
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) =
      𝟙 _ ≫ DerivedCategory.triangleOfSESδ hS
    rw [CategoryTheory.Functor.map_id, comp_id, id_comp]

end Cochain

/-! ### The comparison of a right derived functor with the degreewise functor -/

section Comparison

variable {A : Type u} [Category.{v} A] [Abelian A] {C : Type u'} [Category.{v'} C] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} C]

/-- A natural isomorphism of additive functors, applied degreewise to cochain complexes. -/
def mapHomologicalComplexNatIso {F F' : A ⥤ C} [F.Additive] [F'.Additive] (θ : F ≅ F') :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F'.mapHomologicalComplex (ComplexShape.up ℤ) where
  hom := NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)
  inv := NatTrans.mapHomologicalComplex θ.inv (ComplexShape.up ℤ)
  hom_inv_id := by ext K n; simp
  inv_hom_id := by ext K n; simp

/-- **Stacks 070K as a natural transformation.**  The comparison from the functor applied
degreewise to a cochain complex to the right derived functor at its image in the derived
category: `Q(Ψ K) ⟶ RΨ(Q K)`, natural in `K`, precomposed with a natural isomorphism
`θ : F ≅ Ψ`. -/
def mapRightDerivedComparison (F : A ⥤ C) [F.Additive] {Ψ : A ⥤ C} [Ψ.Additive] (θ : F ≅ Ψ)
    (RF : DerivedCategory A ⥤ DerivedCategory C)
    (α : Ψ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
  Functor.whiskerRight (mapHomologicalComplexNatIso θ).hom DerivedCategory.Q ≫
    Functor.whiskerLeft (Ψ.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso C).inv ≫
    Functor.whiskerRight (Ψ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (ComplexShape.up ℤ)) α ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom RF

/-- The component of `mapRightDerivedComparison F θ RF α` at a cochain complex `K`. -/
lemma mapRightDerivedComparison_app (F : A ⥤ C) [F.Additive] {Ψ : A ⥤ C} [Ψ.Additive]
    (θ : F ≅ Ψ) (RF : DerivedCategory A ⥤ DerivedCategory C)
    (α : Ψ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) (K : CochainComplex A ℤ) :
    (mapRightDerivedComparison F θ RF α).app K =
      DerivedCategory.Q.map ((mapHomologicalComplexNatIso θ).hom.app K) ≫
        ((DerivedCategory.quotientCompQhIso C).inv.app
            ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Ψ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
          α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
          RF.map ((DerivedCategory.quotientCompQhIso A).hom.app K)) :=
  rfl

/-- The comparison of `CategoryTheory.PushforwardMayerVietoris.mapRightDerivedComparison` is
invertible at a K-injective complex: that is Stacks 070K. -/
lemma isIso_mapRightDerivedComparison_app
    (hres : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (F : A ⥤ C) [F.Additive] {Ψ : A ⥤ C} [Ψ.Additive] (θ : F ≅ Ψ)
    (RF : DerivedCategory A ⥤ DerivedCategory C)
    (α : Ψ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
    IsIso ((mapRightDerivedComparison F θ RF α).app I) := by
  rw [mapRightDerivedComparison_app]
  have h : ((DerivedCategory.quotientCompQhIso C).inv.app
        ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
      DerivedCategory.Qh.map
        ((Ψ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app I) ≫
      α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≫
      RF.map ((DerivedCategory.quotientCompQhIso A).hom.app I)) =
      (rightDerivedObjIsoOfKInjective hres Ψ inferInstance RF α hRF I hI).hom := rfl
  rw [h]
  infer_instance

end Comparison

/-! ### The functorial triangle -/

section Functorial

variable {A : Type u} [Category.{v} A] [Abelian A] {C : Type u'} [Category.{v'} C] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} C]

/-- The natural isomorphism `Q ≅ Res ⋙ Q` attached to a functorial resolution, given by the
inclusion into the resolution. -/
def resolutionQIso (R : Stacks.Injectives.FunctorialKInjectiveResolution A) :
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ≅
      R.functor ⋙ DerivedCategory.Q :=
  NatIso.ofComponents
    (fun K => haveI := R.quasiIso K; asIso (DerivedCategory.Q.map (R.inclusion.app K)))
    (fun {K K'} ψ => by
      dsimp
      rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
      exact congrArg DerivedCategory.Q.map (R.inclusion.naturality ψ))

/-- **The `Localization.Lifting` datum of a right derived functor.**  The natural isomorphism
`Q ⋙ RΨ ≅ Res ⋙ Ψ(-) ⋙ Q`, built from `Q ≅ Res ⋙ Q` and the comparison of Stacks 070K on the
resolution. -/
def derivedResolutionLiftingIso (R : Stacks.Injectives.FunctorialKInjectiveResolution A)
    (F : A ⥤ C) [F.Additive] {Ψ : A ⥤ C} [Ψ.Additive] (θ : F ≅ Ψ)
    (RF : DerivedCategory A ⥤ DerivedCategory C)
    (α : Ψ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    DerivedCategory.Q ⋙ RF ≅
      R.functor ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := by
  have hres : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i :=
    fun K => ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K, R.quasiIso K⟩
  have : ∀ K : CochainComplex A ℤ,
      IsIso ((Functor.whiskerLeft R.functor (mapRightDerivedComparison F θ RF α)).app K) :=
    fun K => isIso_mapRightDerivedComparison_app hres F θ RF α hRF (R.functor.obj K)
      (R.isKInjective K)
  have : IsIso (Functor.whiskerLeft R.functor (mapRightDerivedComparison F θ RF α)) :=
    NatIso.isIso_of_isIso_app _
  exact Functor.isoWhiskerRight (resolutionQIso R) RF ≪≫
    (asIso (Functor.whiskerLeft R.functor (mapRightDerivedComparison F θ RF α))).symm

/-- **Descent of a natural transformation through the localization.**  A natural
transformation of functors on cochain complexes descends to one of functors on the derived
category as soon as the two targets are presented as lifts, and its value at `Q.obj K` is the
transformation at `K` conjugated by the two lifting isomorphisms.  This is
`CategoryTheory.Localization.liftNatTrans` for `DerivedCategory.Q`, with the lifting data given
explicitly rather than by instance search. -/
lemma exists_natTrans_app_eq_of_liftingIso
    {F₁ F₂ : CochainComplex A ℤ ⥤ DerivedCategory C}
    (R₁ R₂ : DerivedCategory A ⥤ DerivedCategory C)
    (ξ₁ : DerivedCategory.Q ⋙ R₁ ≅ F₁) (ξ₂ : DerivedCategory.Q ⋙ R₂ ≅ F₂) (τ : F₁ ⟶ F₂) :
    ∃ τ' : R₁ ⟶ R₂, ∀ K : CochainComplex A ℤ,
      τ'.app (DerivedCategory.Q.obj K) =
        ξ₁.hom.app K ≫ τ.app K ≫ ξ₂.inv.app K := by
  let h₁ : Localization.Lifting (DerivedCategory.Q (C := A))
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) F₁ R₁ := ⟨ξ₁⟩
  let h₂ : Localization.Lifting (DerivedCategory.Q (C := A))
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) F₂ R₂ := ⟨ξ₂⟩
  exact ⟨Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) F₁ F₂ R₁ R₂ τ,
    fun K => Localization.liftNatTrans_app DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) F₁ F₂ R₁ R₂ τ K⟩

variable {ΦU ΦV ΦP : A ⥤ A} [ΦU.Additive] [ΦV.Additive] [ΦP.Additive]
  (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV) (dU : ΦU ⟶ ΦP) (dV : ΦV ⟶ ΦP)
  (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
    biprod.desc (dU.app M) (-(dV.app M)) = 0)
  (G : A ⥤ C) [G.Additive]
  {ΨX ΨU ΨV ΨP : A ⥤ C} [ΨX.Additive] [ΨU.Additive] [ΨV.Additive] [ΨP.Additive]
  (θX : G ≅ ΨX) (θU : ΦU ⋙ G ≅ ΨU) (θV : ΦV ⋙ G ≅ ΨV) (θP : ΦP ⋙ G ≅ ΨP)

include hzero θX θU θV θP in
/-- **The abstract form of the functoriality in `E` of Stacks 08JK and of Stacks 0CRS.**

The data and hypotheses are those of
`CategoryTheory.PushforwardMayerVietoris.exists_mem_distTriang_mapMayerVietoris`, with the
K-injective resolutions demanded *functorially*, as Stacks 079P supplies in a Grothendieck
abelian category, and with the Mayer–Vietoris sequence demanded at the *injective* objects only,
as in `CategoryTheory.PushforwardMayerVietoris`
`.exists_mem_distTriang_mapMayerVietoris_of_shortExact_at_injectives`.  The five morphisms of the
Mayer–Vietoris triangle are natural transformations of the four right derived functors, and the
triangle they assemble is distinguished at *every* object `E` of `D(A)`.  So a morphism
`E ⟶ E'` induces a morphism of the two triangles. -/
theorem exists_natTrans_mem_distTriang_mapMayerVietoris_of_functorialResolution
    (hres : Nonempty (Stacks.Injectives.FunctorialKInjectiveResolution A))
    (hMV : ∀ M, Injective M → (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (RX RU RV RP : DerivedCategory A ⥤ DerivedCategory C)
    (αX : ΨX.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RX)
    (αU : ΨU.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RU)
    (αV : ΨV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RV)
    (αP : ΨP.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    ∃ (fU : RX ⟶ RU) (fV : RX ⟶ RV) (gU : RU ⟶ RP) (gV : RV ⟶ RP)
      (δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ)),
      ∀ E : DerivedCategory A,
        Triangle.mk (biprod.lift (fU.app E) (fV.app E))
            (biprod.desc (gU.app E) (-(gV.app E))) (δ.app E) ∈
          distTriang (DerivedCategory C) := by
  obtain ⟨R⟩ := hres
  have ξX := derivedResolutionLiftingIso R G θX RX αX hRX
  have ξU := derivedResolutionLiftingIso R (ΦU ⋙ G) θU RU αU hRU
  have ξV := derivedResolutionLiftingIso R (ΦV ⋙ G) θV RV αV hRV
  have ξP := derivedResolutionLiftingIso R (ΦP ⋙ G) θP RP αP hRP
  have hS : ∀ K : CochainComplex A ℤ,
      (mapMayerVietorisShortComplex ηU ηV dU dV hzero G (R.functor.obj K)).ShortExact :=
    fun K => shortExact_mapMayerVietorisShortComplex ηU ηV dU dV hzero G _ hMV
      (fun n => R.injective K n)
  obtain ⟨fU, hfU⟩ := exists_natTrans_app_eq_of_liftingIso RX RU ξX ξU
    (Functor.whiskerLeft R.functor
      (Functor.whiskerRight (mapUnitNatTrans G ηU) DerivedCategory.Q))
  obtain ⟨fV, hfV⟩ := exists_natTrans_app_eq_of_liftingIso RX RV ξX ξV
    (Functor.whiskerLeft R.functor
      (Functor.whiskerRight (mapUnitNatTrans G ηV) DerivedCategory.Q))
  obtain ⟨gU, hgU⟩ := exists_natTrans_app_eq_of_liftingIso RU RP ξU ξP
    (Functor.whiskerLeft R.functor (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (Functor.whiskerRight dU G) (ComplexShape.up ℤ))
      DerivedCategory.Q))
  obtain ⟨gV, hgV⟩ := exists_natTrans_app_eq_of_liftingIso RV RP ξV ξP
    (Functor.whiskerLeft R.functor (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (Functor.whiskerRight dV G) (ComplexShape.up ℤ))
      DerivedCategory.Q))
  obtain ⟨δ, hδ⟩ := exists_natTrans_app_eq_of_liftingIso RP
    (RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ)) ξP
    (Functor.isoWhiskerRight ξX (shiftFunctor (DerivedCategory C) (1 : ℤ)))
    { app := fun K => DerivedCategory.triangleOfSESδ (hS K)
      naturality := fun K K' ψ =>
        (DerivedCategory.triangleOfSESδ_naturality (hS K) (hS K')
          (mapMayerVietorisShortComplexMap ηU ηV dU dV hzero G (R.functor.map ψ))).symm }
  refine ⟨fU, fV, gU, gV, δ, fun E => ?_⟩
  have hQK : Triangle.mk
      (biprod.lift (fU.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E)))
        (fV.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E))))
      (biprod.desc (gU.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E)))
        (-(gV.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E)))))
      (δ.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E))) ∈
      distTriang (DerivedCategory C) := by
    set K := DerivedCategory.Q.objPreimage E
    refine isomorphic_distinguished _
      (mem_distTriang_mapMayerVietorisTriangle ηU ηV dU dV hzero G
        (R.functor.obj K) (hS K)) _
      (Triangle.isoMk _ _ (ξX.app K) (biprod.mapIso (ξU.app K) (ξV.app K)) (ξP.app K)
        ?_ ?_ ?_)
    · refine biprod.hom_ext _ _ ?_ ?_ <;>
        simp [hfU K, hfV K]
    · refine biprod.hom_ext' _ _ ?_ ?_ <;>
        simp [hgU K, hgV K]
    · simp [hδ K]
  refine isomorphic_distinguished _ hQK _
    (Triangle.isoMk _ _ (RX.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm)
      (biprod.mapIso (RU.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm)
        (RV.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm))
      (RP.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm) ?_ ?_ ?_)
  · refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [fU.naturality, fV.naturality]
  · refine biprod.hom_ext' _ _ ?_ ?_ <;>
      simp [gU.naturality, gV.naturality]
  · simp [δ.naturality (DerivedCategory.Q.objObjPreimageIso E).inv]

end Functorial

end CategoryTheory.PushforwardMayerVietoris

namespace AlgebraicGeometry.Space

open CategoryTheory.PushforwardMayerVietoris

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- **Stacks 079P for the modules on an algebraic space, functorially.**  The K-injective
resolution of a complex of `𝒪_F`-modules may be chosen as an endofunctor of cochain complexes
with a natural inclusion, whose values are K-injective with injective terms. -/
theorem nonempty_functorialKInjectiveResolution_modules
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Nonempty (Stacks.Injectives.FunctorialKInjectiveResolution
      (Modules.{u, u} B S hS F hF)) :=
  have _hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS F hF) :=
    isGrothendieckAbelian_modules B S hS F hF
  Stacks.Injectives.exists_functorial_quasiIso_isKInjective.{u} (Modules.{u, u} B S hS F hF)

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {Z : AlgebraicSpaces B S hS} (f : W ⟶ Z)

variable [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS W.1 W.2)]
  [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Z.1 Z.2)]

/-- **The functoriality in `E` of the relative Mayer–Vietoris triangle of Stacks 08JK, with
part (1) of Stacks 08GW as a hypothesis.**

The data and hypotheses are those of
`AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris`, the matching form of
the triangle itself: `f : X ⟶ Y` a morphism of algebraic spaces over a scheme `S`,
`(U ⊆ X, j_V : V ⟶ X)` an elementary distinguished square on `X`, `P = U ×_X V`, and
`a = f|_U`, `b = f|_V`, `c = f|_P` the restrictions of `f`; `Rf_*`, `Ra_*((-)|_U)`,
`Rb_*((-)|_V)` and `Rc_*((-)|_P)` right derived functors of `f_*`, `a_*((-)|_U)`,
`b_*((-)|_V)` and `c_*((-)|_P)` with their comparisons; and `hMV`, part (1) of Stacks 08GW.

Then the five morphisms of the Mayer–Vietoris triangle

`Rf_*E ⟶ Ra_*(E|_U) ⊕ Rb_*(E|_V) ⟶ Rc_*(E|_{U ×_X V}) ⟶ (Rf_*E)[1]`

are **natural transformations** of the four derived functors `D(𝒪_X) ⥤ D(𝒪_Y)`, and the
triangle is distinguished at every object `E` of `D(𝒪_X)`.  So a morphism `φ : E ⟶ E'` of
`D(𝒪_X)` induces a morphism of the two triangles, with components `Rf_*φ`,
`Ra_*φ ⊕ Rb_*φ` and `Rc_*φ`.  The resolutions used are the functorial K-injective resolutions of
Stacks 079P (`…nonempty_functorialKInjectiveResolution_modules`). -/
theorem exists_natTrans_mem_distTriang_edsRelativeMayerVietoris
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αX : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙
        modulePushforward B S hS (edsOpenHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙
        modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙
        modulePushforward B S hS (edsInterHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (ηU : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushOpen B S hS hsq)
    (ηV : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushEtale B S hS hsq)
    (dU : edsRestrictPushOpen B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (dV : edsRestrictPushEtale B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
      biprod.desc (dU.app M) (-(dV.app M)) = 0)
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact) :
    ∃ (fU : RX ⟶ RU) (fV : RX ⟶ RV) (gU : RU ⟶ RP) (gV : RV ⟶ RP)
      (δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) (1 : ℤ)),
      ∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
        Triangle.mk (biprod.lift (fU.app E) (fV.app E))
            (biprod.desc (gU.app E) (-(gV.app E))) (δ.app E) ∈
          distTriang (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :=
  exists_natTrans_mem_distTriang_mapMayerVietoris_of_functorialResolution ηU ηV dU dV hzero
    (modulePushforward B S hS f) (Iso.refl _)
    (edsRestrictPushOpenPushforwardIso B S hS hsq f)
    (edsRestrictPushEtalePushforwardIso B S hS hsq f)
    (edsRestrictPushInterPushforwardIso B S hS hsq f)
    (nonempty_functorialKInjectiveResolution_modules B S hS W.1 W.2) (fun M _ => hMV M)
    RX RU RV RP αX αU αV αP hRX hRU hRV hRP

end Square

/-! ### The functoriality with nothing granted -/

section Unconditional

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))

variable {Z : AlgebraicSpaces B S hS} (f : W ⟶ Z)
  [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS W.1 W.2)]
  [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Z.1 Z.2)]

include adjU adjV adjP in
/-- **Stacks 08JK, the functoriality in `E`**, for any functors `shriekU`, `shriekV`,
`shriekP` left adjoint to restriction along the three étale morphisms of the square. -/
theorem exists_natTrans_mem_distTriang_edsRelativeMayerVietoris_of_shriek
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αX : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙
        modulePushforward B S hS (edsOpenHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙
        modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙
        modulePushforward B S hS (edsInterHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))) :
    ∃ (fU : RX ⟶ RU) (fV : RX ⟶ RV) (gU : RU ⟶ RP) (gV : RV ⟶ RP)
      (δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) (1 : ℤ)),
      ∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
        Triangle.mk (biprod.lift (fU.app E) (fV.app E))
            (biprod.desc (gU.app E) (-(gV.app E))) (δ.app E) ∈
          distTriang (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :=
  exists_natTrans_mem_distTriang_mapMayerVietoris_of_functorialResolution
    (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
      ((edsAdjInter B S hS hsq).comp adjP) (edsShriekOpenComparison B S hS hsq adjU adjP))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
      ((edsAdjInter B S hS hsq).comp adjP) (edsShriekEtaleComparison B S hS hsq adjV adjP))
    (zero_edsRestrictPushMayerVietoris B S hS hsq adjU adjV adjP
      (edsShriekOpenComparison B S hS hsq adjU adjP)
      (edsShriekEtaleComparison B S hS hsq adjV adjP)
      (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP))
    (modulePushforward B S hS f)
    (Iso.refl _) (edsRestrictPushOpenPushforwardIso B S hS hsq f)
    (edsRestrictPushEtalePushforwardIso B S hS hsq f)
    (edsRestrictPushInterPushforwardIso B S hS hsq f)
    (nonempty_functorialKInjectiveResolution_modules B S hS W.1 W.2)
    (fun M hM => shortExact_edsRestrictPushMayerVietoris_of_injective B S hS hsq
      adjU adjV adjP M hM)
    RX RU RV RP αX αU αV αP hRX hRU hRV hRP

/-- **Stacks 08JK, the functoriality in `E`.**

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let
`(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square on `X`, let `P = U ×_X V`, and let
`Rf_*`, `Ra_*((-)|_U)`, `Rb_*((-)|_V)`, `Rc_*((-)|_P)` be right derived functors of the four
functors of the square, with their comparisons.  Then the five morphisms of the Mayer–Vietoris
triangle

`Rf_*E ⟶ Ra_*(E|_U) ⊕ Rb_*(E|_V) ⟶ Rc_*(E|_{U ×_X V}) ⟶ (Rf_*E)[1]`

are **natural transformations** of the four derived functors `D(𝒪_X) ⥤ D(𝒪_Y)`, and the triangle
is distinguished at every object `E` of `D(𝒪_X)`.  So a morphism `φ : E ⟶ E'` induces a
morphism of the two triangles.

The direct-image Mayer–Vietoris sequence is used only at *injective* modules — the functorial
resolution of Stacks 079P is termwise injective — where it is proved from part (1) of
Stacks 08GV: `AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris_of_injective`.  The
first assertion of Stacks 08JK is
`AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris_unconditional`. -/
@[stacks 08JK "SECOND ASSERTION: the distinguished triangle is FUNCTORIAL IN E. The five
morphisms are natural transformations of the four right derived functors D(O_X) -> D(O_Y) and
the triangle is distinguished at EVERY E, with no hypothesis beyond the square, f and those
functors. The FIRST ASSERTION is exists_mem_distTriang_edsRelativeMayerVietoris_unconditional in
the sibling module. Proof route and provenance are in this theorem's docstring"]
theorem exists_natTrans_mem_distTriang_edsRelativeMayerVietoris_unconditional
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αX : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙
        modulePushforward B S hS (edsOpenHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙
        modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙
        modulePushforward B S hS (edsInterHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))) :
    ∃ (fU : RX ⟶ RU) (fV : RX ⟶ RV) (gU : RU ⟶ RP) (gV : RV ⟶ RP)
      (δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) (1 : ℤ)),
      ∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
        Triangle.mk (biprod.lift (fU.app E) (fV.app E))
            (biprod.desc (gU.app E) (-(gV.app E))) (δ.app E) ∈
          distTriang (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :=
  exists_natTrans_mem_distTriang_edsRelativeMayerVietoris_of_shriek B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq))
    f RX RU RV RP αX αU αV αP hRX hRU hRV hRP

end Unconditional

end AlgebraicGeometry.Space

end
