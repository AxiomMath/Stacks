module

public import StacksFrontier.AlgebraicGeometry.NormalizationQuotientDirectSum.SkyscraperMap

/-!
# Skyscraper decomposition of a module supported on a closed discrete set

An `O_X`-module whose stalks vanish outside a closed subset `Z` carrying the discrete induced
topology is the direct sum, indexed by `Z`, of the skyscraper modules of its stalks at the
points of `Z`.  This is the sheaf-theoretic content of
[Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)(2), where `Z` is the singular
locus of a reduced one-dimensional Nagata scheme.

## Main definitions

* `moduleToSkyscraperModule` is the canonical morphism of *sheaves* of modules
  `M ⟶ skyscraperModule X x M_x`, the unit of `SkyscraperMap` followed by the sheafification
  unit.

## Main results

* `stalk_map_moduleToSkyscraperPOM_isIso`: the unit is an isomorphism on the stalk at `x`.
* `sheafify_map_isIso_of_stalk_map_isIso`: sheafifying a stalkwise isomorphism of presheaves
  of modules gives an isomorphism of modules.
* `sheaf_iso_coproduct_skyscraper_of_closed_discrete_support` is the decomposition.

## Implementation notes

The comparison is built as a composite of three isomorphisms: the module maps to the
sheafification of the *product* of the skyscrapers over `Z` (a stalkwise isomorphism, by the
unit at the points of `Z` and by vanishing elsewhere); the coproduct-to-product comparison of
the skyscrapers is a stalkwise isomorphism, because a small enough open set around any point
meets the closed discrete set `Z` at most once, so all but one factor vanishes there; and
sheafification preserves coproducts.  The index set `Z` need not be finite — the biproduct
comparison is only ever used after evaluating on one open set, where all but one factor is
zero.

Each `IsIso` of a composite is supplied explicitly through `IsIso.comp_isIso'` rather than
left to instance search, which does not find it across the `def`s `TopCat.Presheaf` and
`Scheme.Modules`; likewise the functoriality rewrites are stated as named `have`s and chained
with `Eq.trans`, since `rw` fails on them for the same reason.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum

open Stacks.AlgebraicGeometry.NormalizationQuotient

variable {X : Scheme.{u}} (M : X.Modules) (x : X)

/-- The underlying presheaf morphism of `moduleToSkyscraperPOM` is `toSkyscraperPsh`. -/
public theorem toPresheaf_map_moduleToSkyscraperPOM :
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (moduleToSkyscraperPOM M x) =
      toSkyscraperPsh M x := by
  refine NatTrans.ext (funext fun U => ?_)
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ => rfl)

/-- On a germ, the stalk map of `moduleToSkyscraperPOM` is the germ of the component of
`toSkyscraperApp`. -/
public theorem stalkFunctor_map_moduleToSkyscraperPOM_germ (U : Opens X.carrier) (hx : x ∈ U)
    (s : M.val.presheaf.obj (op U)) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (moduleToSkyscraperPOM M x)))
          (TopCat.Presheaf.germ M.val.presheaf U x hx s) =
      TopCat.Presheaf.germ (OXModule.skyscraperPOM x (OXModule.stalk M x)).presheaf U x hx
        (toSkyscraperApp M x (op U) s) := by
  rw [toPresheaf_map_moduleToSkyscraperPOM]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (toSkyscraperPsh M x) s

/-- The stalk map at `x` of the canonical map from `M` to the skyscraper of `M_x` is an
isomorphism of abelian groups. -/
public theorem stalk_map_moduleToSkyscraperPOM_isIso :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (moduleToSkyscraperPOM M x))) := by
  classical
  set f := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (moduleToSkyscraperPOM M x)) with hf
  set e := OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x
    (OXModule.stalk M x) with he'
  have he : ∀ a : ↑(TopCat.Presheaf.stalk M.val.presheaf x), e (f a) = a := by
    intro a
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf a
    rw [hf, stalkFunctor_map_moduleToSkyscraperPOM_germ M x U hxU s, he',
      OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ x
        (OXModule.stalk M x) (op U) hxU]
    exact toSkyscraperApp_leg_apply M x (op U) hxU s
  exact (ConcreteCategory.isIso_iff_bijective f).2
    ⟨fun a b h => (he a).symm.trans ((congrArg e h).trans (he b)),
      fun b => ⟨e b, e.injective (he (e b))⟩⟩

/-- The canonical map from a module to the skyscraper module whose value is its stalk at `x`. -/
public def moduleToSkyscraperModule : M ⟶ skyscraperModule X x (OXModule.stalk M x) :=
  ⟨moduleToSkyscraperPOM M x ≫
    OXModule.sheafifyUnitHom (OXModule.skyscraperPOM x (OXModule.stalk M x))⟩

variable {M x}

/-- The stalk map of the unit from a presheaf of modules to its sheafification is an
isomorphism of abelian groups. -/
private theorem isIso_stalkFunctor_map_sheafifyUnitPshMap (y : X)
    (P : PresheafOfModules.{u} X.ringCatSheaf.obj) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      (OXModule.sheafifyUnitPshMap P)) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (OXModule.sheafifyStalkLinearEquiv y P).bijective

/-- Sheafifying a map of presheaves of modules that is a stalkwise isomorphism produces an
isomorphism of modules. -/
public theorem sheafify_map_isIso_of_stalk_map_isIso
    {P Q : PresheafOfModules.{u} X.ringCatSheaf.obj} (f : P ⟶ Q)
    (h : ∀ y : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f))) :
    IsIso (OXModule.sheafify.map f) := by
  apply module_isIso_of_stalk_map_isIso
  intro y
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  have hisoP := isIso_stalkFunctor_map_sheafifyUnitPshMap y P
  have hisoQ := isIso_stalkFunctor_map_sheafifyUnitPshMap y Q
  have hisoc : IsIso (T.map ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f) ≫
      T.map (OXModule.sheafifyUnitPshMap Q)) := IsIso.comp_isIso' (h y) hisoQ
  refine @IsIso.of_isIso_fac_left _ _ _ _ _
    (T.map (OXModule.sheafifyUnitPshMap P)) _
    (T.map ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f) ≫
      T.map (OXModule.sheafifyUnitPshMap Q)) hisoP hisoc ?_
  have h1 : T.map (OXModule.sheafifyUnitPshMap P) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
            (OXModule.sheafify.map f).val) =
      T.map (OXModule.sheafifyUnitPshMap P ≫
        (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          (OXModule.sheafify.map f).val) := (T.map_comp _ _).symm
  have h2 : T.map ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f) ≫
        T.map (OXModule.sheafifyUnitPshMap Q) =
      T.map ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f ≫
        OXModule.sheafifyUnitPshMap Q) := (T.map_comp _ _).symm
  exact h1.trans
    ((congrArg T.map (CategoryTheory.toSheafify_naturality _ _).symm).trans h2.symm)

/-- **The skyscraper decomposition.** A module on a scheme whose stalks vanish outside a closed
discrete subset `Z` is the direct sum over `Z` of the skyscrapers of its stalks. -/
public theorem sheaf_iso_coproduct_skyscraper_of_closed_discrete_support
    (M : X.Modules) (Z : Set X) (hZ : IsClosed Z) [DiscreteTopology Z]
    (hM : ∀ y ∉ Z, IsZero (OXModule.stalk M y)) :
    Nonempty (M ≅ ∐ fun z : Z => skyscraperModule X z.1 (OXModule.stalk M z.1)) := by
  classical
  let : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : HasColimitsOfSize.{u, u} X.Modules := inferInstance
  let R := X.ringCatSheaf.obj
  let S : Z → PresheafOfModules.{u} R :=
    fun z => OXModule.skyscraperPOM z.1 (OXModule.stalk M z.1)
  let P := ∏ᶜ S
  let A := PresheafOfModules.toPresheaf R
  let f : M.val ⟶ P := Pi.lift fun z => moduleToSkyscraperPOM M z.1
  let c : ∐ S ⟶ P := Sigma.desc (Pi.ι S)
  let G (V : X.Opens) := PresheafOfModules.evaluation R (op V) ⋙
    forget₂ (ModuleCat (R.obj (op V))) AddCommGrpCat
  have hz (V : X.Opens) (z : Z) (hzV : z.1 ∉ V) : IsZero ((G V).obj (S z)) := by
    exact Functor.map_isZero (forget₂ (ModuleCat (R.obj (op V))) AddCommGrpCat)
      (skyscraperPOM_obj_isZero_of_not_mem z.1 (OXModule.stalk M z.1) V hzV)
  have hc (y : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      (A.map c)) := by
    obtain ⟨U, hyU, hU⟩ := exists_open_meets_closed_discrete_at_most_one Z hZ y
    apply stalk_map_isIso_of_locally_isIso (A.map c) y U hyU
    intro V hVU hyV
    change IsIso ((G V).map c)
    apply map_coproductToProduct_isIso S (G V)
    intro i j hi hj
    have hiV : i.1 ∈ V := by_contra fun hcon => hi (hz V i hcon)
    have hjV : j.1 ∈ V := by_contra fun hcon => hj (hz V j hcon)
    exact Subtype.ext ((hU i.1 i.2 (hVU hiV)).trans (hU j.1 j.2 (hVU hjV)).symm)
  have hf (y : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      (A.map f)) := by
    let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    obtain ⟨U, hyU, hU⟩ := exists_open_meets_closed_discrete_at_most_one Z hZ y
    by_cases hyZ : y ∈ Z
    · let z : Z := ⟨y, hyZ⟩
      have hp : IsIso (T.map (A.map (Pi.π S z))) := by
        apply stalk_map_isIso_of_locally_isIso _ y U hyU
        intro V hVU hyV
        change IsIso ((G V).map (Pi.π S z))
        exact isIso_fan_π_of_isZero _
          (isLimitOfPreserves (G V) (limit.isLimit (Discrete.functor S))) z fun j hj =>
            hz V j fun hjV => hj (Subtype.ext (hU j.1 j.2 (hVU hjV)))
      have heq : T.map (A.map f) ≫ T.map (A.map (Pi.π S z)) =
          T.map (A.map (moduleToSkyscraperPOM M y)) := by
        rw [← T.map_comp, ← A.map_comp]
        simp [f, z]
      have := stalk_map_moduleToSkyscraperPOM_isIso M y
      exact IsIso.of_isIso_fac_right heq
    · have hPz : IsZero (TopCat.Presheaf.stalk (A.obj P) y) := by
        apply stalk_isZero_of_locally_isZero _ y U hyU
        intro V hVU hyV
        apply IsLimit.isZero_pt (isLimitOfPreserves (G V) (limit.isLimit (Discrete.functor S)))
        refine (Functor.isZero_iff _).2 fun ⟨j⟩ => ?_
        exact hz V j fun hjV => hyZ ((hU j.1 j.2 (hVU hjV)) ▸ j.2)
      have hMy : IsZero (TopCat.Presheaf.stalk M.val.presheaf y) :=
        AddCommGrpCat.isZero_iff_subsingleton.mpr
          (ModuleCat.isZero_iff_subsingleton.mp (hM y hyZ))
      exact hMy.isIso hPz _
  let g : M ⟶ OXModule.sheafify.obj P := ⟨f ≫ OXModule.sheafifyUnitHom P⟩
  have : IsIso g := by
    apply module_isIso_of_stalk_map_isIso
    intro y
    let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    have hisoP := isIso_stalkFunctor_map_sheafifyUnitPshMap y P
    change IsIso (T.map (A.map f ≫ OXModule.sheafifyUnitPshMap P))
    have hcomp : T.map (A.map f ≫ OXModule.sheafifyUnitPshMap P) =
        T.map (A.map f) ≫ T.map (OXModule.sheafifyUnitPshMap P) := T.map_comp _ _
    rw [hcomp]
    exact IsIso.comp_isIso' (hf y) hisoP
  have : IsIso (OXModule.sheafify.map c) := sheafify_map_isIso_of_stalk_map_isIso c hc
  have : PreservesColimitsOfSize.{u, u} (OXModule.sheafify (X := X.toRingedSpace)) := by
    dsimp [OXModule.sheafify]
    infer_instance
  have : HasCoproduct (fun z : Z =>
      (OXModule.sheafify : PresheafOfModules.{u} R ⥤ X.Modules).obj (S z)) :=
    inferInstanceAs (HasCoproduct (fun z : Z =>
      skyscraperModule X z.1 (OXModule.stalk M z.1)))
  exact ⟨asIso g ≪≫ (asIso (OXModule.sheafify.map c)).symm ≪≫
    PreservesCoproduct.iso (OXModule.sheafify : PresheafOfModules.{u} R ⥤ X.Modules) S⟩

end Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum

end
