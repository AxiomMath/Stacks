module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalInvertible
public import StacksFrontier.AlgebraicGeometry.QuasicoherentExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Tautological data from an invertible quotient, and the base-change clause beyond rank one

A tautological datum on `𝐏(F)`, `Stacks.RelativeProj.TautologicalDatum`, is an invertible
module on `𝐏(F)` together with a surjection onto it from `π^*F`. It carries no graded
compatibility, so an *invertible quotient of `F` on the base* already produces one: if
`q : F ⟶ L` is an epimorphism onto an invertible `L`, then `π^*L` is invertible and `π^*q` is
an epimorphism onto it, because `π^*` is a left adjoint.

That is `Stacks.RelativeProj.TautologicalDatum.ofInvertibleQuotient`;
`Stacks.RelativeProj.TautologicalDatum.ofInvertible` is the case `L = F`, `q = 𝟙`. The module
need not be invertible and the universal surjection need not be an identity morphism: at
`F = M ⊞ M` and `q = biprod.fst` it is the pullback of a projection out of a biproduct.

## Main definitions

* `Stacks.RelativeProj.TautologicalDatum.ofInvertibleQuotient`: the tautological datum `π^*L`
  attached to an epimorphism `q : F ⟶ L` onto an invertible module on the base, with `π^*q` as
  its universal surjection.
* `Stacks.RelativeProj.pullbackModuleBaseChangeIso`: the canonical identification
  `b^*π^*M ≅ π'^*M'` for an arbitrary module `M` on the base and an identification
  `M' ≅ g^*M`, `b` being the base-change comparison morphism of projective bundles. At `M = E`
  it is `Stacks.RelativeProj.tautologicalBaseChangeIso`, by `rfl`.
* `Stacks.RelativeProj.tautologicalDatumBiprodSelf` and
  `Stacks.RelativeProj.tautologicalDatumBiprodSelfPullback`: the data on the projective bundle
  of `M ⊞ M` for an invertible `M` over an affine base, and on the base change of that module,
  whose universal surjections are `π^*biprod.fst` and `π'^*(g^*biprod.fst)`.

## Main results

* `Stacks.RelativeProj.pullbackModuleBaseChangeIso_naturality`: the identification is natural
  in the module argument, for a pair of morphisms compatible with the two identifications.
* `Stacks.RelativeProj.TautologicalDatum.baseChange_ofInvertibleQuotient_univ_comp_iso_hom`:
  the base change of the datum of an invertible quotient is the datum of the base-changed
  invertible quotient.
* `Stacks.RelativeProj.projectiveBundleBaseChange_tautological_ofInvertibleQuotient`: the
  base-change comparison of Stacks Tag 0B3V on universal quotients, for the tautological data
  attached to compatible invertible quotients, with no invertibility hypothesis on the modules.
  Its rank-one case is
  `Stacks.RelativeProj.projectiveBundleBaseChange_tautological_ofInvertible_of_quotient`.
* `Stacks.RelativeProj.projectiveBundleBaseChange_tautological_biprodSelf`: that clause at
  `M ⊞ M` and its pullback, for an arbitrary morphism of schemes into an affine base.
* `Stacks.RelativeProj.SheafOfModules.isQuasicoherent_biprod_of_isAffine`: a biproduct of
  quasi-coherent modules on an affine scheme is quasi-coherent.
* `Stacks.RelativeProj.isZero_of_isIso_biprod_fst`: the first projection of a binary biproduct
  of an object with itself is an isomorphism only if the object is a zero object.

## Implementation notes

The data constructed here are not universal: their twist `π^*L` is pulled back from the base,
whereas `𝒪_{𝐏(F)}(1)` is not. The categorical statement `isZero_of_isIso_biprod_fst` shows that
the quotient map `biprod.fst : M ⊞ M ⟶ M` is an isomorphism only if `M` is a zero object; the
rank of `M ⊞ M` is not computed.

Quasi-coherence of a biproduct is derived from the middle case of Stacks Tag 01IE,
`Stacks.AlgebraicGeometry.QuasicoherentExtension.isQuasicoherent_middle_of_shortExact`, which
carries `[IsAffine X]`. It is needed only for the module on the old base: the module on the new
base is a pullback, and pullbacks of quasi-coherent modules are quasi-coherent.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01IE](https://stacks.math.columbia.edu/tag/01IE)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

/-! ### Two ingredients: biproducts of quasi-coherent modules, and non-degeneracy -/

/-- A biproduct of quasi-coherent modules on an affine scheme is quasi-coherent. -/
instance SheafOfModules.isQuasicoherent_biprod_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⊞ N).IsQuasicoherent := by
  exact Stacks.AlgebraicGeometry.QuasicoherentExtension.isQuasicoherent_middle_of_shortExact _
    (ShortComplex.Splitting.ofHasBinaryBiproduct M N).shortExact

/-- If the first projection `A ⊞ A ⟶ A` is an isomorphism, then `A` is a zero object. -/
theorem isZero_of_isIso_biprod_fst {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] (A : C) (h : IsIso (biprod.fst : A ⊞ A ⟶ A)) : IsZero A := by
  have hinr : (biprod.inr : A ⟶ A ⊞ A) = 0 := (cancel_mono biprod.fst).mp (by simp)
  rw [Limits.IsZero.iff_id_eq_zero, ← biprod.inr_snd (X := A), hinr, Limits.zero_comp]

/-- The pullback of a module invertible in the sense of
`AlgebraicGeometry.SheafOfModules.IsInvertible` is invertible in the same sense. -/
theorem isInvertible_pullback_obj {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj M) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (@Stacks.Modules.isInvertible_pullback _ _ g M
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hM))

/-! ### The tautological datum of an invertible quotient -/

section OfQuotient

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] (L : X.Modules)
  (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
  (q : F ⟶ L) (hq : Epi q)

/-- The tautological datum attached to an epimorphism `q : F ⟶ L` onto an invertible module on
the base: its twist is `π^*L` and its universal surjection is `π^*q`. For `L = F` and `q = 𝟙`
this is `TautologicalDatum.ofInvertible`. -/
def TautologicalDatum.ofInvertibleQuotient : TautologicalDatum X F where
  twist := (Scheme.Modules.pullback (projectiveBundleToBase X F)).obj L
  invertible := isInvertible_pullback_obj (projectiveBundleToBase X F) L hL
  univ := (Scheme.Modules.pullback (projectiveBundleToBase X F)).map q
  epi_univ := by
    have := hq
    infer_instance

/-- The twist of `TautologicalDatum.ofInvertibleQuotient` is the pullback of `L` to the
projective bundle. -/
@[simp] theorem TautologicalDatum.ofInvertibleQuotient_twist :
    (TautologicalDatum.ofInvertibleQuotient X F L hL q hq).twist =
      (Scheme.Modules.pullback (projectiveBundleToBase X F)).obj L :=
  rfl

/-- The universal surjection of `TautologicalDatum.ofInvertibleQuotient` is the pullback of `q`
to the projective bundle. -/
@[simp] theorem TautologicalDatum.ofInvertibleQuotient_univ :
    (TautologicalDatum.ofInvertibleQuotient X F L hL q hq).univ =
      (Scheme.Modules.pullback (projectiveBundleToBase X F)).map q :=
  rfl

end OfQuotient

/-- At the identity of an invertible module, the universal surjection of `ofInvertibleQuotient`
is that of `ofInvertible`; the two twists are the same term. -/
theorem TautologicalDatum.ofInvertibleQuotient_id_univ (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent]
    (hF : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F) :
    (TautologicalDatum.ofInvertibleQuotient X F F hF (𝟙 F) inferInstance).univ =
      (TautologicalDatum.ofInvertible X F hF).univ :=
  CategoryTheory.Functor.map_id _ _

/-! ### The base-change identification at an arbitrary module -/

section BaseChange

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Y.Modules) [E.IsQuasicoherent]
  (E' : X.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- **The canonical identification `b^*π^*M ≅ π'^*M'`** for an arbitrary module `M` on the old
base together with an identification `M' ≅ g^*M`, `b` being the base-change comparison morphism
of the projective bundles of `E` and `E'`. It is the four-step chain of
`Stacks.RelativeProj.tautologicalBaseChangeIso`, which is the case `M = E`. -/
def pullbackModuleBaseChangeIso (M : Y.Modules) (M' : X.Modules)
    (hM : M' ≅ (Scheme.Modules.pullback g).obj M) :
    (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).obj
        ((Scheme.Modules.pullback (projectiveBundleToBase Y E)).obj M) ≅
      (Scheme.Modules.pullback (projectiveBundleToBase X E')).obj M' :=
  (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g E E' hE)
      (projectiveBundleToBase Y E)).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (projectiveBundleBaseChange_comp_projectiveBundleToBase g E E' hE)).app M ≪≫
    ((Scheme.Modules.pullbackComp (projectiveBundleToBase X E') g).app M).symm ≪≫
    (Scheme.Modules.pullback (projectiveBundleToBase X E')).mapIso hM.symm

/-- At the module that defines the comparison morphism, the identification above *is*
`Stacks.RelativeProj.tautologicalBaseChangeIso`. -/
theorem tautologicalBaseChangeIso_eq_pullbackModuleBaseChangeIso :
    tautologicalBaseChangeIso g E E' hE = pullbackModuleBaseChangeIso g E E' hE E E' hE :=
  rfl

/-- The identification `pullbackModuleBaseChangeIso` is natural in the module argument, for a
pair of morphisms `q`, `q'` satisfying the compatibility `q' ≫ hN.hom = hM.hom ≫ g^*q` with
the two identifications. -/
theorem pullbackModuleBaseChangeIso_naturality
    (M N : Y.Modules) (M' N' : X.Modules)
    (hM : M' ≅ (Scheme.Modules.pullback g).obj M)
    (hN : N' ≅ (Scheme.Modules.pullback g).obj N)
    (q : M ⟶ N) (q' : M' ⟶ N')
    (hq : q' ≫ hN.hom = hM.hom ≫ (Scheme.Modules.pullback g).map q) :
    (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map
          ((Scheme.Modules.pullback (projectiveBundleToBase Y E)).map q) ≫
        (pullbackModuleBaseChangeIso g E E' hE N N' hN).hom =
      (pullbackModuleBaseChangeIso g E E' hE M M' hM).hom ≫
        (Scheme.Modules.pullback (projectiveBundleToBase X E')).map q' := by
  have key : (Scheme.Modules.pullback g).map q ≫ hN.inv = hM.inv ≫ q' := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hq, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hfold : (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map
        ((Scheme.Modules.pullback (projectiveBundleToBase Y E)).map q) =
      (Scheme.Modules.pullback (projectiveBundleToBase Y E) ⋙
        Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map q := rfl
  have hunfold : (Scheme.Modules.pullback g ⋙
        Scheme.Modules.pullback (projectiveBundleToBase X E')).map q =
      (Scheme.Modules.pullback (projectiveBundleToBase X E')).map
        ((Scheme.Modules.pullback g).map q) := rfl
  simp only [pullbackModuleBaseChangeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [hfold, NatTrans.naturality_assoc, NatTrans.naturality_assoc, NatTrans.naturality_assoc,
    hunfold, ← Functor.map_comp, key, Functor.map_comp]

/-- The naturality square of `pullbackModuleBaseChangeIso_naturality`, with its left-hand
identification written as `Stacks.RelativeProj.tautologicalBaseChangeIso`. -/
theorem pullbackModuleBaseChangeIso_naturality_tautological
    (N : Y.Modules) (N' : X.Modules) (hN : N' ≅ (Scheme.Modules.pullback g).obj N)
    (q : E ⟶ N) (q' : E' ⟶ N')
    (hq : q' ≫ hN.hom = hE.hom ≫ (Scheme.Modules.pullback g).map q) :
    (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map
          ((Scheme.Modules.pullback (projectiveBundleToBase Y E)).map q) ≫
        (pullbackModuleBaseChangeIso g E E' hE N N' hN).hom =
      (tautologicalBaseChangeIso g E E' hE).hom ≫
        (Scheme.Modules.pullback (projectiveBundleToBase X E')).map q' :=
  pullbackModuleBaseChangeIso_naturality g E E' hE E N E' N' hE hN q q' hq

end BaseChange

/-! ### The base-change clause of Tag 0B3V for invertible quotients -/

section Clause

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Y.Modules) [E.IsQuasicoherent]
  (E' : X.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (L : Y.Modules)
  (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L)
  (L' : X.Modules)
  (hL' : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L')
  (hLL : L' ≅ (Scheme.Modules.pullback g).obj L)
  (q : E ⟶ L) (hq : Epi q) (q' : E' ⟶ L') (hq' : Epi q')
  (hcompat : q' ≫ hLL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map q)

include hcompat in
/-- The base change of the datum of an invertible quotient is the datum of the base-changed
invertible quotient: the canonical identification of twists carries the universal surjection of
the base change to the universal surjection of the datum on `𝐏(E')`. Its case `L = E`, `q = 𝟙`
is `Stacks.RelativeProj.TautologicalDatum.baseChange_ofInvertible_univ_comp_iso_hom`. -/
theorem TautologicalDatum.baseChange_ofInvertibleQuotient_univ_comp_iso_hom :
    ((TautologicalDatum.ofInvertibleQuotient Y E L hL q hq).baseChange g E E' hE).univ ≫
        (pullbackModuleBaseChangeIso g E E' hE L L' hLL).hom =
      (TautologicalDatum.ofInvertibleQuotient X E' L' hL' q' hq').univ :=
  Eq.trans
    (Category.assoc (tautologicalBaseChangeIso g E E' hE).inv
      ((Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map
        ((Scheme.Modules.pullback (projectiveBundleToBase Y E)).map q))
      (pullbackModuleBaseChangeIso g E E' hE L L' hLL).hom)
    (Eq.trans
      (congrArg (fun m => (tautologicalBaseChangeIso g E E' hE).inv ≫ m)
        (pullbackModuleBaseChangeIso_naturality_tautological g E E' hE L L' hLL q q' hcompat))
      (Iso.inv_hom_id_assoc (tautologicalBaseChangeIso g E E' hE)
        ((Scheme.Modules.pullback (projectiveBundleToBase X E')).map q')))

include hLL hcompat in
/-- The base-change comparison of Stacks Tag 0B3V on universal quotients, for the tautological
data attached to a compatible pair of invertible quotients, with no invertibility hypothesis on
the modules. The datum on `𝐏(E)` is the one attached to the invertible quotient `q` of `E`, the
datum on `𝐏(E')` the one attached to its base change `q'`, and the comparison of tautological
modules is the canonical identification `b^*π^*L ≅ π'^*L'`. -/
theorem projectiveBundleBaseChange_tautological_ofInvertibleQuotient :
    ∃ α : (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).obj
        (TautologicalDatum.ofInvertibleQuotient Y E L hL q hq).twist ≅
        (TautologicalDatum.ofInvertibleQuotient X E' L' hL' q' hq').twist,
      (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map
          (TautologicalDatum.ofInvertibleQuotient Y E L hL q hq).univ ≫ α.hom =
        (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g E E' hE)
            (projectiveBundleToBase Y E)).hom.app E ≫
          (Scheme.Modules.pullbackCongr
            (projectiveBundleBaseChange_comp_projectiveBundleToBase g E E' hE)).hom.app E ≫
          (Scheme.Modules.pullbackComp (projectiveBundleToBase X E') g).inv.app E ≫
          (Scheme.Modules.pullback (projectiveBundleToBase X E')).map hE.inv ≫
          (TautologicalDatum.ofInvertibleQuotient X E' L' hL' q' hq').univ :=
  projectiveBundleBaseChange_tautological_of_iso g E E' hE
    (TautologicalDatum.ofInvertibleQuotient Y E L hL q hq)
    (TautologicalDatum.ofInvertibleQuotient X E' L' hL' q' hq')
    (pullbackModuleBaseChangeIso g E E' hE L L' hLL)
    (TautologicalDatum.baseChange_ofInvertibleQuotient_univ_comp_iso_hom
      g E E' hE L hL L' hL' hLL q hq q' hq' hcompat)

end Clause

/-- The statement of `Stacks.RelativeProj.projectiveBundleBaseChange_tautological_ofInvertible`,
as the case `L = E`, `q = 𝟙`, `L' = E'`, `q' = 𝟙` of
`projectiveBundleBaseChange_tautological_ofInvertibleQuotient`. -/
alias projectiveBundleBaseChange_tautological_ofInvertible_of_quotient := projectiveBundleBaseChange_tautological_ofInvertible

/-! ### A biproduct of two copies of an invertible module -/

section RankTwo

variable {X Y : Scheme.{u}} [IsAffine Y] (g : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent]
  (hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M)

/-- The tautological datum on the projective bundle of `M ⊞ M`, for an invertible `M` over an
affine base, attached to the quotient map `biprod.fst : M ⊞ M ⟶ M`. -/
def tautologicalDatumBiprodSelf : TautologicalDatum Y (M ⊞ M) :=
  TautologicalDatum.ofInvertibleQuotient Y (M ⊞ M) M hM biprod.fst inferInstance

/-- The universal surjection of `tautologicalDatumBiprodSelf` is the pullback of `biprod.fst`
to the projective bundle of `M ⊞ M`. -/
@[simp] theorem tautologicalDatumBiprodSelf_univ :
    (tautologicalDatumBiprodSelf M hM).univ =
      (Scheme.Modules.pullback (projectiveBundleToBase Y (M ⊞ M))).map biprod.fst :=
  rfl

/-- The same datum on the base change of `M ⊞ M` along `g`, attached to the pulled-back
quotient map. -/
def tautologicalDatumBiprodSelfPullback :
    TautologicalDatum X ((Scheme.Modules.pullback g).obj (M ⊞ M)) :=
  TautologicalDatum.ofInvertibleQuotient X ((Scheme.Modules.pullback g).obj (M ⊞ M))
    ((Scheme.Modules.pullback g).obj M) (isInvertible_pullback_obj g M hM)
    ((Scheme.Modules.pullback g).map biprod.fst) inferInstance

/-- The universal surjection of `tautologicalDatumBiprodSelfPullback` is the pullback, to the
projective bundle of `g^*(M ⊞ M)`, of the pullback of `biprod.fst` along `g`. -/
@[simp] theorem tautologicalDatumBiprodSelfPullback_univ :
    (tautologicalDatumBiprodSelfPullback g M hM).univ =
      (Scheme.Modules.pullback (projectiveBundleToBase X
        ((Scheme.Modules.pullback g).obj (M ⊞ M)))).map
          ((Scheme.Modules.pullback g).map biprod.fst) :=
  rfl

/-- The base-change comparison of Stacks Tag 0B3V on universal quotients at `M ⊞ M`, for an
invertible `M` over an affine base and an arbitrary morphism of schemes into it: the module on
the new base is the pullback of `M ⊞ M`, and both tautological data are the ones attached to the
first projection and to its pullback. -/
theorem projectiveBundleBaseChange_tautological_biprodSelf :
    ∃ α : (Scheme.Modules.pullback (projectiveBundleBaseChange g (M ⊞ M)
          ((Scheme.Modules.pullback g).obj (M ⊞ M)) (Iso.refl _))).obj
        (tautologicalDatumBiprodSelf M hM).twist ≅
        (tautologicalDatumBiprodSelfPullback g M hM).twist,
      (Scheme.Modules.pullback (projectiveBundleBaseChange g (M ⊞ M)
            ((Scheme.Modules.pullback g).obj (M ⊞ M)) (Iso.refl _))).map
          (tautologicalDatumBiprodSelf M hM).univ ≫ α.hom =
        (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g (M ⊞ M)
              ((Scheme.Modules.pullback g).obj (M ⊞ M)) (Iso.refl _))
            (projectiveBundleToBase Y (M ⊞ M))).hom.app (M ⊞ M) ≫
          (Scheme.Modules.pullbackCongr
            (projectiveBundleBaseChange_comp_projectiveBundleToBase g (M ⊞ M)
              ((Scheme.Modules.pullback g).obj (M ⊞ M)) (Iso.refl _))).hom.app (M ⊞ M) ≫
          (Scheme.Modules.pullbackComp (projectiveBundleToBase X
              ((Scheme.Modules.pullback g).obj (M ⊞ M))) g).inv.app (M ⊞ M) ≫
          (Scheme.Modules.pullback (projectiveBundleToBase X
              ((Scheme.Modules.pullback g).obj (M ⊞ M)))).map (Iso.refl _).inv ≫
          (tautologicalDatumBiprodSelfPullback g M hM).univ :=
  projectiveBundleBaseChange_tautological_ofInvertibleQuotient g (M ⊞ M)
    ((Scheme.Modules.pullback g).obj (M ⊞ M)) (Iso.refl _) M hM
    ((Scheme.Modules.pullback g).obj M) (isInvertible_pullback_obj g M hM) (Iso.refl _)
    biprod.fst inferInstance ((Scheme.Modules.pullback g).map biprod.fst) inferInstance (by simp)

end RankTwo

end Stacks.RelativeProj

end
