module

public import StacksFrontier.CategoryTheory.Sites.Modules.StructureSheafLocalization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Support.LocalizationFlat
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.HomAfterLocalization

/-!
# Inverting one global section of the structure sheaf of a ringed site

Let `(C, 𝒪)` be a ringed site and let `f` be a global section of `𝒪`. The sheaf `𝒪_f` is the
sheaf of rings associated to the presheaf `U ↦ 𝒪(U)[1/f|_U]`: it inverts `f` and nothing else,
and the canonical map `𝒪 ⟶ 𝒪_f` is both an epimorphism and flat.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayMultiplicativeSubpresheaf`: the powers of a global section,
  as a restriction-stable family of multiplicative subsets of the structure sheaf.
* `AlgebraicGeometry.RingedSite.awayPresheaf` and
  `AlgebraicGeometry.RingedSite.awaySheaf`: the presheaf `U ↦ 𝒪(U)[1/f|_U]` and the sheaf `𝒪_f`
  associated to it, with `AlgebraicGeometry.RingedSite.toAwaySheaf` the canonical map `𝒪 ⟶ 𝒪_f`.

## Main results

* `AlgebraicGeometry.RingedSite.isLocalizationAway_awayPresheaf`: each ring of sections of
  `awayPresheaf` is the localization of `𝒪(U)` away from `f|_U`.
* `AlgebraicGeometry.RingedSite.isUnit_toAwaySheaf` and
  `AlgebraicGeometry.RingedSite.existsUnique_lift_toAwaySheaf`: `f` becomes invertible in `𝒪_f`,
  universally.
* `AlgebraicGeometry.RingedSite.epi_toAwaySheaf` and
  `AlgebraicGeometry.RingedSite.isFlatMap_toAwaySheaf`: the canonical map is an epimorphism of
  sheaves of rings and is flat.
* `AlgebraicGeometry.RingedSite.derivedSheafHom_awayRestrictScalarsIso`: derived internal Hom
  of complexes of `𝒪_f`-modules may be computed over `𝒪`.
* `AlgebraicGeometry.RingedSite.derivedSheafHom_awayRestrictScalarsIso_canonical`: that
  comparison is induced by the complex-level map leaving every local Hom unchanged.
* `AlgebraicGeometry.RingedSite.sheafHomComplex_awayLocalizedAction_agree`: the two
  `𝒪_f`-structures on the internal Hom agree.

## Implementation notes

`awayMultiplicativeSubpresheaf` is the `MultiplicativeSubpresheaf` of [Stacks, Tag 0EMC]
specialised to `Submonoid.powers (f|_U)`, so `𝒪_f` and the map `𝒪 ⟶ 𝒪_f` are its sheafification
and canonical map. The statements up to flatness hold for an arbitrary ringed site; the
derived-Hom statements are stated at `RingedSite.{u, u, u}`.

## References

* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.RingedSite

section Away

variable {X : RingedSite.{u, v, w}}

/-- The value over an object `U` of a global section of the structure sheaf. -/
abbrev globalSectionVal (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}))
    (U : X.Cᵒᵖ) : X.O.obj.obj U :=
  (Presheaf.globalSectionsEquivSections _ h).val U

/-- Restriction carries the value of a global section to its value. -/
theorem globalSectionVal_map
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w})) {U V : X.Cᵒᵖ} (g : U ⟶ V) :
    (X.O.obj.map g).hom (globalSectionVal h U) = globalSectionVal h V :=
  (Presheaf.globalSectionsEquivSections _ h).property g

/-- The powers of a global section of the structure sheaf, as a restriction-stable family of
multiplicative subsets. -/
def awayMultiplicativeSubpresheaf
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w})) :
    MultiplicativeSubpresheaf X where
  obj U := Submonoid.powers (globalSectionVal h U)
  map {U V} g := by
    rintro x ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    change globalSectionVal h V ^ n = (X.O.obj.map g).hom (globalSectionVal h U ^ n)
    rw [map_pow, globalSectionVal_map h g]

/-- The presheaf `U ↦ 𝒪(U)[1/f|_U]` of sectionwise localizations away from a global section. -/
abbrev awayPresheaf (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w})) :
    X.Cᵒᵖ ⥤ CommRingCat.{w} :=
  (awayMultiplicativeSubpresheaf h).localizationPresheaf

/-- The canonical map from the structure sheaf into the presheaf of sectionwise localizations. -/
abbrev toAwayPresheaf (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w})) :
    X.O.obj ⟶ awayPresheaf h :=
  (awayMultiplicativeSubpresheaf h).toLocalizationPresheaf

/-- Each ring of sections of `awayPresheaf` is the localization of the sections of the structure
sheaf away from the value there of the global section, for the `Algebra` structure induced by
the canonical map. -/
theorem isLocalizationAway_awayPresheaf
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w})) (U : X.Cᵒᵖ) :
    @IsLocalization.Away (X.O.obj.obj U) _ (globalSectionVal h U) (awayPresheaf h |>.obj U) _
      (((toAwayPresheaf h).app U).hom.toAlgebra) := by
  have heq : (((toAwayPresheaf h).app U).hom.toAlgebra) =
      (inferInstance : Algebra (X.O.obj.obj U) ((awayPresheaf h).obj U)) :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  rw [heq]
  exact inferInstanceAs
    (IsLocalization ((awayMultiplicativeSubpresheaf h).obj U) ((awayPresheaf h).obj U))

variable [HasWeakSheafify X.J CommRingCat.{w}]

/-- The sheaf `𝒪_f` of rings obtained by inverting a global section `f` of the structure
sheaf. -/
abbrev awaySheaf (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w})) :
    Sheaf X.J CommRingCat.{w} :=
  (presheafToSheaf X.J CommRingCat.{w}).obj (awayPresheaf h)

/-- The canonical map `𝒪 ⟶ 𝒪_f`. -/
abbrev toAwaySheaf (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w})) :
    X.O ⟶ awaySheaf h :=
  (awayMultiplicativeSubpresheaf h).toLocalizationSheaf

/-- The canonical map `𝒪 ⟶ 𝒪_f` factors as the sectionwise localization followed by
sheafification. -/
theorem toAwaySheaf_hom (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w})) :
    (toAwaySheaf h).hom = toAwayPresheaf h ≫ toSheafify X.J (awayPresheaf h) := by
  show toSheafify X.J X.O.obj ≫ sheafifyMap X.J (toAwayPresheaf h) = _
  exact (toSheafify_naturality _ _).symm

/-- Every power of a global section becomes invertible in `𝒪_f`. -/
theorem isUnit_toAwaySheaf (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}))
    (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (((toAwaySheaf h).hom.app U).hom (globalSectionVal h U ^ n)) :=
  (awayMultiplicativeSubpresheaf h).isUnit_toLocalizationSheaf U ⟨_, n, rfl⟩

/-- The universal property of `𝒪_f`: a map of sheaves of rings out of `𝒪` inverting every power
of the global section factors uniquely through `𝒪_f`. -/
theorem existsUnique_lift_toAwaySheaf
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}))
    (A : Sheaf X.J CommRingCat.{w}) (g : X.O ⟶ A)
    (hg : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit ((g.hom.app U).hom (globalSectionVal h U ^ n))) :
    ∃! φ : awaySheaf h ⟶ A, toAwaySheaf h ≫ φ = g :=
  (awayMultiplicativeSubpresheaf h).existsUnique_lift_toLocalizationSheaf A g
    fun U ⟨_, n, hn⟩ ↦ hn ▸ hg U n

variable [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective CommRingCat.{w}]

/-- Inverting a global section of the structure sheaf is an epimorphism of sheaves of rings. -/
theorem epi_toAwaySheaf (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w})) :
    Epi (toAwaySheaf h) :=
  SheafOfModules.localizationMap_epi X.O h (awayPresheaf h) (toAwayPresheaf h)
    (isLocalizationAway_awayPresheaf h) (awaySheaf h) (toSheafify X.J (awayPresheaf h))
    (toAwaySheaf h) (toAwaySheaf_hom h)

/-- Inverting a global section of the structure sheaf is flat. -/
theorem isFlatMap_toAwaySheaf (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w})) :
    SheafOfModules.IsFlatMap (toAwaySheaf h) :=
  SheafOfModules.localizationMap_isFlat X.O h (awayPresheaf h) (toAwayPresheaf h)
    (isLocalizationAway_awayPresheaf h) (awaySheaf h) (toSheafify X.J (awayPresheaf h))
    (toAwaySheaf h) (toAwaySheaf_hom h)

end Away

section DerivedHom

attribute [local instance] HasDerivedCategory.standard

open Opposite

/-- Let `(𝒞, 𝒪)` be a ringed site and let `f` be a global section of `𝒪`. For
`L, N ∈ D(𝒪_f)` we have `R SheafHom_𝒪(L, N) = R SheafHom_{𝒪_f}(L, N)`: computing `N` by a
K-injective complex `I` of sheaves of `𝒪_f`-modules, the internal Hom complex over `𝒪` of the
restrictions of `L` and `I` is, as a complex of sheaves of `𝒪`-modules, the restriction of the
internal Hom complex over `𝒪_f` of `L` and `I`. -/
@[stacks 0996 "part (1)"]
def derivedSheafHom_awayRestrictScalarsIso (X : RingedSite.{u, u, u})
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (L I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj (awaySheaf h))) ℤ)
    [I.IsKInjective] :
    let Xh : RingedSite.{u, u, u} := { C := X.C, J := X.J, O := awaySheaf h }
    let R := SheafOfModules.restrictScalars.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).map (toAwaySheaf h))
    let LR := (R.mapHomologicalComplex (.up ℤ)).obj L
    let IR := (R.mapHomologicalComplex (.up ℤ)).obj I
    DerivedCategory.Q.obj (sheafHomComplex X LR IR).obj ≅
      DerivedCategory.Q.obj
        ((R.mapHomologicalComplex (.up ℤ)).obj (sheafHomComplex Xh L I).obj) :=
  have : Epi (toAwaySheaf h) := epi_toAwaySheaf h
  derivedSheafHom_restrictScalarsIso X (awaySheaf h) (toAwaySheaf h)
    (isFlatMap_toAwaySheaf h) L I

/-- The comparison `derivedSheafHom_awayRestrictScalarsIso` is induced by the isomorphism of
internal Hom complexes that leaves every local module homomorphism unchanged. -/
@[stacks 0996 "part (1)"]
theorem derivedSheafHom_awayRestrictScalarsIso_canonical (X : RingedSite.{u, u, u})
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (L I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj (awaySheaf h))) ℤ)
    [I.IsKInjective] :
    let Xh : RingedSite.{u, u, u} := { C := X.C, J := X.J, O := awaySheaf h }
    let R := SheafOfModules.restrictScalars.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).map (toAwaySheaf h))
    let LR := (R.mapHomologicalComplex (.up ℤ)).obj L
    let IR := (R.mapHomologicalComplex (.up ℤ)).obj I
    ∃ c : (sheafHomComplex X LR IR).obj ≅
        (R.mapHomologicalComplex (.up ℤ)).obj (sheafHomComplex Xh L I).obj,
      (DerivedCategory.Q.mapIso c = derivedSheafHom_awayRestrictScalarsIso X h L I) ∧
      (∀ (U : X.C) (n p q : ℤ) (hpq : p + n = q)
          (s : ((sheafHomComplex X LR IR).obj.X n).val.obj (op U))
          {W : X.C} (g : W ⟶ U) (x : (L.X p).val.obj (op W)),
        (((AddCommGrpCat.Hom.hom
            (((sheafHomComplex Xh L I).sectionsIso U).hom.f n)
            ((c.hom.f n).val.app (op U) s)).v p q hpq).val.app
              (op (Over.mk g))) x =
          (((AddCommGrpCat.Hom.hom
            (((sheafHomComplex X LR IR).sectionsIso U).hom.f n) s).v p q hpq).val.app
              (op (Over.mk g))) x) :=
  have : Epi (toAwaySheaf h) := epi_toAwaySheaf h
  derivedSheafHom_restrictScalarsIso_canonical X (awaySheaf h) (toAwaySheaf h)
    (isFlatMap_toAwaySheaf h) L I

/-- The two `𝒪_f`-structures on `R SheafHom_𝒪(L, N)` agree: acting by a local section of `𝒪_f`
on the source of a local Hom and acting by it on the target give the same section of the
internal Hom complex. -/
@[stacks 0996 "part (1)"]
theorem sheafHomComplex_awayLocalizedAction_agree (X : RingedSite.{u, u, u})
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (L I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj (awaySheaf h))) ℤ) :
    let _Xh : RingedSite.{u, u, u} := { C := X.C, J := X.J, O := awaySheaf h }
    let R := SheafOfModules.restrictScalars.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).map (toAwaySheaf h))
    let LR := (R.mapHomologicalComplex (.up ℤ)).obj L
    let IR := (R.mapHomologicalComplex (.up ℤ)).obj I
    ∀ (U : X.C)
      (r : ((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj
        (awaySheaf h)).obj.obj (op U))
      (n p q : ℤ) (hpq : p + n = q)
      (s : ((sheafHomComplex X LR IR).obj.X n).val.obj (op U))
      {W : X.C} (g : W ⟶ U) (x : (L.X p).val.obj (op W)),
      (((AddCommGrpCat.Hom.hom
        (((sheafHomComplex X LR IR).sectionsIso U).hom.f n) s).v p q hpq).val.app
          (op (Over.mk g)))
            (((L.X p).val.obj (op W)).isModule.smul
              (((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj
                (awaySheaf h)).obj.map g.op r) x) =
        ((I.X q).val.obj (op W)).isModule.smul
          (((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj
            (awaySheaf h)).obj.map g.op r)
          (show (I.X q).val.obj (op W) from (((AddCommGrpCat.Hom.hom
            (((sheafHomComplex X LR IR).sectionsIso U).hom.f n) s).v p q hpq).val.app
              (op (Over.mk g))) x) :=
  have : Epi (toAwaySheaf h) := epi_toAwaySheaf h
  sheafHomComplex_localizedAction_agree X (awaySheaf h) (toAwaySheaf h) L I

end DerivedHom

end AlgebraicGeometry.RingedSite

end
