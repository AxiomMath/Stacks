module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.AffineOpenSections
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapLocalOnSource
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BoundedComparison

/-!
# The top-degree base change map at the bounded below model of the direct image

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageBaseChangeMap` is the canonical map

> `γ : h^* R^d f'_* F' ⟶ R^d f''_* (h')^* F'`

of [Stacks, Tag 0EX3], whose ends are degree-`d` cohomology sheaves of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward`; conclusion (c) of that
tag asserts that `γ` is an isomorphism. This file identifies the cohomology sheaves of
`derivedPushforward` canonically with the higher direct images
`CategoryTheory.Functor.rightDerivedPlus`, and proves:

* `γ` corresponds to a map `γ⁺` between the higher direct images `h^* R^d f'_* F'` and
  `R^d f''_* (h')^* F'` taken in the bounded below model, and `γ` is invertible if and only if
  `γ⁺` is;
* both ends of `γ`, and of `γ⁺`, are quasi-coherent;
* `γ` is an isomorphism as soon as `γ` (or `γ⁺`) is bijective on the modules of sections over
  every affine open of `Y''` lying over an affine open of `Y'`.

## Main definitions

* `…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso`: the canonical isomorphism
  `Hⁱ(Rf_*(F[0])) ≅ Rⁱ f_* F` between the two models of the derived direct image at a morphism of
  schemes.
* `…TopDegreeBaseChange.topDirectImageBaseChangeMapPlus`: **`γ⁺`**, the canonical map `γ` read
  between `h^* R^d f'_* F'` and `R^d f''_* (h')^* F'` with the higher direct images taken in the
  bounded below model.

## Main results

* `…TopDegreeBaseChange.isQuasicoherent_source_topDirectImageBaseChangeMap` and
  `…TopDegreeBaseChange.isQuasicoherent_target_topDirectImageBaseChangeMap`: **both ends of `γ`
  are quasi-coherent.**
* `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMapPlus_iff`: **`γ⁺` is invertible if and
  only if `γ` is.**
* `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_bijective_app` and
  `…_of_bijective_app_of_isPullback`: `γ` is an isomorphism if it is bijective on the sections
  over the members of an affine open covering of `Y''`.
* `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMapPlus_of_bijective_app`: the same for
  `γ⁺`.
* `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_bijective_app_affineOpens` and
  `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens`:
  **`γ` is an isomorphism if `γ`, respectively `γ⁺`, is bijective on the sections over the affine
  opens of `Y''` lying over an affine open of `Y'`.**
* `…TopDegreeBaseChange.exists_isAffineOpen_cover_over`: for a morphism of schemes, a covering of
  the source by affine opens each lying over an affine open of the target.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open DerivedCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

section Schemes

variable {X Y : Scheme.{u}}

/-- **The canonical isomorphism `Hⁱ(Rf_*(F[0])) ≅ Rⁱ f_* F` at a morphism of schemes**: `Hⁱ` of
the component at `F[0]` of the isomorphism
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso` between the two
models of the derived direct image on bounded below objects. -/
def homologyFunctorDerivedPushforwardIso (f : X ⟶ Y) (F : X.Modules) (i : ℤ) :
    (homologyFunctor Y.Modules i).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor X.Modules 0).obj F)) ≅
      ((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F :=
  ((homologyFunctor Y.Modules i).mapIso
    ((boundedDerivedPushforwardIso f.toLRSHom.toShHom).app
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F))).symm

/-- **A covering by affine opens each lying over an affine open.** For a morphism of schemes
`k : Z ⟶ Z'`, there is an open cover of `Z` by affine opens, indexed by the points of `Z`, each
contained in the preimage of an affine open of `Z'`. -/
theorem exists_isAffineOpen_cover_over {Z Z' : Scheme.{u}} (k : Z ⟶ Z') :
    ∃ W : Z → Z.Opens, IsOpenCover W ∧ ∀ z : Z, IsAffineOpen (W z) ∧
      ∃ V : Z'.Opens, IsAffineOpen V ∧ (W z).1 ⊆ (k ⁻¹ᵁ V).1 := by
  choose V hV hkV _ using fun z : Z =>
    exists_isAffineOpen_mem_and_subset (x := k.base z) (U := ⊤) (by simp)
  choose W hW hzW hWV using fun z : Z =>
    exists_isAffineOpen_mem_and_subset (x := z) (U := k ⁻¹ᵁ V z) (hkV z)
  refine ⟨W, Opens.ext (Set.eq_univ_of_forall fun z => ?_), fun z => ⟨hW z, V z, hV z, hWV z⟩⟩
  simpa only [Opens.coe_iSup, Set.mem_iUnion] using ⟨z, hzW z⟩

end Schemes

variable {X'' Y'' : Scheme.{u}}

/-! ### Quasi-coherence of the two ends of the canonical map -/

/-- **The source of the canonical map `γ` of [Stacks, Tag 0EX3] is quasi-coherent**: the pullback
along `h` of the degree-`d` cohomology of `Rf'_*(F'[0])` is quasi-coherent. -/
theorem isQuasicoherent_source_topDirectImageBaseChangeMap
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent] (h : Y'' ⟶ S.Y') :
    ((Scheme.Modules.pullback h).obj
      ((homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
        ((derivedPushforward S.f'.toLRSHom.toShHom).obj
          ((singleFunctor S.X'.Modules 0).obj F')))).IsQuasicoherent := by
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  have := Stacks.AffineHigherDirectImage.isQuasicoherent_homologyFunctor_derivedPushforward
    S.f' F' (S.d : ℤ)
  exact AffineBaseChange.isQuasicoherent_pullback h _

/-- **The target of the canonical map `γ` of [Stacks, Tag 0EX3] is quasi-coherent**: for a
quasi-compact and quasi-separated `f''`, the degree-`d` cohomology of `Rf''_*((h')^* F'[0])` is
quasi-coherent. -/
theorem isQuasicoherent_target_topDirectImageBaseChangeMap
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'')
    (hqc : QuasiCompact f'') (hqs : QuasiSeparated f'') :
    ((homologyFunctor Y''.Modules (S.d : ℤ)).obj
      ((derivedPushforward f''.toLRSHom.toShHom).obj
        ((singleFunctor X''.Modules 0).obj
          ((Scheme.Modules.pullback h').obj F')))).IsQuasicoherent := by
  have := hqc
  have := hqs
  have := AffineBaseChange.isQuasicoherent_pullback h' F'
  exact Stacks.AffineHigherDirectImage.isQuasicoherent_homologyFunctor_derivedPushforward f'' _
    (S.d : ℤ)

/-- **The source of `γ⁺` is quasi-coherent**: the pullback along `h` of `R^d f'_* F'` is
quasi-coherent. -/
theorem isQuasicoherent_source_topDirectImageBaseChangeMapPlus
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent] (h : Y'' ⟶ S.Y') :
    ((Scheme.Modules.pullback h).obj
      (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj
        F')).IsQuasicoherent := by
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  exact AffineBaseChange.isQuasicoherent_pullback h _

/-- **The target of `γ⁺` is quasi-coherent**: for a quasi-compact and quasi-separated `f''`,
`R^d f''_* ((h')^* F')` is quasi-coherent. -/
theorem isQuasicoherent_target_topDirectImageBaseChangeMapPlus
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'')
    (hqc : QuasiCompact f'') (hqs : QuasiSeparated f'') :
    (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
      ((Scheme.Modules.pullback h').obj F')).IsQuasicoherent := by
  have := hqc
  have := hqs
  have := AffineBaseChange.isQuasicoherent_pullback h' F'
  infer_instance

/-! ### Conclusion (c) reduced to modules of sections -/

/-- A statement `Q` follows from a property `P` of opens, known for the affine opens lying over
affine opens, once it follows from `P` on the members of an affine open cover. -/
private theorem of_forall_isAffineOpen_cover_over {Z Z' : Scheme.{u}} (k : Z ⟶ Z')
    {P : Z.Opens → Prop} {Q : Prop}
    (hP : ∀ V : Z'.Opens, IsAffineOpen V → ∀ W : Z.Opens, IsAffineOpen W →
      W.1 ⊆ (k ⁻¹ᵁ V).1 → P W)
    (hQ : ∀ W : Z → Z.Opens, IsOpenCover W → (∀ z, IsAffineOpen (W z)) → (∀ z, P (W z)) → Q) :
    Q := by
  obtain ⟨W, hcover, hWdata⟩ := exists_isAffineOpen_cover_over k
  refine hQ W hcover (fun z => (hWdata z).1) fun z => ?_
  obtain ⟨V, hV, hle⟩ := (hWdata z).2
  exact hP V hV (W z) (hWdata z).1 hle

/-- **Conclusion (c) of [Stacks, Tag 0EX3] from bijectivity on sections over an affine open
covering of `Y''`.** If `γ` is bijective on the module of sections over each member of a covering
of `Y''` by affine opens, then `γ` is an isomorphism. -/
theorem isIso_topDirectImageBaseChangeMap_of_bijective_app
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)
    (hqc : QuasiCompact f'') (hqs : QuasiSeparated f'')
    {I : Type*} (W : I → Y''.Opens) (hcover : IsOpenCover W)
    (hW : ∀ i, IsAffineOpen (W i))
    (hbij : ∀ i, Function.Bijective
      ((topDirectImageBaseChangeMap S F' h' f'' h sq).val.app (op (W i)))) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h sq) := by
  have := isQuasicoherent_source_topDirectImageBaseChangeMap S F' h
  have := isQuasicoherent_target_topDirectImageBaseChangeMap S F' h' f'' hqc hqs
  exact AffineBaseChange.isIso_of_bijective_app_of_isOpenCover _ W hcover hW hbij

/-- **Conclusion (c) of [Stacks, Tag 0EX3] from bijectivity on sections over an affine open
covering of `Y''`, for a cartesian square.** If the square formed by `h'`, `f''`, `f'` and `h` is
cartesian and `γ` is bijective on the module of sections over each member of a covering of `Y''`
by affine opens, then `γ` is an isomorphism. -/
theorem isIso_topDirectImageBaseChangeMap_of_bijective_app_of_isPullback
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : IsPullback h' f'' S.f' h)
    {I : Type*} (W : I → Y''.Opens) (hcover : IsOpenCover W)
    (hW : ∀ i, IsAffineOpen (W i))
    (hbij : ∀ i, Function.Bijective
      ((topDirectImageBaseChangeMap S F' h' f'' h
        (toShHom_comm_of_isPullback h' f'' h sq)).val.app (op (W i)))) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h
      (toShHom_comm_of_isPullback h' f'' h sq)) :=
  isIso_topDirectImageBaseChangeMap_of_bijective_app S F' h' f'' h _
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) sq
      S.quasiCompact_f')
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated) sq
      S.quasiSeparated_f')
    W hcover hW hbij

/-- **Conclusion (c) of [Stacks, Tag 0EX3] from bijectivity on the sections over the affine opens
of `Y''` lying over an affine open of `Y'`.** If `γ` is bijective on the module of sections over
every affine open `W` of `Y''` contained in `h ⁻¹ V` for an affine open `V` of `Y'`, then `γ` is
an isomorphism. -/
theorem isIso_topDirectImageBaseChangeMap_of_bijective_app_affineOpens
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)
    (hqc : QuasiCompact f'') (hqs : QuasiSeparated f'')
    (hbij : ∀ V : S.Y'.Opens, IsAffineOpen V → ∀ W : Y''.Opens, IsAffineOpen W →
      W.1 ⊆ (h ⁻¹ᵁ V).1 →
      Function.Bijective
        ((topDirectImageBaseChangeMap S F' h' f'' h sq).val.app (op W))) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h sq) := by
  exact of_forall_isAffineOpen_cover_over h hbij
    (isIso_topDirectImageBaseChangeMap_of_bijective_app S F' h' f'' h sq hqc hqs)

/-! ### The canonical map at the spelling of conclusions (a) and (b) -/

/-- **The canonical map `γ` of [Stacks, Tag 0EX3], read between the higher direct images that the
tag's other conclusions are about.** Conjugating `γ` by the two crossings
`homologyFunctorDerivedPushforwardIso` gives a morphism

> `γ⁺ : h^* R^d f'_* F' ⟶ R^d f''_* (h')^* F'`

whose source and target are built from `CategoryTheory.Functor.rightDerivedPlus`. -/
def topDirectImageBaseChangeMapPlus
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom) :
    (Scheme.Modules.pullback h).obj
        (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F') ⟶
      ((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F') :=
  ((Scheme.Modules.pullback h).mapIso
        (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ))).inv ≫
    topDirectImageBaseChangeMap S F' h' f'' h sq ≫
    (homologyFunctorDerivedPushforwardIso f''
      ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom

/-- `γ⁺` with its three factors named: the two crossings of the models of `Rf_*` and `γ`. -/
theorem topDirectImageBaseChangeMapPlus_eq
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom) :
    topDirectImageBaseChangeMapPlus S F' h' f'' h sq =
      ((Scheme.Modules.pullback h).mapIso
            (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ))).inv ≫
        topDirectImageBaseChangeMap S F' h' f'' h sq ≫
        (homologyFunctorDerivedPushforwardIso f''
          ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  rfl

/-- **`γ⁺` is invertible if and only if `γ` is.** -/
theorem isIso_topDirectImageBaseChangeMapPlus_iff
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom) :
    IsIso (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) ↔
      IsIso (topDirectImageBaseChangeMap S F' h' f'' h sq) := by
  have hx : IsIso ((Scheme.Modules.pullback h).mapIso
      (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ))).inv := inferInstance
  have hy : IsIso (homologyFunctorDerivedPushforwardIso f''
      ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom := inferInstance
  exact ⟨fun hp => @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hy
      (@IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hx hp),
    fun hg => @IsIso.comp_isIso _ _ _ _ _ _ _ hx (@IsIso.comp_isIso _ _ _ _ _ _ _ hg hy)⟩

/-- **Invertibility of `γ⁺` from bijectivity on sections over an affine open covering of `Y''`.**
If `γ⁺` is bijective on the module of sections over each member of a covering of `Y''` by affine
opens, then `γ⁺` is an isomorphism. -/
theorem isIso_topDirectImageBaseChangeMapPlus_of_bijective_app
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)
    (hqc : QuasiCompact f'') (hqs : QuasiSeparated f'')
    {I : Type*} (W : I → Y''.Opens) (hcover : IsOpenCover W)
    (hW : ∀ i, IsAffineOpen (W i))
    (hbij : ∀ i, Function.Bijective
      ((topDirectImageBaseChangeMapPlus S F' h' f'' h sq).val.app (op (W i)))) :
    IsIso (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) := by
  have := isQuasicoherent_source_topDirectImageBaseChangeMapPlus S F' h
  have := isQuasicoherent_target_topDirectImageBaseChangeMapPlus S F' h' f'' hqc hqs
  exact AffineBaseChange.isIso_of_bijective_app_of_isOpenCover _ W hcover hW hbij

/-- **Conclusion (c) of [Stacks, Tag 0EX3] from bijectivity of `γ⁺` on the sections over the
affine opens of `Y''` lying over an affine open of `Y'`.** If `γ⁺` is bijective on the module of
sections over every affine open `W` of `Y''` contained in `h ⁻¹ V` for an affine open `V` of
`Y'`, then `γ` is an isomorphism. -/
theorem isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)
    (hqc : QuasiCompact f'') (hqs : QuasiSeparated f'')
    (hbij : ∀ V : S.Y'.Opens, IsAffineOpen V → ∀ W : Y''.Opens, IsAffineOpen W →
      W.1 ⊆ (h ⁻¹ᵁ V).1 →
      Function.Bijective
        ((topDirectImageBaseChangeMapPlus S F' h' f'' h sq).val.app (op W))) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h sq) := by
  refine (isIso_topDirectImageBaseChangeMapPlus_iff S F' h' f'' h sq).1 ?_
  exact of_forall_isAffineOpen_cover_over h hbij
    (isIso_topDirectImageBaseChangeMapPlus_of_bijective_app S F' h' f'' h sq hqc hqs)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
