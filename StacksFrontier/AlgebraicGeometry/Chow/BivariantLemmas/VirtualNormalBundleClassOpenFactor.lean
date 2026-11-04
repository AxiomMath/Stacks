module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleOpenFactor
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Conormal.OpenFactorization
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalBundleClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.Completion

/-!
# The virtual normal Gysin class along an open factorization

Let `i : Z ⟶ X` be a closed immersion factoring as `i = i' ≫ ι_U` through an open subscheme
`U ⊆ X`, and let `𝒩` be a virtual normal bundle for `i`, read as one for `i'`
(`Stacks.Chow.VirtualNormalBundle.toOpenFactor`). The square `i' ≫ ι_U = 𝟙 ≫ i` is cartesian, so
the base-change clause of Stacks 0FBK applies to it; this file identifies the base change `𝟙^*𝒩`
with `𝒩` read along `i'`, compatibly with the surjections onto the conormal sheaf, and deduces
that the restriction of `c(Z ⟶ X, 𝒩)` to `U` is `c(Z ⟶ U, 𝒩)`.

The identification rests on the conormal map of the square `i' ≫ ι_U = 𝟙 ≫ i`: it is the
identification `𝟙^* ≅ 𝟭` followed by `𝒞_{Z/X} ≅ 𝒞_{Z/U}`
(`Stacks.Chow.immersionConormalSheafMap_id_ι`), which on ringed spaces comes from the coherence
of the pullback pseudofunctor with identities and the characterization of both ideal-sheaf maps
by the inclusions into the structure sheaf.

The same argument applies to an immersion `i` factoring as closed immersions `iU : Z ⟶ U` and
`iV : Z ⟶ V` through opens `V ⊆ U` of `X`: the square `iV ≫ (V ⊆ U) = 𝟙 ≫ iU` is cartesian, its
conormal map is `𝟙^* ≅ 𝟭` followed by `𝒞_{Z/U} ≅ 𝒞_{Z/X} ≅ 𝒞_{Z/V}` (by the composition law of
Stacks 01R4 for `(V ⊆ U) ≫ ι_U = ι_V`), and so the restriction of `c(Z ⟶ U, 𝒩)` to `V` is
`c(Z ⟶ V, 𝒩)`.

## Main results

* `Stacks.Chow.bivariantTransport_bivariantRestriction_virtualNormalGysinClass_toOpenFactor` —
  the base-change clause of Stacks 0FBK along an open subscheme containing `Z`, at constant rank.
* `Stacks.Chow.bivariantTransport_bivariantRestriction_virtualNormalGysinClass_homOfLE` — the
  same along an inclusion of opens `V ⊆ U` containing `Z`, for an immersion `Z ⟶ X`.
* `Stacks.Chow.immersionConormalSheafMap_id_ι`, `Stacks.Chow.conormalSheafMap_ofRestrict` — the
  conormal map of the square `i' ≫ ι_U = 𝟙 ≫ i`.
* `Stacks.Chow.immersionConormalSheafMap_id_homOfLE` — the conormal map of the square
  `iV ≫ (V ⊆ U) = 𝟙 ≫ iU`.

## Implementation notes

The restriction of a class over `U` to `V ⊆ U` is a class for the structure morphism
`(V ⊆ U) ≫ ι_U ≫ s_X` of `V`, which equals `ι_V ≫ s_X` without being the same term, so the
comparison along `V ⊆ U` is stated with `HEq`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

section Coherence

variable {Z X : RingedSpace.{u, u}}

/-- `(𝟙 ≫ j)^* ≅ j^* ⋙ 𝟙^*` is, read backwards, the identification `𝟙^* ≅ 𝟭`. -/
theorem modulePullbackComp_id_inv_app (j : Z ⟶ X) (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackComp (𝟙 Z) j).inv.app M =
      (modulePullbackId Z).hom.app ((modulePullback j).obj M) := by
  have := NatTrans.congr_app (congrArg Iso.hom (SheafOfModules.pullback_comp_id.{u}
    (structureSheafHom j))) M
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at this
  exact this

/-- `(j ≫ 𝟙)^* ≅ 𝟙^* ⋙ j^*` is `j^*` applied to the identification `𝟙^* ≅ 𝟭`, read backwards. -/
theorem modulePullbackComp_comp_id_hom_app (j : Z ⟶ X)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackComp j (𝟙 X)).hom.app M =
      (modulePullback j).map ((modulePullbackId X).inv.app M) := by
  have := NatTrans.congr_app (congrArg Iso.inv (SheafOfModules.pullback_id_comp.{u}
    (structureSheafHom j))) M
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Category.id_comp] at this
  exact this

/-- The transport `(𝟙 ≫ j)^* ≅ j^*` along `𝟙 ≫ j = j` is the identity. -/
theorem modulePullbackCongr_id_comp_hom_app (j : Z ⟶ X)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackCongr (Category.id_comp j)).hom.app M = 𝟙 _ := by
  simp [modulePullbackCongr]
  rfl

variable (U : TopologicalSpace.Opens X.carrier) (g : Z ⟶ X.restrict U.isOpenEmbedding)

/-- The ideal-sheaf map of the square `g ≫ ι_U = 𝟙 ≫ (g ≫ ι_U)` is the identification
`ι_U^* ℐ_{g ≫ ι_U} ≅ ℐ_g`. -/
theorem idealSheafMap_ofRestrict
    (comm : g ≫ X.ofRestrict U.isOpenEmbedding = 𝟙 Z ≫ (g ≫ X.ofRestrict U.isOpenEmbedding)) :
    Stacks.ClosedImmersion.idealSheafMap comm =
      (Stacks.ClosedImmersion.idealSheafOfRestrictIso U g).hom := by
  have := Stacks.ClosedImmersion.mono_idealSheafι g
  refine (cancel_mono (Stacks.ClosedImmersion.idealSheafι g)).1 ?_
  rw [Stacks.ClosedImmersion.idealSheafMap_comp_ι,
    Stacks.ClosedImmersion.idealSheafOfRestrictIso_hom_comp_ι]

/-- **The conormal-sheaf map of the square `g ≫ ι_U = 𝟙 ≫ (g ≫ ι_U)`** is the identification
`𝟙^* ≅ 𝟭` followed by `𝒞_{g ≫ ι_U} ≅ 𝒞_g`. -/
theorem conormalSheafMap_ofRestrict
    (comm : g ≫ X.ofRestrict U.isOpenEmbedding = 𝟙 Z ≫ (g ≫ X.ofRestrict U.isOpenEmbedding)) :
    Stacks.ClosedImmersion.conormalSheafMap comm =
      (modulePullbackId Z).hom.app
          (Stacks.ClosedImmersion.conormalSheaf (g ≫ X.ofRestrict U.isOpenEmbedding)) ≫
        (Stacks.ClosedImmersion.conormalSheafOfRestrictIso U g).hom := by
  rw [Stacks.ClosedImmersion.conormalSheafMap, idealSheafMap_ofRestrict,
    Stacks.ClosedImmersion.pullbackCompIso, Stacks.ClosedImmersion.conormalSheafOfRestrictIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Category.assoc]
  rw [modulePullbackComp_id_inv_app, modulePullbackCongr_id_comp_hom_app]
  exact congrArg (_ ≫ ·) (Category.id_comp _)

end Coherence

section SchemeCoherence

variable {Z X : Scheme.{u}}

/-- **The conormal map of the square `i' ≫ ι_U = 𝟙 ≫ i`**, for an immersion `i` factoring as
`i = i' ≫ ι_U` through an open subscheme `U`, is the identification `𝟙^* ≅ 𝟭` followed by
`𝒞_{Z/X} ≅ 𝒞_{Z/U}`. -/
theorem immersionConormalSheafMap_id_ι {i : Z ⟶ X} [IsImmersion i] (U : X.Opens)
    (i' : Z ⟶ U.toScheme) [IsImmersion i'] (hU : i' ≫ U.ι = i) :
    Stacks.Immersion.immersionConormalSheafMap i' i (𝟙 Z) U.ι
        (Stacks.Immersion.toShHom_square (hU.trans (Category.id_comp i).symm)) =
      (modulePullbackId Z.toRingedSpace).hom.app (Stacks.Thickenings.immersionConormalSheaf i) ≫
        (immersionConormalSheafFactorIso U i' hU).hom := by
  subst hU
  have h := conormalSheafMap_ofRestrict (Z := Z.toRingedSpace) (X := X.toRingedSpace) U
    i'.toLRSHom.toShHom (Stacks.Immersion.toShHom_square (Category.id_comp (i' ≫ U.ι)).symm)
  have hn := (modulePullbackId Z.toRingedSpace).hom.naturality
    (Stacks.Immersion.conormalSheafSelfIso (i' ≫ U.ι)).inv
  unfold Stacks.Immersion.immersionConormalSheafMap immersionConormalSheafFactorIso
  refine (congrArg (_ ≫ · ≫ (Stacks.Immersion.conormalSheafSelfIso i').hom) h).trans ?_
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hn))).trans ?_)
  simp only
  rfl

/-- The conormal map of a square only depends on the two horizontal edges up to equality. -/
private theorem immersionConormalSheafMap_heq_of_eq {Z₁ Z₂ X₁ X₂ : Scheme.{u}} (i : Z₁ ⟶ X₁)
    (j : Z₂ ⟶ X₂) [IsImmersion i] [IsImmersion j] {f f' : Z₁ ⟶ Z₂} {g g' : X₁ ⟶ X₂}
    (hf : f = f') (hg : g = g') (c c') :
    Stacks.Immersion.immersionConormalSheafMap i j f g c ≍
      Stacks.Immersion.immersionConormalSheafMap i j f' g' c' := by
  subst hf hg
  rfl

/-- **The conormal map of the square `iV ≫ (V ⊆ U) = 𝟙 ≫ iU`**, for an immersion `i` factoring
as `i = iU ≫ ι_U = iV ≫ ι_V` through opens `V ⊆ U`, is the identification `𝟙^* ≅ 𝟭` followed by
`𝒞_{Z/U} ≅ 𝒞_{Z/X} ≅ 𝒞_{Z/V}`. -/
theorem immersionConormalSheafMap_id_homOfLE {i : Z ⟶ X} [IsImmersion i] {U V : X.Opens}
    (hVU : V ≤ U) (iU : Z ⟶ U.toScheme) [IsImmersion iU] (iV : Z ⟶ V.toScheme) [IsImmersion iV]
    (hU : iU ≫ U.ι = i) (hV : iV ≫ V.ι = i)
    (comm : iV.toLRSHom.toShHom ≫ (X.homOfLE hVU).toLRSHom.toShHom =
      (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom ≫ iU.toLRSHom.toShHom) :
    Stacks.Immersion.immersionConormalSheafMap iV iU (𝟙 Z) (X.homOfLE hVU) comm =
      (modulePullbackId Z.toRingedSpace).hom.app (Stacks.Thickenings.immersionConormalSheaf iU) ≫
        (immersionConormalSheafFactorIso U iU hU).inv ≫
          (immersionConormalSheafFactorIso V iV hV).hom := by
  have hVU' : iV ≫ X.homOfLE hVU = 𝟙 Z ≫ iU := by
    rw [Category.id_comp, ← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, hV, hU]
  have hU' : iU ≫ U.ι = 𝟙 Z ≫ i := hU.trans (Category.id_comp i).symm
  have hc := Stacks.Immersion.immersionConormalSheafMap_comp iV iU i (𝟙 Z) (X.homOfLE hVU) hVU'
    (𝟙 Z) U.ι hU'
  rw [eq_of_heq (immersionConormalSheafMap_heq_of_eq iV i (Category.id_comp _)
      (Scheme.homOfLE_ι X hVU) _
      (Stacks.Immersion.toShHom_square (hV.trans (Category.id_comp i).symm))),
    immersionConormalSheafMap_id_ι V iV hV, immersionConormalSheafMap_id_ι U iU hU] at hc
  have hX : ∀ M : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace),
      (modulePullbackComp (𝟙 Z.toRingedSpace) (𝟙 Z.toRingedSpace)).hom.app M ≫
        (modulePullback (𝟙 Z.toRingedSpace)).map ((modulePullbackId Z.toRingedSpace).hom.app M) =
        𝟙 _ := by
    intro M
    have hn : (modulePullback (𝟙 Z.toRingedSpace)).map
        ((modulePullbackId Z.toRingedSpace).hom.app M) =
        (modulePullbackId Z.toRingedSpace).hom.app ((modulePullback (𝟙 Z.toRingedSpace)).obj M) :=
      (Iso.cancel_iso_hom_right _ _ ((modulePullbackId Z.toRingedSpace).app M)).1
        ((modulePullbackId Z.toRingedSpace).hom.naturality
          ((modulePullbackId Z.toRingedSpace).hom.app M))
    rw [hn, ← modulePullbackComp_id_inv_app]
    exact Iso.hom_inv_id_app _ _
  have hnat := (modulePullbackId Z.toRingedSpace).hom.naturality
    (immersionConormalSheafFactorIso U iU hU).inv
  have hinv :
      (modulePullback (𝟙 Z.toRingedSpace)).map (immersionConormalSheafFactorIso U iU hU).inv ≫
      (modulePullback (𝟙 Z.toRingedSpace)).map (immersionConormalSheafFactorIso U iU hU).hom =
      𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  refine ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hinv.symm)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine ((congrArg (_ ≫ ·) ((Category.id_comp _).symm.trans
    (congrArg (· ≫ _) (hX (Stacks.Thickenings.immersionConormalSheaf i)).symm))).trans ?_)
  refine (congrArg (_ ≫ ·) ?_).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hnat).trans (Category.assoc _ _ _)))
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ hc.symm)
  exact congrArg (_ ≫ ·) (CategoryTheory.Functor.map_comp_assoc _ _ _ _).symm

end SchemeCoherence

section OpenFactor

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] {U : X.Opens}
  {i' : Z ⟶ U.toScheme} [IsImmersion i'] (hU : i' ≫ U.ι = i)

omit [IsImmersion i] [IsImmersion i'] in
include hU in
/-- `Z = Z ×_X U` for a factorization `i = i' ≫ ι_U` through an open subscheme. -/
theorem isPullback_id_ι : IsPullback i' (𝟙 Z) U.ι i :=
  IsPullback.of_vert_isIso_mono ⟨by rw [hU, Category.id_comp]⟩

/-- The identification of the duals of `𝒩` and of its base change along a cartesian square
whose edge `Z' ⟶ Z` is `𝟙 Z`. -/
def VirtualNormalBundle.baseChangeIdDualIso {X' : Scheme.{u}} {j : Z ⟶ X'} [IsImmersion j]
    (f : X' ⟶ X) (sq : IsPullback j (𝟙 Z) f i) (𝒩 : VirtualNormalBundle i) :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf 𝒩.bundle ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (𝒩.baseChange i j (𝟙 Z) f sq).bundle :=
  ((modulePullbackId Z.toRingedSpace).app
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf 𝒩.bundle)).symm ≪≫
    @asIso _ _ _ _ (pullbackDualMap (𝟙 Z) 𝒩.bundle)
      (pullbackDualMap_isIso (𝟙 Z) 𝒩.bundle 𝒩.isFiniteLocallyFree)

/-- The surjection of a base change along a square with source edge `𝟙 Z`, through
`baseChangeIdDualIso`: `𝒩.surjection` followed by `𝟙^* ≅ 𝟭` and the conormal map. -/
private theorem baseChangeIdDualIso_hom_comp_surjection_aux {Z X X' : Scheme.{u}}
    {i : Z ⟶ X} [IsImmersion i] {j : Z ⟶ X'} [IsImmersion j] (f : X' ⟶ X)
    (sq : IsPullback j (𝟙 Z) f i) (𝒩 : VirtualNormalBundle i) :
    (𝒩.baseChangeIdDualIso f sq).hom ≫ (𝒩.baseChange i j (𝟙 Z) f sq).surjection =
      𝒩.surjection ≫ (modulePullbackId Z.toRingedSpace).inv.app _ ≫
        Stacks.Immersion.immersionConormalSheafMap j i (𝟙 Z) f
          (Stacks.Immersion.toShHom_square sq.w) := by
  rw [VirtualNormalBundle.baseChange_surjection]
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc
    (@asIso _ _ _ _ (pullbackDualMap (𝟙 Z) 𝒩.bundle)
      (pullbackDualMap_isIso (𝟙 Z) 𝒩.bundle 𝒩.isFiniteLocallyFree)) _))).trans ?_
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    ((modulePullbackId Z.toRingedSpace).inv.naturality 𝒩.surjection).symm)).trans
    (Category.assoc _ _ _)

/-- **The virtual normal bundle `𝒩` read along `i = i' ≫ ι_U` is its base change along `ι_U`**,
compatibly with the surjections onto the conormal sheaf of `i'`. -/
theorem VirtualNormalBundle.baseChangeIdDualIso_hom_comp_surjection_ι
    (𝒩 : VirtualNormalBundle i) :
    (𝒩.baseChangeIdDualIso U.ι (isPullback_id_ι hU)).hom ≫
        (𝒩.baseChange i i' (𝟙 Z) U.ι (isPullback_id_ι hU)).surjection =
      (𝒩.toOpenFactor hU).surjection := by
  subst hU
  rw [baseChangeIdDualIso_hom_comp_surjection_aux, VirtualNormalBundle.toOpenFactor_surjection,
    immersionConormalSheafMap_id_ι U i' rfl]
  erw [Iso.inv_hom_id_app_assoc]

omit [IsImmersion i] [IsImmersion i'] in
include hU in
/-- `Z = Z ×_U V` for factorizations `i = i' ≫ ι_U = iV ≫ ι_V` through opens `V ⊆ U`. -/
theorem isPullback_id_homOfLE {V : X.Opens} (hVU : V ≤ U) {iV : Z ⟶ V.toScheme}
    (hV : iV ≫ V.ι = i) : IsPullback iV (𝟙 Z) (X.homOfLE hVU) i' :=
  IsPullback.of_vert_isIso_mono ⟨by
    rw [Category.id_comp, ← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, hV, hU]⟩

/-- **The virtual normal bundle `𝒩` read along `i = iV ≫ ι_V` is the base change along `V ⊆ U` of
`𝒩` read along `i = iU ≫ ι_U`**, compatibly with the surjections onto the conormal sheaf of
`iV`. -/
theorem VirtualNormalBundle.baseChangeIdDualIso_hom_comp_surjection_homOfLE
    (𝒩 : VirtualNormalBundle i) {V : X.Opens} (hVU : V ≤ U) {iV : Z ⟶ V.toScheme}
    [IsImmersion iV] (hV : iV ≫ V.ι = i) :
    ((𝒩.toOpenFactor hU).baseChangeIdDualIso (X.homOfLE hVU)
        (isPullback_id_homOfLE hU hVU hV)).hom ≫
        ((𝒩.toOpenFactor hU).baseChange i' iV (𝟙 Z) (X.homOfLE hVU)
          (isPullback_id_homOfLE hU hVU hV)).surjection =
      (𝒩.toOpenFactor hV).surjection := by
  rw [baseChangeIdDualIso_hom_comp_surjection_aux, VirtualNormalBundle.toOpenFactor_surjection,
    VirtualNormalBundle.toOpenFactor_surjection,
    immersionConormalSheafMap_id_homOfLE hVU i' iV hU hV]
  refine (Category.assoc _ _ _).trans (congrArg (𝒩.surjection ≫ ·) ?_)
  exact (congrArg (_ ≫ ·) (Iso.inv_hom_id_app_assoc (modulePullbackId Z.toRingedSpace) _ _)).trans
    (Iso.hom_inv_id_assoc _ _)

end OpenFactor

section OpenFactorClass

/-- The virtual normal bundle class only depends on the structure morphism of the target up to
equality. -/
private theorem virtualNormalBundleClass_heq_of_eq (C : ChowSituation.{u}) {Z X : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] {s s' : X ⟶ C.S} [LocallyOfFiniteType s]
    [LocallyOfFiniteType s'] (hss : s = s') {i : Z ⟶ X} [IsClosedImmersion i] (hs : i ≫ s = sZ)
    (hs' : i ≫ s' = sZ) (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    virtualNormalBundleClass C sZ s i hs 𝒩 r ≍ virtualNormalBundleClass C sZ s' i hs' 𝒩 r := by
  subst hss
  rfl

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {i : Z ⟶ X} [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) {U : X.Opens} {i' : Z ⟶ U.toScheme} [IsClosedImmersion i']
  (hU : i' ≫ U.ι = i) (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **Stacks 0FBK, the base-change clause along an open subscheme containing `Z`.** For a
factorization `i = i' ≫ ι_U` of the closed immersion `i` through an open subscheme `U ⊆ X`, the
restriction (Stacks 0F9Z) of `c(Z ⟶ X, 𝒩)` along `ι_U`, carried to `Z` along `Z ×_X U ≅ Z`, is
`c(Z ⟶ U, 𝒩)`, with `𝒩` read as a virtual normal bundle for `i'`. A special case, at constant
rank, of the base-change clause of Stacks 0FBK registered at arbitrary rank as
`Stacks.Chow.completedBivariantRestriction_completedVirtualNormalGysinClass`. -/
theorem bivariantTransport_bivariantRestriction_virtualNormalGysinClass_toOpenFactor
    (sZ' : Z ⟶ C.S) [LocallyOfFiniteType sZ'] (hi' : i' ≫ (U.ι ≫ sX) = sZ') :
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst i U.ι ≫ sZ) sZ' (U.ι ≫ sX)
        (pullback.snd i U.ι) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi U.ι) i' hi'
        (isPullback_id_ι hU).flip.isoPullback.symm ((isPullback_id_ι hU).flip.isoPullback_inv_snd)
        (r : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi U.ι (r : ℤ)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (virtualNormalBundleClass C sZ sX i hi 𝒩 r)) =
      virtualNormalBundleClass C sZ' (U.ι ≫ sX) i' hi' (𝒩.toOpenFactor hU) r := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (𝒩.baseChange i i' (𝟙 Z) U.ι (isPullback_id_ι hU)).bundle r :=
    isFiniteLocallyFreeOfRank_modulePullback (𝟙 Z) 𝒩.bundle r inferInstance
  exact (bivariantTransport_bivariantRestriction_virtualNormalGysinClass C sZ sX i hi i' (𝟙 Z)
    U.ι (isPullback_id_ι hU) 𝒩 r sZ' hi').trans
    (virtualNormalGysinClass_eq_of_dualIso C sZ' (U.ι ≫ sX) i' hi'
      (𝒩.baseChange i i' (𝟙 Z) U.ι (isPullback_id_ι hU)) (𝒩.toOpenFactor hU)
      (𝒩.baseChangeIdDualIso U.ι (isPullback_id_ι hU))
      (𝒩.baseChangeIdDualIso_hom_comp_surjection_ι hU) r)

end OpenFactorClass

section TwoOpensClass

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {i : Z ⟶ X} [IsImmersion i] (hi : i ≫ sX = sZ)
  {U V : X.Opens} (hVU : V ≤ U) {iU : Z ⟶ U.toScheme} [IsClosedImmersion iU]
  {iV : Z ⟶ V.toScheme} [IsClosedImmersion iV] (hU : iU ≫ U.ι = i) (hV : iV ≫ V.ι = i)
  (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

include hi in
/-- **The base-change clause of Stacks 0FBK along an inclusion of opens `V ⊆ U` containing `Z`.**
Let the immersion `i : Z ⟶ X` factor as closed immersions `iU : Z ⟶ U` and `iV : Z ⟶ V` through
opens `V ⊆ U` of `X`. The restriction (Stacks 0F9Z) of `c(Z ⟶ U, 𝒩)` along `V ⊆ U`, carried to
`Z` along `Z ×_U V ≅ Z`, is `c(Z ⟶ V, 𝒩)`, with `𝒩` read as a virtual normal bundle for `iU` and
for `iV`.

The restriction is a class over `V` for the structure morphism `(V ⊆ U) ≫ ι_U ≫ s_X`, which
equals `ι_V ≫ s_X` without being the same term; the two classes are therefore compared by `≍`. -/
theorem bivariantTransport_bivariantRestriction_virtualNormalGysinClass_homOfLE :
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst iU (X.homOfLE hVU) ≫ sZ) sZ
        (X.homOfLE hVU ≫ U.ι ≫ sX) (pullback.snd iU (X.homOfLE hVU))
        (pullbackSnd_comp_structureMorphism_eq C sZ (U.ι ≫ sX) iU
          (by rw [← Category.assoc, hU, hi]) (X.homOfLE hVU)) iV
        (by rw [Scheme.homOfLE_ι_assoc, ← Category.assoc, hV, hi])
        (isPullback_id_homOfLE hU hVU hV).flip.isoPullback.symm
        (isPullback_id_homOfLE hU hVU hV).flip.isoPullback_inv_snd (r : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) sZ (U.ι ≫ sX) iU
          (by rw [← Category.assoc, hU, hi]) (X.homOfLE hVU) (r : ℤ)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (virtualNormalBundleClass C sZ (U.ι ≫ sX) iU (by rw [← Category.assoc, hU, hi])
            (𝒩.toOpenFactor hU) r)) ≍
      virtualNormalBundleClass C sZ (V.ι ≫ sX) iV (by rw [← Category.assoc, hV, hi])
        (𝒩.toOpenFactor hV) r := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.toOpenFactor hU).baseChange iU iV (𝟙 Z) (X.homOfLE hVU)
        (isPullback_id_homOfLE hU hVU hV)).bundle r :=
    isFiniteLocallyFreeOfRank_modulePullback (𝟙 Z) 𝒩.bundle r inferInstance
  have hiV : iV ≫ (X.homOfLE hVU ≫ U.ι ≫ sX) = sZ := by
    rw [Scheme.homOfLE_ι_assoc, ← Category.assoc, hV, hi]
  refine (heq_of_eq ((bivariantTransport_bivariantRestriction_virtualNormalGysinClass C sZ
    (U.ι ≫ sX) iU (by rw [← Category.assoc, hU, hi]) iV (𝟙 Z) (X.homOfLE hVU)
    (isPullback_id_homOfLE hU hVU hV) (𝒩.toOpenFactor hU) r sZ hiV).trans
    (virtualNormalGysinClass_eq_of_dualIso C sZ (X.homOfLE hVU ≫ U.ι ≫ sX) iV hiV
      ((𝒩.toOpenFactor hU).baseChange iU iV (𝟙 Z) (X.homOfLE hVU)
        (isPullback_id_homOfLE hU hVU hV)) (𝒩.toOpenFactor hV)
      ((𝒩.toOpenFactor hU).baseChangeIdDualIso (X.homOfLE hVU)
        (isPullback_id_homOfLE hU hVU hV))
      (𝒩.baseChangeIdDualIso_hom_comp_surjection_homOfLE hU hVU hV) r))).trans ?_
  exact virtualNormalBundleClass_heq_of_eq C sZ (by rw [← Category.assoc, Scheme.homOfLE_ι])
    _ _ _ r

end TwoOpensClass

/-- The surjection of the base change of a virtual normal bundle along a square whose edge on
the source is an identity, read through `Stacks.Chow.VirtualNormalBundle.baseChangeIdDualIso`: the
original surjection followed by `𝟙^* ≅ 𝟭` and the conormal map of the square. -/
theorem VirtualNormalBundle.baseChangeIdDualIso_hom_comp_surjection {Z X X' : Scheme.{u}}
    {i : Z ⟶ X} [IsImmersion i] {j : Z ⟶ X'} [IsImmersion j] (f : X' ⟶ X)
    (sq : IsPullback j (𝟙 Z) f i) (𝒩 : VirtualNormalBundle i) :
    (𝒩.baseChangeIdDualIso f sq).hom ≫ (𝒩.baseChange i j (𝟙 Z) f sq).surjection =
      𝒩.surjection ≫ (modulePullbackId Z.toRingedSpace).inv.app _ ≫
        Stacks.Immersion.immersionConormalSheafMap j i (𝟙 Z) f
          (Stacks.Immersion.toShHom_square sq.w) :=
  baseChangeIdDualIso_hom_comp_surjection_aux f sq 𝒩

/-! ### The component neighbourhoods of two factorizations through opens `V ⊆ U` -/

section ComponentShrink

variable {Z X : Scheme.{u}} [LocallyConnectedSpace Z] {U V : X.Opens}
  [LocallyConnectedSpace U.toScheme] [LocallyConnectedSpace V.toScheme] (hVU : V ≤ U)
  {iU : Z ⟶ U.toScheme} [IsClosedImmersion iU] {iV : Z ⟶ V.toScheme} [IsClosedImmersion iV]
  (hιi : iV ≫ X.homOfLE hVU = iU) (z : _root_.ConnectedComponents Z)

include hιi in
/-- The component neighbourhood of `Z_z` in `V` lies in the preimage of the one in `U`. -/
theorem componentNeighbourhood_le_preimage_homOfLE :
    componentNeighbourhood iV z ≤ X.homOfLE hVU ⁻¹ᵁ componentNeighbourhood iU z := by
  rintro x ⟨hx₁, hx₂⟩
  refine ⟨?_, ?_⟩
  · have e : (X.homOfLE hVU).continuous.connectedComponentsMap
        (iV.continuous.connectedComponentsMap z) = iU.continuous.connectedComponentsMap z := by
      rw [← Scheme.Hom.connectedComponentsMap_comp, hιi]
    exact e ▸ (X.homOfLE hVU).mapsTo_connectedComponentOpens _ hx₁
  · rintro ⟨y, hy, hyx⟩
    refine hx₂ ⟨y, hy, (X.homOfLE hVU).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hιi]
    exact hyx

/-- The open immersion `W_V ⟶ W_U` of the component neighbourhoods of `Z_z` in `V` and in `U`. -/
abbrev componentNeighbourhoodShrink :
    (componentNeighbourhood iV z : Scheme.{u}) ⟶ (componentNeighbourhood iU z : Scheme.{u}) :=
  (X.homOfLE hVU).resLE _ _ (componentNeighbourhood_le_preimage_homOfLE hVU hιi z)

/-- The morphism `componentNeighbourhoodShrink` is an open immersion. -/
instance isOpenImmersion_componentNeighbourhoodShrink :
    IsOpenImmersion (componentNeighbourhoodShrink hVU hιi z) := by
  have : IsOpenImmersion (componentNeighbourhoodShrink hVU hιi z ≫
      (componentNeighbourhood iU z).ι) := by
    rw [Scheme.Hom.resLE_comp_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (componentNeighbourhood iU z).ι

include hιi in
/-- The inclusion `Z_z ⟶ W_V` followed by `W_V ⟶ W_U` is the inclusion `Z_z ⟶ W_U`. -/
theorem componentRestriction_comp_componentNeighbourhoodShrink :
    componentRestriction iV z ≫ componentNeighbourhoodShrink hVU hιi z =
      componentRestriction iU z := by
  rw [← cancel_mono (componentNeighbourhood iU z).ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
    componentRestriction_ι_assoc, hιi, componentRestriction_ι]

include hιi in
/-- `Z_z = Z_z ×_{W_U} W_V`. -/
theorem isPullback_componentNeighbourhoodShrink :
    IsPullback (componentRestriction iV z) (𝟙 _) (componentNeighbourhoodShrink hVU hιi z)
      (componentRestriction iU z) :=
  IsPullback.of_vert_isIso_mono ⟨by
    rw [Category.id_comp, componentRestriction_comp_componentNeighbourhoodShrink]⟩

include hιi in
/-- **The conormal maps of the component squares of two factorizations through opens `V ⊆ U`.**
The conormal map of `Z_z ⟶ W_U` over `Z ⟶ U`, preceded by `𝒞_{Z/X} ≅ 𝒞_{Z/U}` and followed by
`𝟙^* ≅ 𝟭` and the conormal map of `Z_z ⟶ W_V` over `Z_z ⟶ W_U`, is the conormal map of
`Z_z ⟶ W_V` over `Z ⟶ V` preceded by `𝒞_{Z/X} ≅ 𝒞_{Z/V}`: both are the conormal map of the
square `Z_z ⟶ W_V` over `Z ⟶ X`, by `Stacks.Immersion.immersionConormalSheafMap_comp` and
`Stacks.Chow.immersionConormalSheafMap_id_ι`. -/
theorem immersionConormalSheafMap_componentShrink {i : Z ⟶ X} [IsImmersion i]
    (hU : iU ≫ U.ι = i) (hV : iV ≫ V.ι = i) :
    (modulePullback (Z.connectedComponentOpens z).ι.toLRSHom.toShHom).map
        (immersionConormalSheafFactorIso U iU hU).hom ≫
      Stacks.Immersion.immersionConormalSheafMap (componentRestriction iU z) iU
          (Z.connectedComponentOpens z).ι (componentNeighbourhood iU z).ι
          (Stacks.Immersion.toShHom_square (isPullback_componentRestriction iU z).w) ≫
        (modulePullbackId (Z.connectedComponentOpens z : Scheme.{u}).toRingedSpace).inv.app _ ≫
          Stacks.Immersion.immersionConormalSheafMap (componentRestriction iV z)
            (componentRestriction iU z) (𝟙 _) (componentNeighbourhoodShrink hVU hιi z)
            (Stacks.Immersion.toShHom_square
              (isPullback_componentNeighbourhoodShrink hVU hιi z).w) =
      (modulePullback (Z.connectedComponentOpens z).ι.toLRSHom.toShHom).map
          (immersionConormalSheafFactorIso V iV hV).hom ≫
        Stacks.Immersion.immersionConormalSheafMap (componentRestriction iV z) iV
          (Z.connectedComponentOpens z).ι (componentNeighbourhood iV z).ι
          (Stacks.Immersion.toShHom_square (isPullback_componentRestriction iV z).w) := by
  -- `𝒞_{Z/X} ≅ 𝒞_{Z/U}` is a conormal map
  have hFU : (immersionConormalSheafFactorIso U iU hU).hom =
      (modulePullbackId Z.toRingedSpace).inv.app _ ≫
        Stacks.Immersion.immersionConormalSheafMap iU i (𝟙 Z) U.ι
          (Stacks.Immersion.toShHom_square (hU.trans (Category.id_comp i).symm)) := by
    rw [immersionConormalSheafMap_id_ι U iU hU, Iso.inv_hom_id_app_assoc]
  have hFV : (immersionConormalSheafFactorIso V iV hV).hom =
      (modulePullbackId Z.toRingedSpace).inv.app _ ≫
        Stacks.Immersion.immersionConormalSheafMap iV i (𝟙 Z) V.ι
          (Stacks.Immersion.toShHom_square (hV.trans (Category.id_comp i).symm)) := by
    rw [immersionConormalSheafMap_id_ι V iV hV, Iso.inv_hom_id_app_assoc]
  have c1 := Stacks.Immersion.immersionConormalSheafMap_comp (componentRestriction iU z) iU i
    (Z.connectedComponentOpens z).ι (componentNeighbourhood iU z).ι
    (isPullback_componentRestriction iU z).w (𝟙 Z) U.ι (hU.trans (Category.id_comp i).symm)
  have c3 := Stacks.Immersion.immersionConormalSheafMap_comp (componentRestriction iV z) iV i
    (Z.connectedComponentOpens z).ι (componentNeighbourhood iV z).ι
    (isPullback_componentRestriction iV z).w (𝟙 Z) V.ι (hV.trans (Category.id_comp i).symm)
  have c2 := Stacks.Immersion.immersionConormalSheafMap_comp (componentRestriction iV z)
    (componentRestriction iU z) i (𝟙 _) (componentNeighbourhoodShrink hVU hιi z)
    (isPullback_componentNeighbourhoodShrink hVU hιi z).w
    ((Z.connectedComponentOpens z).ι ≫ 𝟙 Z) ((componentNeighbourhood iU z).ι ≫ U.ι)
    (Stacks.Immersion.square_comp (isPullback_componentRestriction iU z).w
      (hU.trans (Category.id_comp i).symm))
  have hci : ∀ {A B : Scheme.{u}} (j : A ⟶ B)
      (M : SheafOfModules.{u} (structureSheafRing B.toRingedSpace)),
      (modulePullbackComp j.toLRSHom.toShHom (Scheme.Hom.toLRSHom (𝟙 B)).toShHom).hom.app M =
        (modulePullback j.toLRSHom.toShHom).map ((modulePullbackId B.toRingedSpace).inv.app M) :=
    fun j M ↦ modulePullbackComp_comp_id_hom_app j.toLRSHom.toShHom M
  have hic : ∀ {A B : Scheme.{u}} (j : A ⟶ B)
      (M : SheafOfModules.{u} (structureSheafRing B.toRingedSpace)),
      (modulePullbackComp (Scheme.Hom.toLRSHom (𝟙 A)).toShHom j.toLRSHom.toShHom).hom.app M =
        (modulePullbackId A.toRingedSpace).inv.app ((modulePullback j.toLRSHom.toShHom).obj M) := by
    intro A B j M
    exact (Iso.hom_eq_inv ((modulePullbackComp (Scheme.Hom.toLRSHom (𝟙 A)).toShHom
      j.toLRSHom.toShHom).app M) ((modulePullbackId A.toRingedSpace).app _)).2
      (modulePullbackComp_id_inv_app j.toLRSHom.toShHom M).symm
  rw [hci] at c1 c3
  rw [hic] at c2
  have hA := (congrArg (fun φ ↦
    (modulePullback (Z.connectedComponentOpens z).ι.toLRSHom.toShHom).map φ ≫
      Stacks.Immersion.immersionConormalSheafMap (componentRestriction iU z) iU
      (Z.connectedComponentOpens z).ι (componentNeighbourhood iU z).ι
      (Stacks.Immersion.toShHom_square (isPullback_componentRestriction iU z).w)) hFU).trans
    ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans c1.symm))
  have hC := (congrArg (fun φ ↦
    (modulePullback (Z.connectedComponentOpens z).ι.toLRSHom.toShHom).map φ ≫
      Stacks.Immersion.immersionConormalSheafMap (componentRestriction iV z) iV
      (Z.connectedComponentOpens z).ι (componentNeighbourhood iV z).ι
      (Stacks.Immersion.toShHom_square (isPullback_componentRestriction iV z).w)) hFV).trans
    ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans c3.symm))
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hA)).trans (Eq.trans ?_ hC.symm)
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    ((modulePullbackId (Z.connectedComponentOpens z : Scheme.{u}).toRingedSpace).inv.naturality
      _))).trans ((Category.assoc _ _ _).trans (c2.symm.trans ?_))
  refine eq_of_heq (immersionConormalSheafMap_heq_of_eq _ _ (Category.id_comp _) ?_ _ _)
  rw [Scheme.Hom.resLE_comp_ι_assoc, Scheme.homOfLE_ι]

include hιi in
/-- `W_V = V_{a'} ∩ (V ⊆ U)⁻¹(W_U)`: the component neighbourhood of `Z_z` in `V` is the part of
the connected component of `V` containing `Z_z` lying over the one in `U`. -/
theorem componentNeighbourhood_eq_preimage_inf :
    componentNeighbourhood iV z = X.homOfLE hVU ⁻¹ᵁ componentNeighbourhood iU z ⊓
      (𝟙 V.toScheme) ⁻¹ᵁ V.toScheme.connectedComponentOpens
        (iV.continuous.connectedComponentsMap z) := by
  refine le_antisymm (le_inf (componentNeighbourhood_le_preimage_homOfLE hVU hιi z)
    (componentNeighbourhood_le iV z)) ?_
  rintro x ⟨⟨-, hx⟩, hx'⟩
  refine ⟨hx', ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact hx ⟨y, hy, by rw [← Scheme.Hom.comp_apply, hιi]⟩


/-- **The virtual normal bundle of `Z_z ⟶ W_V` is the base change of that of `Z_z ⟶ W_U`**, for
`𝒩` read along the two factorizations `i = iU ≫ ι_U = iV ≫ ι_V` through opens `V ⊆ U`:
compatibly with the surjections onto the conormal sheaf of `Z_z ⟶ W_V`. -/
theorem VirtualNormalBundle.baseChangeIdDualIso_hom_comp_surjection_componentShrink
    {i : Z ⟶ X} [IsImmersion i] (hU : iU ≫ U.ι = i) (hV : iV ≫ V.ι = i)
    (𝒩 : VirtualNormalBundle i) :
    (((𝒩.toOpenFactor hU).toComponent iU z).baseChangeIdDualIso
        (componentNeighbourhoodShrink hVU hιi z)
        (isPullback_componentNeighbourhoodShrink hVU hιi z)).hom ≫
      (((𝒩.toOpenFactor hU).toComponent iU z).baseChange (componentRestriction iU z)
        (componentRestriction iV z) (𝟙 _) (componentNeighbourhoodShrink hVU hιi z)
        (isPullback_componentNeighbourhoodShrink hVU hιi z)).surjection =
      ((𝒩.toOpenFactor hV).toComponent iV z).surjection := by
  rw [VirtualNormalBundle.baseChangeIdDualIso_hom_comp_surjection]
  unfold VirtualNormalBundle.toComponent
  rw [VirtualNormalBundle.baseChange_surjection, VirtualNormalBundle.baseChange_surjection,
    VirtualNormalBundle.toOpenFactor_surjection, VirtualNormalBundle.toOpenFactor_surjection]
  have key := immersionConormalSheafMap_componentShrink hVU hιi z hU hV
  set M := modulePullback (Z.connectedComponentOpens z).ι.toLRSHom.toShHom
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (· ≫ _) (M.map_comp 𝒩.surjection _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (M.map 𝒩.surjection ≫ ·) key) ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (M.map_comp _ _).symm)

end ComponentShrink

/-! ### The class of Stacks 0FBK on the component neighbourhoods of `V ⊆ U` -/

section ComponentShrinkClass

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [LocallyConnectedSpace Z] {U V : X.Opens}
  [LocallyConnectedSpace U.toScheme] [LocallyConnectedSpace V.toScheme] (hVU : V ≤ U)
  {iU : Z ⟶ U.toScheme} [IsClosedImmersion iU] {iV : Z ⟶ V.toScheme} [IsClosedImmersion iV]
  (hιi : iV ≫ X.homOfLE hVU = iU) (z : _root_.ConnectedComponents Z) {i : Z ⟶ X} [IsImmersion i]
  (hi : i ≫ sX = sZ) (hU : iU ≫ U.ι = i) (hV : iV ≫ V.ι = i) (𝒩 : VirtualNormalBundle i)

/-- **Stacks 0FBK along the shrinking of component neighbourhoods.** The restriction (Stacks 0F9Z)
of `c(Z_z ⟶ W_U, 𝒩|)` along `W_V ⟶ W_U`, carried to `Z_z` along `Z_z ×_{W_U} W_V ≅ Z_z`, is
`c(Z_z ⟶ W_V, 𝒩|)`, for the component neighbourhoods `W_U`, `W_V` of a connected component
`Z_z` in two factorizations `i = iU ≫ ι_U = iV ≫ ι_V` through opens `V ⊆ U`. The two classes are
over the equal structure morphisms `(W_V ⟶ W_U) ≫ ι_{W_U} ≫ ι_U ≫ s_X` and `ι_{W_V} ≫ ι_V ≫ s_X`,
whence `≍`. -/
theorem bivariantTransport_bivariantRestriction_virtualNormalGysinClass_componentShrink :
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((𝒩.toOpenFactor hU).toComponent iU z).bundle (componentRank 𝒩.bundle z) :=
      VirtualNormalBundle.isFiniteLocallyFreeOfRank_toComponent iU z (𝒩.toOpenFactor hU)
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((𝒩.toOpenFactor hV).toComponent iV z).bundle (componentRank 𝒩.bundle z) :=
      VirtualNormalBundle.isFiniteLocallyFreeOfRank_toComponent iV z (𝒩.toOpenFactor hV)
    bivariantTransport C (gysinSystemOfInvertible C)
        (pullback.fst (componentRestriction iU z) (componentNeighbourhoodShrink hVU hιi z) ≫
          ((Z.connectedComponentOpens z).ι ≫ sZ)) ((Z.connectedComponentOpens z).ι ≫ sZ)
        (componentNeighbourhoodShrink hVU hιi z ≫ ((componentNeighbourhood iU z).ι ≫ (U.ι ≫ sX)))
        (pullback.snd (componentRestriction iU z) (componentNeighbourhoodShrink hVU hιi z))
        (pullbackSnd_comp_structureMorphism_eq C _ _ (componentRestriction iU z)
          (componentRestriction_comp_structureMorphism C sZ (U.ι ≫ sX) iU
            (by rw [← Category.assoc, hU, hi]) z)
          (componentNeighbourhoodShrink hVU hιi z))
        (componentRestriction iV z)
        (by rw [← Category.assoc, componentRestriction_comp_componentNeighbourhoodShrink,
          componentRestriction_comp_structureMorphism C sZ (U.ι ≫ sX) iU
            (by rw [← Category.assoc, hU, hi]) z])
        (isPullback_componentNeighbourhoodShrink hVU hιi z).flip.isoPullback.symm
        (isPullback_componentNeighbourhoodShrink hVU hιi z).flip.isoPullback_inv_snd
        (componentRank 𝒩.bundle z : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens z).ι ≫ sZ)
          ((componentNeighbourhood iU z).ι ≫ (U.ι ≫ sX)) (componentRestriction iU z)
          (componentRestriction_comp_structureMorphism C sZ (U.ι ≫ sX) iU
            (by rw [← Category.assoc, hU, hi]) z)
          (componentNeighbourhoodShrink hVU hιi z) (componentRank 𝒩.bundle z : ℤ)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (virtualNormalBundleClass C ((Z.connectedComponentOpens z).ι ≫ sZ)
            ((componentNeighbourhood iU z).ι ≫ (U.ι ≫ sX)) (componentRestriction iU z)
            (componentRestriction_comp_structureMorphism C sZ (U.ι ≫ sX) iU
              (by rw [← Category.assoc, hU, hi]) z)
            ((𝒩.toOpenFactor hU).toComponent iU z) (componentRank 𝒩.bundle z))) ≍
      virtualNormalBundleClass C ((Z.connectedComponentOpens z).ι ≫ sZ)
        ((componentNeighbourhood iV z).ι ≫ (V.ι ≫ sX)) (componentRestriction iV z)
        (componentRestriction_comp_structureMorphism C sZ (V.ι ≫ sX) iV
          (by rw [← Category.assoc, hV, hi]) z)
        ((𝒩.toOpenFactor hV).toComponent iV z) (componentRank 𝒩.bundle z) := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.toOpenFactor hU).toComponent iU z).bundle (componentRank 𝒩.bundle z) :=
    VirtualNormalBundle.isFiniteLocallyFreeOfRank_toComponent iU z (𝒩.toOpenFactor hU)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.toOpenFactor hV).toComponent iV z).bundle (componentRank 𝒩.bundle z) :=
    VirtualNormalBundle.isFiniteLocallyFreeOfRank_toComponent iV z (𝒩.toOpenFactor hV)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((𝒩.toOpenFactor hU).toComponent iU z).baseChange (componentRestriction iU z)
        (componentRestriction iV z) (𝟙 _) (componentNeighbourhoodShrink hVU hιi z)
        (isPullback_componentNeighbourhoodShrink hVU hιi z)).bundle (componentRank 𝒩.bundle z) :=
    isFiniteLocallyFreeOfRank_modulePullback (𝟙 _) _ _ inferInstance
  have hiV : componentRestriction iV z ≫ (componentNeighbourhoodShrink hVU hιi z ≫
      ((componentNeighbourhood iU z).ι ≫ (U.ι ≫ sX))) = (Z.connectedComponentOpens z).ι ≫ sZ := by
    rw [← Category.assoc, componentRestriction_comp_componentNeighbourhoodShrink,
      componentRestriction_comp_structureMorphism C sZ (U.ι ≫ sX) iU
        (by rw [← Category.assoc, hU, hi]) z]
  refine (heq_of_eq ((bivariantTransport_bivariantRestriction_virtualNormalGysinClass C
    ((Z.connectedComponentOpens z).ι ≫ sZ) ((componentNeighbourhood iU z).ι ≫ (U.ι ≫ sX))
    (componentRestriction iU z) _ (componentRestriction iV z) (𝟙 _)
    (componentNeighbourhoodShrink hVU hιi z) (isPullback_componentNeighbourhoodShrink hVU hιi z)
    ((𝒩.toOpenFactor hU).toComponent iU z) (componentRank 𝒩.bundle z) _ hiV).trans
    (virtualNormalGysinClass_eq_of_dualIso C ((Z.connectedComponentOpens z).ι ≫ sZ) _
      (componentRestriction iV z) hiV _ ((𝒩.toOpenFactor hV).toComponent iV z)
      (((𝒩.toOpenFactor hU).toComponent iU z).baseChangeIdDualIso
        (componentNeighbourhoodShrink hVU hιi z)
        (isPullback_componentNeighbourhoodShrink hVU hιi z))
      (VirtualNormalBundle.baseChangeIdDualIso_hom_comp_surjection_componentShrink hVU hιi z hU
        hV 𝒩) (componentRank 𝒩.bundle z)))).trans ?_
  refine virtualNormalBundleClass_heq_of_eq C _ ?_ _ _ _ _
  rw [Scheme.Hom.resLE_comp_ι_assoc, Scheme.homOfLE_ι_assoc]

end ComponentShrinkClass

end Stacks.Chow

end
