module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.CartesianCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.EtaleModuliSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseOpenGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.QuasiSeparated

/-!
# The morphism of moduli spaces of Stacks 0DUV is separated and étale, étale locally on `M`

Let `h : 𝒳' ⟶ 𝒳` be étale, separated and stabilizer preserving (Stacks 0DTW), let `f : 𝒳 ⟶ M` be a
1-morphism to an algebraic space, `f' : 𝒳' ⟶ M'` a uniform categorical moduli space and
`g : M' ⟶ M` with `f' ≫ g = h ≫ f`. Suppose that `M` is covered by étale morphisms `bⱼ : Mⱼ ⟶ M`
from objects of the site over which `f` is the moduli space of a well-nigh affine stack: the square
`𝒳ⱼ ⟶ 𝒳` over `Mⱼ ⟶ M` is cartesian and `𝒳ⱼ ⟶ Mⱼ` is a uniform categorical moduli space. (These are
the pieces from which the Keel–Mori moduli space is built in the proof of Stacks 0DUT.) Then `g` is
étale and separated.

For each `j`, Stacks 0DUS over the prescribed moduli space `Mⱼ` (applied to
`𝒳'ⱼ = 𝒳' ×_𝒳 𝒳ⱼ ⟶ 𝒳ⱼ`) gives a separated étale `M''ⱼ ⟶ Mⱼ` with `𝒳'ⱼ ⟶ M''ⱼ` a categorical
moduli space. By pasting, `𝒳'ⱼ` is also the base change of `f'` along `M' ×_M Mⱼ ⟶ M'`, so that
`M' ×_M Mⱼ` is a categorical moduli space of `𝒳'ⱼ` too; the two are isomorphic over `Mⱼ`, and
étaleness and separatedness are fpqc local on the target (Stacks 042B, 0421).

## Main results

* `AlgebraicGeometry.Stack.isEtale_and_isSeparated_pullback_snd_of_wellNighAffinePiece`
* `AlgebraicGeometry.Stack.isEtale_and_isSeparated_of_wellNighAffinePieces`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Piece

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳)
  {M M' : AlgebraicSpaces B S hS}
  (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
  (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS M'.obj M'.property) (g : M' ⟶ M)
  (hcomm : f'.hom ≫ (associatedMap B S hS g.hom).1 = h.hom ≫ f.hom)
  {𝒳j : AlgebraicStacks.{u, w} B S hS} (gj : 𝒳j ⟶ 𝒳) {Mj : BigFppfOver B S hS}
  (fj : 𝒳j ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj Mj) (isAlgebraicSpace_yoneda B S hS Mj))
  (bj : (⟨yoneda.obj Mj, isAlgebraicSpace_yoneda B S hS Mj⟩ : AlgebraicSpaces B S hS) ⟶ M)
  (hcommj : fj.hom ≫ (associatedMap B S hS bj.hom).1 = gj.hom ≫ f.hom)

include hcomm hcommj in
/-- **The base change of `f'` along `M' ×_M Mⱼ ⟶ M'` is a uniform categorical moduli space** of
`𝒳'ⱼ = 𝒳' ×_𝒳 𝒳ⱼ`, through a map compatible with `𝒳'ⱼ ⟶ 𝒳ⱼ ⟶ Mⱼ`. -/
theorem exists_isUniformCategoricalModuliSpace_pullback_of_wellNighAffinePiece
    (hf' : IsUniformCategoricalModuliSpace B S hS M' f'.hom)
    (hbj : Space.IsEtale B S hS bj.hom)
    (hcartj : Bicategory.IsTwoFibreProduct (spaceModuliSquare B S hS gj f fj bj hcommj)) :
    ∃ φ : (twoFibreProductSquareAlgebraicStacks B S hS h gj).pt ⟶
        algebraicSpaceStack.{u, w} B S hS (pullback g.hom bj.hom)
          (isAlgebraicSpace_pullback B S hS g.hom bj.hom M'.property
            (isAlgebraicSpace_yoneda B S hS Mj) M.property),
      φ.hom ≫ (associatedMap B S hS (pullback.snd g.hom bj.hom)).1 =
          (twoFibreProductSquareAlgebraicStacks B S hS h gj).snd.hom ≫ fj.hom ∧
        IsUniformCategoricalModuliSpace B S hS
          ⟨pullback g.hom bj.hom, isAlgebraicSpace_pullback B S hS g.hom bj.hom M'.property
            (isAlgebraicSpace_yoneda B S hS Mj) M.property⟩ φ.hom := by
  let P := twoFibreProductSquareAlgebraicStacks B S hS h gj
  have hMj := isAlgebraicSpace_yoneda B S hS Mj
  have hM'j := isAlgebraicSpace_pullback B S hS g.hom bj.hom M'.property hMj M.property
  let gS := algebraicSpaceStackMap.{u, w} B S hS M'.property M.property g.hom
  let bS := algebraicSpaceStackMap.{u, w} B S hS hMj M.property bj.hom
  have hcomm' : f' ≫ gS = h ≫ f := Bicategory.InducedBicategory.hom_ext hcomm
  have hcommj' : fj ≫ bS = gj ≫ f := Bicategory.InducedBicategory.hom_ext hcommj
  let Q := algebraicSpaceStackPullbackSquare.{u, w} B S hS M'.property hMj M.property g.hom bj.hom
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_algebraicSpaceStackPullbackSquare B S hS M'.property hMj M.property g.hom
      bj.hom
  let Z : Bicategory.TwoCommSq gS bS :=
    ⟨P.pt, P.fst ≫ f', P.snd ≫ fj,
      Bicategory.associator P.fst f' gS ≪≫ Bicategory.whiskerLeftIso P.fst (eqToIso hcomm') ≪≫
        (Bicategory.associator P.fst h f).symm ≪≫ Bicategory.whiskerRightIso P.iso f ≪≫
          Bicategory.associator P.snd gj f ≪≫
            Bicategory.whiskerLeftIso P.snd (eqToIso hcommj'.symm) ≪≫
              (Bicategory.associator P.snd fj bS).symm⟩
  let ρ : Bicategory.TwoCommSq.PreHom Z Q := Quotient.out (hQ.from Z)
  have hρsnd : ρ.hom ≫ Q.snd = P.snd ≫ fj :=
    Bicategory.InducedBicategory.hom_ext (hom_eq_of_hom₂ B S hS ρ.isoSnd.inv.hom)
  let T : Bicategory.TwoCommSq Q.swap.snd f' := ⟨P.pt, ρ.hom, P.fst, ρ.isoFst.symm⟩
  let Sq : Bicategory.TwoCommSq bS f := ⟨𝒳j, fj, gj, eqToIso hcommj'⟩
  have hSq : Bicategory.IsTwoFibreProduct Sq :=
    Bicategory.isTwoFibreProduct_of_underlying
      (isTwoFibreProduct_of_eq_of_discrete B S hS _ hcartj Sq.underlying.iso)
  have hR := Bicategory.isTwoFibreProduct_paste hSq (Bicategory.isTwoFibreProduct_swap
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS h gj))
  have key : ∀ (x : P.pt ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj Mj) hMj)
      (_ : x = P.snd ≫ fj) (k : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
      (_ : k = h ≫ f) (φ : x ≫ bS ≅ P.fst ≫ k),
      Bicategory.IsTwoFibreProduct (⟨P.pt, x, P.fst, φ⟩ : Bicategory.TwoCommSq bS k) := by
    rintro x rfl k rfl φ
    exact Bicategory.isTwoFibreProduct_of_underlying
      (isTwoFibreProduct_of_eq_of_discrete B S hS _
        (isTwoFibreProduct_underlying_algebraicStacks B S hS _ hR) _)
  have hT : Bicategory.IsTwoFibreProduct T :=
    isTwoFibreProduct_of_isTwoFibreProduct_paste B S hS (Bicategory.isTwoFibreProduct_swap hQ) T
      (key _ hρsnd _ hcomm' _)
  let pr₁ : (⟨pullback g.hom bj.hom, hM'j⟩ : AlgebraicSpaces B S hS) ⟶ M' :=
    ObjectProperty.homMk (pullback.fst g.hom bj.hom)
  exact ⟨ρ.hom, congrArg Bicategory.InducedBicategory.Hom.hom hρsnd,
    isUniformCategoricalModuliSpace_fst B S hS hf' pr₁ (Space.isFlat_of_isEtale B S hS
      (Space.isEtale_pullback_fst B S hS M'.property M.property hMj g.hom bj.hom hbj))
      T.underlying (isTwoFibreProduct_underlying_algebraicStacks B S hS T hT)⟩

include hcomm in
/-- **The base change of `g : M' ⟶ M` to one well-nigh affine piece `Mⱼ ⟶ M` of `f` is étale and
separated.** -/
theorem isEtale_and_isSeparated_pullback_snd_of_wellNighAffinePiece
    (he : IsEtale B S hS h) (hsep : AlgebraicStacks.IsSeparated B S hS h)
    (hauto : ∀ q : points B S hS 𝒳'.val.val 𝒳'.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS h q)
    (hf' : IsUniformCategoricalModuliSpace B S hS M' f'.hom)
    (hwna : IsWellNighAffine.{u, w} B S hS 𝒳j)
    (hfj : IsUniformCategoricalModuliSpace B S hS
      ⟨yoneda.obj Mj, isAlgebraicSpace_yoneda B S hS Mj⟩ fj.hom)
    (hbj : Space.IsEtale B S hS bj.hom)
    (hcartj : Bicategory.IsTwoFibreProduct (spaceModuliSquare B S hS gj f fj bj hcommj)) :
    Space.IsEtale B S hS (pullback.snd g.hom bj.hom) ∧
      Space.IsSeparated B S hS (pullback.snd g.hom bj.hom) := by
  let P := twoFibreProductSquareAlgebraicStacks B S hS h gj
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS h gj
  have hrep := AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_isEtale_of_inducesIsomorphismAt
    h he hauto
  have hPe : IsEtale B S hS P.snd := AlgebraicStacks.isEtale_of_isRelativelyEtale B S hS P.snd
    (isRelativelyEtale_baseChange B S hS _ _ _ h.hom gj.hom P.underlying.swap
      (Bicategory.isTwoFibreProduct_swap
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          h.hom gj.hom))
      (isRelativelyEtale_of_isEtale B S hS h hrep he))
  have hPs : AlgebraicStacks.IsSeparated B S hS P.snd :=
    AlgebraicStacks.isSeparated_baseChange_of_isTwoFibreProduct B S hS h gj P hP hsep
  have hPa : ∀ q, InducesIsomorphismAt B S hS P.snd q := fun q =>
    inducesIsomorphismAt_baseChange B S hS h gj P.swap (Bicategory.isTwoFibreProduct_swap hP) q
      (hauto _)
  obtain ⟨M'', f'', s, hcomm'', hsE, hsS, ⟨hsq⟩⟩ :=
    exists_moduliSquare_of_isEtale_of_isSeparated B S hS P.snd hwna hPe hPs hPa Mj fj
      (isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS hfj)
  have hsE' : Space.IsEtale B S hS (yoneda.map s) :=
    (Space.isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map s)).2
      ((Space.presheaf_yoneda_map_etale_iff B S hS s).2 hsE)
  let sM : (⟨yoneda.obj M'', isAlgebraicSpace_yoneda B S hS M''⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj Mj, isAlgebraicSpace_yoneda B S hS Mj⟩ := ObjectProperty.homMk (yoneda.map s)
  have hf''c := isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS
    (isUniformCategoricalModuliSpace_fst B S hS hfj sM (Space.isFlat_of_isEtale B S hS hsE')
      (ChartBaseChange.moduliSquare P.snd s fj.hom f''.hom hcomm'') hsq)
  obtain ⟨φ, hφsnd, hφ⟩ := exists_isUniformCategoricalModuliSpace_pullback_of_wellNighAffinePiece
    B S hS h f f' g hcomm gj fj bj hcommj hf' hbj hcartj
  obtain ⟨e, he⟩ := exists_iso_of_isCategoricalModuliSpace B S hS hf''c
    (isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS hφ)
  let pr₂ : (⟨pullback g.hom bj.hom, isAlgebraicSpace_pullback B S hS g.hom bj.hom M'.property
      (isAlgebraicSpace_yoneda B S hS Mj) M.property⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj Mj, isAlgebraicSpace_yoneda B S hS Mj⟩ :=
    ObjectProperty.homMk (pullback.snd g.hom bj.hom)
  have h1 : f''.hom ≫ (associatedMap B S hS (e.hom ≫ pr₂).hom).1 = P.snd.hom ≫ fj.hom := by
    change f''.hom ≫ (associatedMap B S hS (e.hom.hom ≫ pullback.snd g.hom bj.hom)).1 = _
    rwa [associatedMap_comp, ← Category.assoc, he]
  have huniq := (hf''c ⟨yoneda.obj Mj, isAlgebraicSpace_yoneda B S hS Mj⟩
    (P.snd.hom ≫ fj.hom)).unique (y₁ := e.hom ≫ pr₂) (y₂ := sM) ⟨eqToIso h1⟩ ⟨eqToIso hcomm''⟩
  have : IsIso e.hom.hom :=
    ⟨e.inv.hom, congrArg (fun k => k.hom) e.hom_inv_id, congrArg (fun k => k.hom) e.inv_hom_id⟩
  have hpr₂ : pullback.snd g.hom bj.hom = inv e.hom.hom ≫ yoneda.map s :=
    (IsIso.eq_inv_comp _).2 (congrArg (fun k => k.hom) huniq)
  rw [hpr₂]
  exact ⟨Space.isEtale_comp B S hS (Space.isEtale_of_isIso B S hS _) hsE',
    Space.isSeparated_comp B S hS _ _ (Space.isSeparated_of_isIso B S hS _)
      ((Space.isSeparated_yoneda_map_iff B S hS s).2 hsS)⟩

end Piece

/-- **The morphism of moduli spaces is étale and separated** when `M` is covered by étale
morphisms over which `f` is the moduli space of a well-nigh affine stack. -/
theorem isEtale_and_isSeparated_of_wellNighAffinePieces {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (h : 𝒳' ⟶ 𝒳)
    {M M' : AlgebraicSpaces B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS M'.obj M'.property) (g : M' ⟶ M)
    (hcomm : f'.hom ≫ (associatedMap B S hS g.hom).1 = h.hom ≫ f.hom)
    (he : IsEtale B S hS h) (hsep : AlgebraicStacks.IsSeparated B S hS h)
    (hauto : ∀ q : points B S hS 𝒳'.val.val 𝒳'.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS h q)
    (hf' : IsUniformCategoricalModuliSpace B S hS M' f'.hom)
    {J : Type u} (𝒳j : J → AlgebraicStacks.{u, w} B S hS) (gj : ∀ j, 𝒳j j ⟶ 𝒳)
    (hwna : ∀ j, IsWellNighAffine.{u, w} B S hS (𝒳j j)) (Mj : J → BigFppfOver B S hS)
    (fj : ∀ j, 𝒳j j ⟶
      algebraicSpaceStack.{u, w} B S hS (schemeSpace (Mj j)).obj (schemeSpace (Mj j)).property)
    (hfj : ∀ j, IsUniformCategoricalModuliSpace B S hS
      (schemeSpace (Mj j)) (fj j).hom)
    (bj : ∀ j, (schemeSpace (Mj j) :
      AlgebraicSpaces B S hS) ⟶ M)
    (hbj : ∀ j, Space.IsEtale B S hS (bj j).hom)
    (hcover : (⋃ j, Set.range (Space.pointsMap B S hS (yoneda.obj (Mj j)) (bj j).hom)) =
      Set.univ)
    (hcommj : ∀ j, (fj j).hom ≫ (associatedMap B S hS (bj j).hom).1 = (gj j).hom ≫ f.hom)
    (hcartj : ∀ j, Bicategory.IsTwoFibreProduct
      (spaceModuliSquare B S hS (gj j) f (fj j) (bj j) (hcommj j))) :
    Space.IsEtale B S hS g.hom ∧ Space.IsSeparated B S hS g.hom := by
  have hR : Presieve.ofArrows (fun j => (schemeSpace (Mj j) :
      AlgebraicSpaces B S hS)) bj ∈ Space.Topology.precoverage.{u, u} .fpqc B S hS M :=
    ⟨J, _, bj, rfl, M.property, fun j => isAlgebraicSpace_yoneda B S hS (Mj j),
      Space.isFpqcCovering_of_isEtaleCovering B S hS _ _
        ⟨M.property, fun j => isAlgebraicSpace_yoneda B S hS (Mj j), hbj, hcover⟩⟩
  have hloc : ∀ {U : AlgebraicSpaces B S hS} {b : U ⟶ M}, Presieve.ofArrows _ bj b →
      Space.IsEtale B S hS (pullback.snd g b).hom ∧
        Space.IsSeparated B S hS (pullback.snd g b).hom := by
    rintro U b ⟨j⟩
    have sq := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback g (bj j))
    have hiso : (sq.isoIsPullback _ _ (IsPullback.of_hasPullback g.hom (bj j).hom)).hom ≫
        pullback.snd g.hom (bj j).hom = (pullback.snd g (bj j)).hom :=
      sq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback g.hom (bj j).hom)
    obtain ⟨h1, h2⟩ := isEtale_and_isSeparated_pullback_snd_of_wellNighAffinePiece B S hS h f f' g
      hcomm (gj j) (fj j) (bj j) (hcommj j) he hsep hauto hf' (hwna j) (hfj j) (hbj j) (hcartj j)
    rw [← hiso]
    exact ⟨Space.isEtale_comp B S hS (Space.isEtale_of_isIso B S hS _) h1,
      Space.isSeparated_comp B S hS _ _ (Space.isSeparated_of_isIso B S hS _) h2⟩
  exact ⟨MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => Space.IsEtale B S hS f.hom)
      hR (fun hb => (hloc hb).1),
    MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := Space.separatedProperty B S hS)
      hR (fun hb => (hloc hb).2)⟩

end AlgebraicGeometry.Stack

end
