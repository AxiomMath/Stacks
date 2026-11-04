module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.FrobeniusColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.ZariskiCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Recovery21.FilteredColimitsAndCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactObjects.PerfectObjectsOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Limits.DescendOpensAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `𝒪^h` on the opens of `S` is `colim_F 𝒪_S`, and Zariski cohomology of it

Let `p` be a prime, `S` a quasi-compact and quasi-separated scheme over `𝔽_p` and `B` a big h
site containing `S`. Restricting the h sheaf `𝒪^h = (X ↦ Γ(Xᵃʷⁿ, 𝒪))` of the big h category over
`S` to the small Zariski site of `S` gives an abelian sheaf on `S`, and this file identifies it
with the colimit, in abelian sheaves on `S`, of the Frobenius system

`𝒪_S →^F 𝒪_S →^F 𝒪_S →^F ⋯`.

Combined with Stacks 0739 on the site of opens of `S`, this computes the Zariski cohomology of the
restriction of `𝒪^h` as `colim_F H^i(S, 𝒪_S)`.

## Main definitions

* `AlgebraicGeometry.Scheme.abelianStructureSheaf`: the structure sheaf of `S` as an abelian
  sheaf on the opens of `S`.
* `AlgebraicGeometry.Scheme.frobeniusAbelianStructureSheaf`: its Frobenius `f ↦ f^p`.
* `AlgebraicGeometry.Scheme.abelianFrobeniusSystem`: the system `𝒪_S →^F 𝒪_S →^F ⋯`.
* `AlgebraicGeometry.BigHOver.awnSheafAb`: the abelian h sheaf underlying `X ↦ Γ(Xᵃʷⁿ, 𝒪)`.
* `AlgebraicGeometry.BigHOver.zariskiPerfectionCocone`: the cocone on the Frobenius system of `S`
  with vertex the restriction of `awnSheafAb` to the opens of `S`.

## Main results

* `AlgebraicGeometry.Scheme.isIso_colimit_post_abelianFrobeniusSystem`: the canonical map
  `colim_F H^i(S, 𝒪_S) ⟶ H^i(S, colim_F 𝒪_S)` is an isomorphism for `S` quasi-compact and
  quasi-separated (Stacks 0739).
* `AlgebraicGeometry.BigHOver.isColimitZariskiPerfectionCocone`: the cocone is a colimit.

## References

* [Stacks Project, Tag 0EWU](https://stacks.math.columbia.edu/tag/0EWU)
* [Stacks Project, Tag 0EVK](https://stacks.math.columbia.edu/tag/0EVK)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme

variable (S : Scheme.{u})

/-- **The structure sheaf of a scheme as an abelian sheaf** on its opens. -/
def abelianStructureSheaf : Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u} :=
  ⟨S.presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat,
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ S.sheaf.property⟩

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)

/-- **The Frobenius `F : 𝒪_S ⟶ 𝒪_S`, `f ↦ f^p`,** of a scheme over `𝔽_p`, as a map of abelian
sheaves. -/
@[sga "7 XXI 1.0"]
def frobeniusAbelianStructureSheaf : S.abelianStructureSheaf ⟶ S.abelianStructureSheaf :=
  ObjectProperty.homMk (Functor.whiskerRight (Presheaf.frobeniusRingHom S.presheaf p
    (fun U ↦ Stacks.Frobenius.cast_eq_zero_of_isInCharacteristic hSp U.unop))
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))

/-- The Frobenius of the abelian structure sheaf raises a section to its `p`-th power. -/
theorem frobeniusAbelianStructureSheaf_hom_app_apply (U : (Opens S)ᵒᵖ) (a : Γ(S, U.unop)) :
    (S.frobeniusAbelianStructureSheaf p hSp).hom.app U a = a ^ p :=
  Stacks.Frobenius.primePowerEndomorphism_apply _ p
    (Stacks.Frobenius.cast_eq_zero_of_isInCharacteristic hSp U.unop) a

/-- **The Frobenius system `𝒪_S →^F 𝒪_S →^F 𝒪_S →^F ⋯`** of abelian sheaves on a scheme over
`𝔽_p`, all of whose transition maps are the Frobenius. -/
def abelianFrobeniusSystem : ℕ ⥤ Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u} :=
  Functor.ofSequence (X := fun _ ↦ S.abelianStructureSheaf)
    (fun _ ↦ S.frobeniusAbelianStructureSheaf p hSp)

/-- Every transition map of the Frobenius system is the Frobenius. -/
theorem abelianFrobeniusSystem_map_succ (n : ℕ) :
    (S.abelianFrobeniusSystem p hSp).map (homOfLE n.le_succ) =
      S.frobeniusAbelianStructureSheaf p hSp :=
  Functor.ofSequence_map_homOfLE_succ _ n

attribute [local instance] Stacks.Topology.enoughInjectives_sheafOpens

/-- **Stacks 0739 for the opens of a quasi-compact quasi-separated scheme and the Frobenius
system**: the canonical map `colim_F H^i(S, 𝒪_S) ⟶ H^i(S, colim_F 𝒪_S)` is an isomorphism. -/
theorem isIso_colimit_post_abelianFrobeniusSystem [CompactSpace S] [QuasiSeparatedSpace S]
    (i : ℕ) :
    IsIso (colimit.post (S.abelianFrobeniusSystem p hSp)
      (((sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived i)) := by
  let E : AsSmall.{u} ℕ ⥤ ℕ := AsSmall.down
  have : E.IsEquivalence := (AsSmall.equiv.{0, 0, u} (C := ℕ)).isEquivalence_inverse
  let G := ((sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj
    (op ⊤)).rightDerived i
  have hpost : IsIso (colimit.post (E ⋙ S.abelianFrobeniusSystem p hSp) G) :=
    Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections
      (Opens.grothendieckTopology S) (Stacks.Cohomology.Basis.compactOpens S)
      Stacks.Cohomology.RingedSpaceCompact.compactHypercovers
      (fun _ E hE ↦ Stacks.Cohomology.RingedSpaceCompact.sieve₀_mem_of_mem_compactHypercovers E hE)
      (fun _ E hE ↦
        Stacks.Cohomology.RingedSpaceCompact.hasIntersectionsIn_of_mem_compactHypercovers
          inferInstance E hE)
      (fun U hU R hR ↦ Stacks.Cohomology.RingedSpaceCompact.exists_mem_compactHypercovers_sieve₀_le
        inferInstance inferInstance U hU R hR)
      i ⊤ isCompact_univ _
  have h := colimit.pre_post E (S.abelianFrobeniusSystem p hSp) G
  have : IsIso (colimit.post (S.abelianFrobeniusSystem p hSp) G) := by
    rw [← IsIso.inv_comp_eq] at h
    rw [← h]
    infer_instance
  exact this

end Scheme

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The abelian h sheaf `𝒪^h`**: the abelian sheaf underlying `X ↦ Γ(Xᵃʷⁿ, 𝒪)` on the big h
category over `S`. -/
abbrev awnSheafAb : Sheaf (BigHOver.topology B S hS) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (awnRingSheaf B S hS))).obj
    (SheafOfModules.unit _)

/-- The global functions on the open subscheme cut out by an open `V` of `S` are the sections of
`𝒪_S` over `V`. -/
def opensSectionsIso : (opensToBigH B S hS).op ⋙ sectionsRingPresheaf B S hS ≅ S.presheaf :=
  Scheme.restrictFunctorΓ

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)

/-- The map of presheaves of rings on the opens of `S` underlying the stage `n` leg of the
Zariski perfection cocone: identify `Γ(S, V)` with the global functions on the open subscheme `V`
and send a function to the `pⁿ`-th root of its pullback to `Vᵃʷⁿ`. -/
def zariskiStage (n : ℕ) :
    S.presheaf ⟶ (opensToBigH B S hS).op ⋙ (awnRingSheaf B S hS).obj :=
  (opensSectionsIso B S hS).inv ≫
    Functor.whiskerLeft (opensToBigH B S hS).op (perfectionStage B S hS p hSp n)

/-- `zariskiStage n` sends a section `a` of `𝒪_S` over `V` to the image under the stage `n` map
`awnStageFun` of the corresponding global function on the open subscheme `V`. -/
theorem zariskiStage_app_apply (n : ℕ) (V : (Opens S)ᵒᵖ) (a : Γ(S, V.unop)) :
    (zariskiStage B S hS p hSp n).app V a = awnStageFun B S hS p hSp n
      ((opensToBigH B S hS).obj V.unop) ((opensSectionsIso B S hS).inv.app V a) :=
  perfectionStage_app_apply B S hS p hSp n _ _

/-- `zariskiStage (n + 1)` sends `a ^ p` to the image of `a` under `zariskiStage n`. -/
theorem zariskiStage_succ_apply_pow (n : ℕ) (V : (Opens S)ᵒᵖ) (a : Γ(S, V.unop)) :
    (zariskiStage B S hS p hSp (n + 1)).app V (a ^ p) = (zariskiStage B S hS p hSp n).app V a := by
  show (perfectionStage B S hS p hSp (n + 1)).app (op ((opensToBigH B S hS).obj V.unop))
      ((opensSectionsIso B S hS).inv.app V (a ^ p)) =
    (perfectionStage B S hS p hSp n).app (op ((opensToBigH B S hS).obj V.unop))
      ((opensSectionsIso B S hS).inv.app V a)
  have h1 : (opensSectionsIso B S hS).inv.app V (a ^ p) =
      ((opensSectionsIso B S hS).inv.app V a) ^ p := map_pow _ a p
  have h2 := ConcreteCategory.congr_hom
    (congr_app (frobeniusSections_comp_perfectionStage B S hS p hSp n)
      (op ((opensToBigH B S hS).obj V.unop))) ((opensSectionsIso B S hS).inv.app V a)
  rw [h1, ← h2, NatTrans.comp_app, CommRingCat.comp_apply, frobeniusSections_app_apply]

/-- The stage `n` leg of the Zariski perfection cocone, as a map of abelian sheaves on `S`. -/
def zariskiLeg (n : ℕ) :
    S.abelianStructureSheaf ⟶ (zariskiRestriction B S hS).obj (awnSheafAb B S hS) :=
  ObjectProperty.homMk (Functor.whiskerRight (zariskiStage B S hS p hSp n)
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))

/-- On sections, `zariskiLeg n` is `zariskiStage n`. -/
theorem zariskiLeg_hom_app_apply (n : ℕ) (V : (Opens S)ᵒᵖ) (a : Γ(S, V.unop)) :
    (zariskiLeg B S hS p hSp n).hom.app V a = (zariskiStage B S hS p hSp n).app V a :=
  rfl

/-- **The Zariski perfection cocone**: the cocone on the Frobenius system `𝒪_S →^F 𝒪_S →^F ⋯`
with vertex the restriction of `𝒪^h` to the opens of `S`, whose leg at stage `n` sends a function
to the `pⁿ`-th root of its pullback to the absolute weak normalization. -/
def zariskiPerfectionCocone : Cocone (S.abelianFrobeniusSystem p hSp) where
  pt := (zariskiRestriction B S hS).obj (awnSheafAb B S hS)
  ι := NatTrans.ofSequence (zariskiLeg B S hS p hSp) (fun n ↦ by
    rw [Scheme.abelianFrobeniusSystem_map_succ]
    refine Sheaf.hom_ext ?_
    ext V a
    simp only [Functor.const_obj_map]
    change (zariskiLeg B S hS p hSp (n + 1)).hom.app V
        ((S.frobeniusAbelianStructureSheaf p hSp).hom.app V a) =
      (zariskiLeg B S hS p hSp n).hom.app V a
    exact (congrArg ((zariskiLeg B S hS p hSp (n + 1)).hom.app V)
      (Scheme.frobeniusAbelianStructureSheaf_hom_app_apply S p hSp V a)).trans
        (zariskiStage_succ_apply_pow B S hS p hSp n V a))

/-! ### The cocone is a colimit -/

section Colimit

/-- **Over an affine open of `S`, the Zariski perfection cocone is a colimit on sections**, after
forgetting to sets. -/
theorem nonempty_isColimit_sections_zariskiPerfectionCocone (V : S.Opens) (hV : IsAffineOpen V) :
    Nonempty (IsColimit (((sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj
      (op V) ⋙ CategoryTheory.forget AddCommGrpCat).mapCocone
        (zariskiPerfectionCocone B S hS p hSp))) := by
  let X := (opensToBigH B S hS).obj V
  have : IsAffine ((BigHOver.toScheme B S hS).obj X) := hV
  let ev := (evaluation (BigHOver B S hS)ᵒᵖ (Type u)).obj (op X)
  let G := frobeniusSectionsSequence B S hS p ⋙ ev
  let t : Cocone G := ev.mapCocone (awnCocone B S hS p hSp)
  let P : IsColimit (ev.mapCocone (colimit.cocone (frobeniusSectionsSequence B S hS p))) :=
    isColimitOfPreserves ev (colimit.isColimit _)
  have hdesc : P.desc t = (awnComparison B S hS p hSp).app (op X) := by
    refine P.hom_ext (fun n ↦ ?_)
    rw [P.fac]
    exact (congr_app (colimit.ι_desc (awnCocone B S hS p hSp) n) (op X)).symm
  have : IsIso (P.desc t) := by
    rw [hdesc]
    exact (isIso_iff_bijective _).2 (bijective_awnComparison_app B S hS p hSp X)
  let ht : IsColimit t := IsColimit.ofPointIso P
  let F' := S.abelianFrobeniusSystem p hSp ⋙
    (sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj (op V) ⋙
      CategoryTheory.forget AddCommGrpCat
  let d : F' ⟶ G := NatTrans.ofSequence
    (fun _ ↦ (CategoryTheory.forget CommRingCat).map ((opensSectionsIso B S hS).inv.app (op V)))
    (fun n ↦ by
      ext a
      have hG : G.map (homOfLE n.le_succ) = (frobeniusSectionsHom B S hS p).app (op X) :=
        congr_app (frobeniusSectionsSequence_map_succ B S hS p n) (op X)
      exact (congrArg ((opensSectionsIso B S hS).inv.app (op V))
          ((congrArg (fun φ ↦ φ.hom.app (op V) a)
            (Scheme.abelianFrobeniusSystem_map_succ S p hSp n)).trans
              (Scheme.frobeniusAbelianStructureSheaf_hom_app_apply S p hSp (op V) a))).trans
        ((map_pow ((opensSectionsIso B S hS).inv.app (op V)).hom (show Γ(S, V) from a) p).trans
          ((congrArg (fun φ ↦ φ ((opensSectionsIso B S hS).inv.app (op V) a)) hG).trans
            (frobeniusSectionsHom_app B S hS p (op X) _)).symm))
  have : ∀ n, IsIso (d.app n) := fun _ ↦ inferInstanceAs (IsIso
    ((CategoryTheory.forget CommRingCat).map ((opensSectionsIso B S hS).inv.app (op V))))
  have : IsIso d := NatIso.isIso_of_isIso_app d
  let e : (Cocone.precompose (asIso d).hom).obj t ≅
      (((sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj (op V) ⋙
        CategoryTheory.forget AddCommGrpCat).mapCocone (zariskiPerfectionCocone B S hS p hSp)) :=
    Cocone.ext (Iso.refl _) (fun n ↦ by
      ext a
      exact (zariskiStage_app_apply B S hS p hSp n (op V) a).symm)
  exact ⟨IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv (asIso d) t).symm ht) e⟩

/-- Preserving colimits indexed by `AsSmall ℕ` gives preserving colimits indexed by `ℕ`. -/
private theorem preservesColimitsOfShape_nat_of_asSmall {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [PreservesColimitsOfShape (AsSmall.{u} ℕ) F] : PreservesColimitsOfShape ℕ F :=
  preservesColimitsOfShape_of_equiv (AsSmall.equiv.{0, 0, u} (C := ℕ)).symm _

/-- Sections of abelian sheaves over a quasi-compact open of a quasi-separated scheme, followed by
the forgetful functor to sets, commute with colimits indexed by `ℕ` (Stacks 009F). -/
theorem preservesColimitsOfShape_nat_sections_forget [QuasiSeparatedSpace S] (V : S.Opens)
    (hV : IsCompact (V : Set S)) :
    PreservesColimitsOfShape ℕ ((sheafSections (Opens.grothendieckTopology S)
      AddCommGrpCat.{u}).obj (op V) ⋙ CategoryTheory.forget AddCommGrpCat) := by
  have : PreservesColimitsOfShape (AsSmall.{u} ℕ) ((sheafSections (Opens.grothendieckTopology S)
      AddCommGrpCat.{u}).obj (op V)) :=
    Stacks.Cohomology.AbelianSpectral.preservesColimitsOfShape_sheafSections_of_isCompact V hV
  have := preservesColimitsOfShape_nat_of_asSmall.{u} ((sheafSections
    (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj (op V))
  have := preservesColimitsOfShape_nat_of_asSmall.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  infer_instance

/-- **The canonical map `colim_F 𝒪_S ⟶ 𝒪^h|_S` is bijective over every affine open** of a
quasi-separated scheme. -/
theorem bijective_colimitDesc_zariskiPerfectionCocone_app [QuasiSeparatedSpace S] (V : S.Opens)
    (hV : IsAffineOpen V) :
    Function.Bijective ((colimit.desc (S.abelianFrobeniusSystem p hSp)
      (zariskiPerfectionCocone B S hS p hSp)).hom.app (op V)) := by
  let sec := (sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj (op V) ⋙
    CategoryTheory.forget AddCommGrpCat
  have := preservesColimitsOfShape_nat_sections_forget S V hV.isCompact
  let P₁ := isColimitOfPreserves sec (colimit.isColimit (S.abelianFrobeniusSystem p hSp))
  obtain ⟨P₂⟩ := nonempty_isColimit_sections_zariskiPerfectionCocone B S hS p hSp V hV
  have heq : sec.map (colimit.desc _ (zariskiPerfectionCocone B S hS p hSp)) =
      P₁.desc (sec.mapCocone (zariskiPerfectionCocone B S hS p hSp)) :=
    P₁.uniq (sec.mapCocone (zariskiPerfectionCocone B S hS p hSp)) _ (fun n ↦ by
      simp only [Functor.mapCocone_ι_app, colimit.cocone_ι, ← Functor.map_comp, colimit.ι_desc])
  have : IsIso (sec.map (colimit.desc _ (zariskiPerfectionCocone B S hS p hSp))) := by
    rw [heq]
    exact (IsColimit.coconePointUniqueUpToIso P₁ P₂).isIso_hom
  exact (isIso_iff_bijective _).1 this

/-- **`colim_F 𝒪_S` is the restriction of `𝒪^h` to the opens of `S`**, for `S` quasi-separated:
the canonical map is an isomorphism of sheaves. -/
theorem isIso_colimitDesc_zariskiPerfectionCocone [QuasiSeparatedSpace S] :
    IsIso (colimit.desc (S.abelianFrobeniusSystem p hSp)
      (zariskiPerfectionCocone B S hS p hSp)) := by
  let φ := colimit.desc (S.abelianFrobeniusSystem p hSp) (zariskiPerfectionCocone B S hS p hSp)
  rw [← Sheaf.isLocallyBijective_iff_isIso φ]
  constructor
  · refine ⟨fun {U} x y hxy ↦ ?_⟩
    refine (Opens.grothendieckTopology S).superset_covering ?_
      (generate_affineOpensPresieve_mem S U.unop)
    rw [Sieve.generate_le_iff]
    intro W g hW
    apply (bijective_colimitDesc_zariskiPerfectionCocone_app B S hS p hSp W hW).1
    rw [NatTrans.naturality_apply φ.hom, NatTrans.naturality_apply φ.hom, hxy]
  · refine ⟨fun {U} s ↦ ?_⟩
    refine (Opens.grothendieckTopology S).superset_covering ?_
      (generate_affineOpensPresieve_mem S U)
    rw [Sieve.generate_le_iff]
    intro W g hW
    exact (bijective_colimitDesc_zariskiPerfectionCocone_app B S hS p hSp W hW).2 _

/-- **The Zariski perfection cocone is a colimit**: on a quasi-separated scheme `S` over `𝔽_p`,
the restriction of `𝒪^h` to the opens of `S` is `colim_F 𝒪_S`, the colimit in abelian sheaves on
`S` of the Frobenius system. -/
def isColimitZariskiPerfectionCocone [QuasiSeparatedSpace S] :
    IsColimit (zariskiPerfectionCocone B S hS p hSp) :=
  have : IsIso ((colimit.isColimit _).desc (zariskiPerfectionCocone B S hS p hSp)) :=
    isIso_colimitDesc_zariskiPerfectionCocone B S hS p hSp
  IsColimit.ofPointIso (colimit.isColimit _)

end Colimit

end BigHOver

end AlgebraicGeometry
