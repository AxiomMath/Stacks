module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra.LocalIntertwiner
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra.IntertwinerSheaf
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra.LocalIntertwiner

/-!
# The invertible twist (Tag 0A2K)

The local step on a neighbourhood where `F` and `G` are free of positive rank and a rank-one
coefficient is a unit, and the assembly: the intertwiner sheaf of an isomorphism of endomorphism
algebra sheaves is invertible and evaluation identifies `F ⊗ L` with `G`.
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.EtaleCohomology

section
/-- A section of the intertwiner sheaf over `U` naming an isomorphism `F|_U ≅ G|_U` is a basis of
one element over every open subset of `U`, and names a bijection there. -/
private lemma sheafIntertwiner_basis_of_isIso
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)}
    (HFF : SheafHom Rc F F) (HGG : SheafHom Rc G G) (HFG : SheafHom Rc F G)
    (α : HFF.obj ⟶ HGG.obj) (U : Opens X) {I : Type u} [Finite I] [Nonempty I]
    (eF : SheafOfModules.free I ≅ F.over U)
    (t : (sheafIntertwiner HFF HGG HFG α).toSheafOfModules.val.obj (op U))
    [IsIso (HFG.sectionsEquiv U t.1)] :
    let N := sheafIntertwiner HFF HGG HFG α
    let L := N.toSheafOfModules
    (∀ (V : Opens X) (hVU : V ≤ U), Function.Bijective
      (fun r : Rc.obj.obj (op V) => r • L.val.map (homOfLE hVU).op t)) ∧
    (∀ (V : Opens X) (hVU : V ≤ U), Function.Bijective
      (sheafHomApp HFG U V hVU (N.ι.val.app (op U) t))) := by
  dsimp only
  have hb (V : Opens X) (hVU : V ≤ U) :
      Function.Bijective (sheafHomApp HFG U V hVU t.1) := by
    change Function.Bijective
      (((HFG.sectionsEquiv U t.1).val.app (op (Over.mk (homOfLE hVU)))).hom)
    apply (ConcreteCategory.isIso_iff_bijective _).mp
    exact inferInstanceAs (IsIso
      ((PresheafOfModules.evaluation _ (op (Over.mk (homOfLE hVU)))).map
        ((SheafOfModules.forget _).map (HFG.sectionsEquiv U t.1))))
  refine ⟨?_, hb⟩
  intro V hVU
  apply sheafIntertwiner_basis_of_bijective HFF HGG HFG α V (restrictFreeIso eF hVU)
  have he : sheafHomApp HFG V V le_rfl (HFG.obj.val.map (homOfLE hVU).op t.1) =
      sheafHomApp HFG U V hVU t.1 := by
    ext f
    exact sheafHomApp_restrict HFG hVU le_rfl _ _
  change Function.Bijective
    (sheafHomApp HFG V V le_rfl (HFG.obj.val.map (homOfLE hVU).op t.1))
  rw [he]
  exact hb V hVU
end

section
open CategoryTheory.Limits
/-- A morphism between sheaves of modules trivialized over `U` by free sheaves on finite types is
an isomorphism as soon as its component at the terminal object of the slice site is bijective. -/
private lemma isIso_of_bijective_on_sections
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)} (U : Opens X)
    {I K : Type u} [Finite I] [Finite K]
    (eF : SheafOfModules.free I ≅ F.over U) (eG : SheafOfModules.free K ≅ G.over U)
    (f : F.over U ⟶ G.over U)
    (hf : Function.Bijective ((f.val.app (op (Over.mk (𝟙 U)))).hom)) : IsIso f := by
  let V := op (Over.mk (𝟙 U))
  let T := LinearEquiv.ofBijective (f.val.app V).hom hf
  obtain ⟨g, hg⟩ := (homEvaluation_bijective_of_free (Rc.over U) K V eG
    (initialOpOfTerminal (Over.mkIdTerminal (X := U)))).surjective T.symm.toLinearMap
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply (homEvaluation_bijective_of_free (Rc.over U) I V eF
      (initialOpOfTerminal (Over.mkIdTerminal (X := U)))).injective
    refine LinearMap.ext fun y => ?_
    exact (congrArg (fun m => m ((f.val.app V).hom y)) hg).trans (T.symm_apply_apply y)
  · apply (homEvaluation_bijective_of_free (Rc.over U) K V eG
      (initialOpOfTerminal (Over.mkIdTerminal (X := U)))).injective
    refine LinearMap.ext fun y => ?_
    exact (congrArg (fun m => (f.val.app V).hom (m y)) hg).trans (T.apply_symm_apply y)

/-- A linear equivalence conjugating the induced algebra isomorphism over a trivializing open
is named by a section of the intertwiner sheaf, which is an isomorphism `F|_U ≅ G|_U`. -/
private lemma exists_isIso_intertwinerSection_of_conjAlgEquiv
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)}
    (HFF : SheafHom Rc F F) (HGG : SheafHom Rc G G)
    (HFG : SheafHom Rc F G) (α : HFF.obj ≅ HGG.obj)
    (hα_one : ∀ U : Opens X, HGG.sectionsEquiv U
      (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (𝟙 (F.over U)))) =
        𝟙 (G.over U))
    (hα_comp : ∀ (U : Opens X) (f g : F.over U ⟶ F.over U),
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (f ≫ g))) =
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm f)) ≫
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm g)))
    (U : Opens X) {I K : Type u} [Finite I] [Finite K]
    (eF : SheafOfModules.free I ≅ F.over U)
    (eG : SheafOfModules.free K ≅ G.over U)
    (T : F.val.obj (op U) ≃ₗ[Rc.obj.obj (op U)] G.val.obj (op U))
    (hT : sheafEndSectionAlgEquiv HFF HGG α hα_one hα_comp U eF eG =
      T.conjAlgEquiv (Rc.obj.obj (op U))) :
    ∃ t : (sheafIntertwiner HFF HGG HFG α.hom).toSheafOfModules.val.obj (op U),
      IsIso (HFG.sectionsEquiv U t.1) := by
  obtain ⟨t, ht⟩ := (sheafHomApp_bijective_of_free HFG eF).surjective T.toLinearMap
  have ht' : sheafHomSectionLinearMap HFG U t = T.toLinearMap := ht
  refine ⟨⟨t, sheafHom_intertwines_of_conjugator HFF HGG HFG α hα_one hα_comp U eF eG t T
    ht' hT⟩, isIso_of_bijective_on_sections U eF eG _ ?_⟩
  change Function.Bijective (sheafHomSectionLinearMap HFG U t)
  rw [ht']
  exact T.bijective
end

section
/-- A finite locally free sheaf of modules is trivialized by a free sheaf on a finite type on a
neighbourhood of every point. -/
private lemma exists_freeIso_neighborhood
    {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
    (F : SheafOfModules.{u} R)
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
    (x : X) : ∃ (U : Opens X) (I : Type u) (_ : Finite I),
      Nonempty (SheafOfModules.free I ≅ F.over U) ∧ x ∈ U := by
  obtain ⟨q, hq, hfin⟩ := hF.exists_isFiniteLocallyFreeData
  let := hq
  let := hfin
  have hcover := q.coversTop
  rw [Opens.coversTop_iff] at hcover
  have hx : x ∈ iSup q.X := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have hiso : IsIso (q.generators i).π := hq.isIso i
  exact ⟨q.X i, (q.generators i).I, (hfin.isFiniteType i).finite, ⟨asIso (q.generators i).π⟩, hi⟩
end

section
/-- A finite locally free sheaf of modules whose local bases are nonempty is trivialized by a free
sheaf on a nonempty finite type on a neighbourhood of every point, so that its modules of
sections are nontrivial there. -/
private lemma exists_positive_freeIso_neighborhood
    (S : Scheme.{u}) (F : SheafOfModules.{u} (structureSheaf S.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) F]
    (hF : ∃ q : SheafOfModules.LocalGeneratorsData F,
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (q.generators i).I)
    (x : S) : ∃ (U : Opens S) (I : Type u)
      (_ : Finite I) (_ : Nonempty I)
      (_ : SheafOfModules.free I ≅ F.over U), x ∈ U := by
  obtain ⟨U, I, hI, ⟨eI⟩, hxU⟩ := exists_freeIso_neighborhood F x
  obtain ⟨q, hq, hpos⟩ := hF
  let := hq
  have hc := q.coversTop
  rw [Opens.coversTop_iff] at hc
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (show x ∈ iSup q.X by rw [hc]; trivial)
  let V := q.X i
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxi⟩
  let : Finite I := hI
  let : Nonempty (q.generators i).I := hpos i
  let eIW := restrictFreeIso eI (inf_le_left : W ≤ U)
  let eJW := restrictFreeIso (asIso (q.generators i).π) (inf_le_right : W ≤ V)
  let : Nonempty W := ⟨⟨x, hxW⟩⟩
  let : Nontrivial (S.presheaf.obj (op W)) :=
    @AlgebraicGeometry.LocallyRingedSpace.component_nontrivial
      S.toLocallyRingedSpace W ⟨⟨x, hxW⟩⟩
  let : Nontrivial ((S.sheaf.over W).obj.obj (op (Over.mk (𝟙 W)))) :=
    @AlgebraicGeometry.LocallyRingedSpace.component_nontrivial
      S.toLocallyRingedSpace W ⟨⟨x, hxW⟩⟩
  let iJ := Classical.choice (hpos i)
  let unitW := SheafOfModules.unit ((structureSheaf S.sheaf).over W)
  let sW : unitW.sections := unitW.unitHomEquiv (𝟙 unitW)
  let p : SheafOfModules.free (q.generators i).I ⟶ unitW :=
    unitW.freeHomEquiv.symm (fun _ => sW)
  let W₀ := op (Over.mk (𝟙 W))
  let y := (SheafOfModules.freeSection (R := (structureSheaf S.sheaf).over W) iJ).eval W₀
  have hp : (p.val.app W₀).hom y = (1 : S.presheaf.obj (op W)) := by
    have h : (p.val.app W₀).hom y = sW.eval W₀ :=
      congrArg (fun s : unitW.sections => s.eval W₀)
        (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection (fun _ => sW) iJ)
    rw [h]
    simp [sW, unitW]
    rfl
  have hy : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    change (0 : S.presheaf.obj (op W)) = 1 at hp
    exact one_ne_zero hp.symm
  let eJW₀ := ((PresheafOfModules.evaluation _ W₀).mapIso
    ((SheafOfModules.forget _).mapIso eJW)).toLinearEquiv
  have hby : eJW₀ y ≠ 0 := fun h =>
    hy (eJW₀.injective (h.trans (map_zero eJW₀).symm))
  let bI := sectionBasisOfIso (S.sheaf.over W) I
    (op (Over.mk (𝟙 W))) eIW
  let : Nontrivial ((F.over W).val.obj (op (Over.mk (𝟙 W)))) :=
    nontrivial_of_ne (eJW₀ y) 0 hby
  exact ⟨W, I, hI, bI.index_nonempty, eIW, hxW⟩
end

/-- Near every point there is an open set on which `F` is free of positive finite rank and the
intertwiner sheaf has a section inducing an isomorphism `F|_U ≅ G|_U`. This is the local step of
Tag 0A2K: the conjugator is produced by the local linear algebra over the ring of sections, after
shrinking so that the chosen rank-one coefficient becomes a unit. -/
private lemma exists_isIso_intertwinerSection_neighborhood
    (S : Scheme.{u})
    (F G : SheafOfModules.{u} (structureSheaf S.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) G]
    (hF : ∃ q : SheafOfModules.LocalGeneratorsData F,
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (q.generators i).I)
    (hG : ∃ q : SheafOfModules.LocalGeneratorsData G,
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (q.generators i).I)
    (HFF : SheafHom S.sheaf F F) (HGG : SheafHom S.sheaf G G)
    (α : HFF.obj ≅ HGG.obj)
    (hα_one : ∀ U : Opens S, HGG.sectionsEquiv U
      (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (𝟙 (F.over U)))) =
        𝟙 (G.over U))
    (hα_comp : ∀ (U : Opens S) (f g : F.over U ⟶ F.over U),
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (f ≫ g))) =
      (HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm f))) ≫
      (HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm g))))
    (x : S.toLocallyRingedSpace.toRingedSpace) :
    ∃ (U : Opens S) (I : Type u) (_ : Finite I) (_ : Nonempty I)
      (_ : SheafOfModules.free I ≅ F.over U)
      (t : (sheafIntertwiner HFF HGG (internalSheafHom S F G) α.hom).toSheafOfModules.val.obj
        (op U)),
      x ∈ U ∧ IsIso ((internalSheafHom S F G).sectionsEquiv U t.1) := by
  obtain ⟨U₀, I, hI, hIpos, eF₀, hxU₀⟩ :=
    exists_positive_freeIso_neighborhood S F hF x
  obtain ⟨V₀, K, hK, hKpos, eG₀, hxV₀⟩ :=
    exists_positive_freeIso_neighborhood S G hG x
  let W := U₀ ⊓ V₀
  have hxW : x ∈ W := ⟨hxU₀, hxV₀⟩
  let eFW := restrictFreeIso eF₀ (inf_le_left : W ≤ U₀)
  let eGW := restrictFreeIso eG₀ (inf_le_right : W ≤ V₀)
  let a := sheafEndSectionAlgEquiv HFF HGG α hα_one hα_comp W eFW eGW
  let basis {J : Type u} [Finite J] {M : SheafOfModules.{u} (structureSheaf S.sheaf)} {W : Opens S}
      (e : SheafOfModules.free J ≅ M.over W) :
      Module.Basis J (S.sheaf.obj.obj (op W)) (M.val.obj (op W)) :=
    sectionBasisOfIso (S.sheaf.over W) J (op (Over.mk (𝟙 W))) e
  let bF' := basis eFW
  let bG' := basis eGW
  let i₀ := Classical.choice hIpos
  let pW : Module.End (S.sheaf.obj.obj (op W)) (F.val.obj (op W)) :=
    LinearMap.smulRight (bF'.coord i₀) (bF' i₀)
  obtain ⟨j, k, hjk⟩ := exists_isUnit_coord_smulRight_coord bF' bG' a
    (S.presheaf.germ W x hxW).hom i₀
  let c := bG'.coord j (a pW (bG' k))
  obtain ⟨V, iVW, hxV, hcV⟩ :=
    S.toLocallyRingedSpace.toRingedSpace.isUnit_res_of_isUnit_germ W c x hxW hjk
  have hVW : V ≤ W := leOfHom iVW
  let eFV := restrictFreeIso eFW hVW
  let eGV := restrictFreeIso eGW hVW
  let bFV := basis eFV
  let bGV := basis eGV
  let aV := sheafEndSectionAlgEquiv HFF HGG α hα_one hα_comp V eFV eGV
  let pV : Module.End (S.sheaf.obj.obj (op V)) (F.val.obj (op V)) :=
    LinearMap.smulRight (bFV.coord i₀) (bFV i₀)
  obtain ⟨sW, hsW⟩ := (sheafHomApp_bijective_of_free HFF eFW).surjective pW
  have hsW' : sheafHomSectionLinearMap HFF W sW = pW := hsW
  have hsV : sheafHomSectionLinearMap HFF V (HFF.obj.val.map (homOfLE hVW).op sW) = pV :=
    sheafHomSectionLinearMap_restrict_rankOne HFF hVW eFW i₀ sW hsW'
  have hcoef : bGV.coord j (aV pV (bGV k)) =
      (S.sheaf.obj.map (homOfLE hVW).op).hom (bG'.coord j (a pW (bG' k))) := by
    rw [← hsV, ← hsW']
    exact sheafEndSectionAlgEquiv_coord_restrict HFF HGG α hα_one hα_comp hVW eFW eGW sW j k
  have hc : IsUnit (bGV.coord j (aV pV (bGV k))) := by
    rw [hcoef]
    obtain rfl : (homOfLE hVW : V ⟶ W) = iVW := Subsingleton.elim _ _
    change IsUnit ((S.sheaf.obj.map (homOfLE hVW).op).hom c) at hcV
    exact hcV
  obtain ⟨T, hT⟩ := exists_linearEquiv_conjAlgEquiv_of_isUnit_coord bFV bGV aV
    i₀ j k hc
  obtain ⟨tL, htIso⟩ := exists_isIso_intertwinerSection_of_conjAlgEquiv HFF HGG
    (internalSheafHom S F G) α hα_one hα_comp V eFV eGV T hT
  exact ⟨V, I, hI, hIpos, eFV, tL, hxV, htIso⟩

/-- The content of Tag 0A2K: the intertwiner sheaf of a given isomorphism of endomorphism sheaves
is invertible and evaluation identifies `F` tensored with it with `G`, compatibly with the given
isomorphism. -/
private theorem exists_invertible_tensor_iso_of_endomorphism_algebra_iso_aux
    (S : Scheme.{u})
    (F G : SheafOfModules.{u} (structureSheaf S.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) G]
    (hF : ∃ q : SheafOfModules.LocalGeneratorsData F,
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (q.generators i).I)
    (hG : ∃ q : SheafOfModules.LocalGeneratorsData G,
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (q.generators i).I)
    (HFF : SheafHom S.sheaf F F) (HGG : SheafHom S.sheaf G G)
    (α : HFF.obj ≅ HGG.obj)
    (hα_one : ∀ U : Opens S, HGG.sectionsEquiv U
      (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (𝟙 (F.over U)))) =
        𝟙 (G.over U))
    (hα_comp : ∀ (U : Opens S) (f g : F.over U ⟶ F.over U),
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (f ≫ g))) =
      (HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm f))) ≫
      (HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm g)))) :
    ∃ L : SheafOfModules.{u} (structureSheaf S.sheaf),
      Stacks.SheafOfModules.IsInvertible S.sheaf.obj (structureSheaf S.sheaf).property L ∧
      ∃ e : (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((S.toLocallyRingedSpace.toRingedSpace)).presheaf,
            ((S.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj (L)) ≅ G,
        ∀ (U : Opens S) (s : HFF.obj.val.obj (op U))
          (f : F.val.obj (op U)) (l : L.val.obj (op U)),
          ((HGG.sectionsEquiv U (α.hom.val.app (op U) s)).val.app
            (op (Over.mk (𝟙 U)))).hom
              ((e.hom.val.app (op U)).hom
                (toTensorSheafSection S.toLocallyRingedSpace.toRingedSpace F L (op U)
                  (f ⊗ₜ[(O S.toLocallyRingedSpace.toRingedSpace).obj (op U)] l))) =
            (e.hom.val.app (op U)).hom
              (toTensorSheafSection S.toLocallyRingedSpace.toRingedSpace F L (op U)
                ((((HFF.sectionsEquiv U s).val.app (op (Over.mk (𝟙 U)))).hom f) ⊗ₜ[
                  (O S.toLocallyRingedSpace.toRingedSpace).obj (op U)] l)) := by
  let X := S.toLocallyRingedSpace.toRingedSpace
  let HFG := internalSheafHom S F G
  let N := sheafIntertwiner HFF HGG HFG α.hom
  let L := N.toSheafOfModules
  have hlocal : ∀ x : X, ∃ (U : Opens X) (t : L.val.obj (op U)), x ∈ U ∧
      (∀ (V : Opens X) (hVU : V ≤ U), Function.Bijective
        (fun r : X.presheaf.obj (op V) => r • L.val.map (homOfLE hVU).op t)) ∧
      (∀ (V : Opens X) (hVU : V ≤ U), Function.Bijective
        (sheafHomApp HFG U V hVU (N.ι.val.app (op U) t))) := by
    intro x
    obtain ⟨U, I, hI, hIne, eF, t, hxU, ht⟩ :=
      exists_isIso_intertwinerSection_neighborhood S F G hF hG HFF HGG α hα_one hα_comp x
    let := hI
    let := hIne
    let := ht
    exact ⟨U, t, hxU, sheafIntertwiner_basis_of_isIso HFF HGG HFG α.hom U eF t⟩
  have hL := isInvertible_of_locally_basis X L fun x => by
    obtain ⟨U, t, hxU, hb, _⟩ := hlocal x
    exact ⟨U, t, hxU, hb⟩
  have := sheafHomEvaluation_isIso_of_locally_basis X HFG N.ι hlocal
  exact ⟨L, hL, asIso (sheafHomEvaluation X HFG N.ι),
    fun U s f l => sheafIntertwiner_evaluation_commutes X HFF HGG HFG α.hom U s f l⟩

/-- An isomorphism of the endomorphism algebra sheaves of two positive-rank vector
bundles is conjugation by an isomorphism after an invertible twist. -/
@[stacks 0A2K]
public theorem exists_invertible_tensor_iso_of_endomorphism_algebra_iso
    (S : Scheme.{u})
    (F G : SheafOfModules.{u} (structureSheaf S.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) G]
    (hF : ∃ q : SheafOfModules.LocalGeneratorsData F,
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (q.generators i).I)
    (hG : ∃ q : SheafOfModules.LocalGeneratorsData G,
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (q.generators i).I)
    (HFF : SheafHom S.sheaf F F) (HGG : SheafHom S.sheaf G G)
    (α : HFF.obj ≅ HGG.obj)
    (hα_one : ∀ U : Opens S, HGG.sectionsEquiv U
      (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (𝟙 (F.over U)))) =
        𝟙 (G.over U))
    (hα_comp : ∀ (U : Opens S) (f g : F.over U ⟶ F.over U),
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (f ≫ g))) =
      (HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm f))) ≫
      (HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm g)))) :
    ∃ L : SheafOfModules.{u} (structureSheaf S.sheaf),
      Stacks.SheafOfModules.IsInvertible S.sheaf.obj (structureSheaf S.sheaf).property L ∧
      ∃ e : (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((S.toLocallyRingedSpace.toRingedSpace)).presheaf,
            ((S.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj (L)) ≅ G,
        ∀ (U : Opens S) (s : HFF.obj.val.obj (op U))
          (f : F.val.obj (op U)) (l : L.val.obj (op U)),
          ((HGG.sectionsEquiv U (α.hom.val.app (op U) s)).val.app
            (op (Over.mk (𝟙 U)))).hom
              ((e.hom.val.app (op U)).hom
                (toTensorSheafSection S.toLocallyRingedSpace.toRingedSpace F L (op U)
                  (f ⊗ₜ[(O S.toLocallyRingedSpace.toRingedSpace).obj (op U)] l))) =
            (e.hom.val.app (op U)).hom
              (toTensorSheafSection S.toLocallyRingedSpace.toRingedSpace F L (op U)
                ((((HFF.sectionsEquiv U s).val.app (op (Over.mk (𝟙 U)))).hom f) ⊗ₜ[
                  (O S.toLocallyRingedSpace.toRingedSpace).obj (op U)] l)) :=
  exists_invertible_tensor_iso_of_endomorphism_algebra_iso_aux
    S F G hF hG HFF HGG α hα_one hα_comp


/-- After an algebra isomorphism of endomorphism algebras, some matrix coefficient of the image of
a rank-one projection is a unit in a local ring receiving the base ring. Otherwise every
coefficient lies in the maximal ideal and the image vanishes modulo it. -/
private alias exists_isUnit_rankOne_coefficient := exists_isUnit_coord_smulRight_coord

/-- An algebra isomorphism of endomorphism algebras of modules with bases is conjugation by a
linear equivalence as soon as one matrix coefficient of the image of a rank-one projection is a
unit. -/
private alias algEquiv_eq_conjugate_of_unit_coefficient :=
  exists_linearEquiv_conjAlgEquiv_of_isUnit_coord

end Stacks.EtaleCohomology
