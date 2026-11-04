module

public import StacksFrontier.Cotangent.SheavesOfRings.ThickeningLiftCorrespondence
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationSolution
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionSourceIdealGluing
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.InverseImageSquareSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.CohomologyOfClosedMap

/-!
# Sections of an inverse image, and the inverse image of a thickening

Local computations with the sections `Stacks.Topology.ambientSection` of an inverse image sheaf:
every section is locally induced by a section of the sheaf, two induced sections agree near a
point only if the inducing sections agree near its image, and the reduction
`Scheme.liftSourceReduction j f : f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y` and the structure maps of inverse-image
ringed spaces act on induced sections through the comorphisms.

## Main results

* `Stacks.Topology.exists_res_eq_ambientSection`: a section of `f⁻¹F` is, near each point,
  induced by a section of `F`.
* `Stacks.Topology.exists_map_eq_of_ambientSection_eq`: induced sections which agree near a point
  come from sections agreeing near its image.
* `AlgebraicGeometry.Scheme.liftSourceReduction_ambientSection`: the reduction of an induced
  section is induced by the comorphism of `j`.
* `AlgebraicGeometry.ringedSpaceStructureMap_ambientSection`: the structure map of an
  inverse-image ringed space is the comorphism on induced sections.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace TopCat

universe u

namespace Stacks.Topology

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- **A section of an inverse image is locally induced by a section of the sheaf.** -/
theorem exists_res_eq_ambientSection (F : Y.Sheaf CommRingCat.{u}) {U : Opens X}
    (σ : ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.obj (op U)) (x : X)
    (hx : x ∈ U) :
    ∃ (W : Opens Y) (V : Opens X) (hV : V ≤ U) (hVW : V ≤ (Opens.map f).obj W), x ∈ V ∧
      ∃ t : F.presheaf.obj (op W),
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.map (homOfLE hV).op σ =
          ambientSection f F hVW t := by
  obtain ⟨W, hW, t, ht⟩ := exists_ambientSection_germ f F x
    (((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.germ U x hx σ)
  have hx0 : x ∈ U ⊓ (Opens.map f).obj W := ⟨hx, hW⟩
  have hg := germ_ambientSection f F (inf_le_right : U ⊓ (Opens.map f).obj W ≤ _) x hx0 t
  rw [ht, ← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left :
    U ⊓ (Opens.map f).obj W ≤ U)) x hx0] at hg
  obtain ⟨V, hxV, i₁, i₂, he⟩ := TopCat.Presheaf.germ_eq _ x hx0 hx0 _ _ hg
  refine ⟨W, V, (leOfHom i₂).trans inf_le_left, (leOfHom i₂).trans inf_le_right, hxV, t, ?_⟩
  have h₁ : ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.map
      (homOfLE ((leOfHom i₂).trans inf_le_left)).op σ =
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.map i₂.op
        (((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.map
          (homOfLE inf_le_left).op σ) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [h₁, ← he, ← CommRingCat.comp_apply]
  exact ConcreteCategory.congr_hom (ambientSection_comp_restrict f F inf_le_right (leOfHom i₁)) t

/-- Restricting an induced section to a smaller open gives the induced section there. -/
theorem ambientSection_res_apply (F : Y.Sheaf CommRingCat.{u}) {W : Opens Y} {V V' : Opens X}
    (h' : V' ≤ (Opens.map f).obj W) (hVV' : V ≤ V') (t : F.presheaf.obj (op W)) :
    (((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.map (homOfLE hVV').op).hom
        (ambientSection f F h' t) = ambientSection f F (hVV'.trans h') t :=
  (CommRingCat.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom (ambientSection_comp_restrict f F h' hVV') t)

/-- Restricting the inducing section to a smaller open does not change the induced section. -/
theorem ambientSection_map_apply' (F : Y.Sheaf CommRingCat.{u}) {W W' : Opens Y} {V : Opens X}
    (hW : W' ≤ W) (h : V ≤ (Opens.map f).obj W') (t : F.presheaf.obj (op W)) :
    ambientSection f F h ((F.presheaf.map (homOfLE hW).op).hom t) =
      ambientSection f F (h.trans ((Opens.map f).monotone hW)) t :=
  ambientSection_map_apply f F (homOfLE hW) h _ t

/-- **Induced sections which agree near a point come from sections agreeing near its image.** -/
theorem exists_map_eq_of_ambientSection_eq (F : Y.Sheaf CommRingCat.{u}) {W : Opens Y}
    {V : Opens X} (h : V ≤ (Opens.map f).obj W) (t₁ t₂ : F.presheaf.obj (op W))
    (he : ambientSection f F h t₁ = ambientSection f F h t₂) (x : X) (hx : x ∈ V) :
    ∃ (W' : Opens Y) (hW' : W' ≤ W), f x ∈ W' ∧
      F.presheaf.map (homOfLE hW').op t₁ = F.presheaf.map (homOfLE hW').op t₂ := by
  have h₁ := germ_ambientSection f F h x hx t₁
  have h₂ := germ_ambientSection f F h x hx t₂
  rw [he] at h₁
  obtain ⟨W', hxW', i₁, i₂, he'⟩ := TopCat.Presheaf.germ_eq _ (f x) (h hx) (h hx) _ _
    (ambientStalkHom_injective f F x (h₁.symm.trans h₂))
  exact ⟨W', leOfHom i₁, hxW', he'⟩

end Stacks.Topology

namespace AlgebraicGeometry

open RingedSpace Stacks.Topology
open Stacks.SheafOfModules (ringedSpaceStructureMap)
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction structureSheafMap)

/-- An induced section on a smaller open is the restriction of the induced section on the whole
inverse image. -/
theorem ambientSection_eq_unit_comp {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Y.Sheaf CommRingCat.{u})
    {W : Opens Y} {V : Opens X} (hV : V ≤ (Opens.map f).obj W) :
    ambientSection f F hV =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app F).hom.app
          (op W) ≫
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.map (homOfLE hV).op := by
  rw [← ambientSection_eq_unit]
  exact (ambientSection_comp_restrict f F (le_refl _) hV).symm

/-- **The structure map of an inverse-image ringed space on induced sections** is the comorphism:
`h^♯ : h⁻¹𝒪_T ⟶ 𝒪_S` takes the section induced by `t` on `V ⊆ h⁻¹W` to `h^♯(t)|_V`. -/
theorem ambientSection_comp_ringedSpaceStructureMap {S T : RingedSpace.{u, u}} (h : S ⟶ T)
    {W : Opens T.carrier} {V : Opens S.carrier} (hV : V ≤ (Opens.map h.hom.base).obj W) :
    ambientSection h.hom.base T.sheaf hV ≫ (ringedSpaceStructureMap h).hom.app (op V) =
      h.hom.c.app (op W) ≫ S.presheaf.map (homOfLE hV).op := by
  rw [ambientSection_eq_unit_comp]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((ringedSpaceStructureMap h).hom.naturality (homOfLE hV).op)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (congrArg (fun φ => φ.hom.app (op W))
    (Stacks.SheafOfModules.unit_comp_map_ringedSpaceStructureMap h))

/-- The structure map `h^♯ : h⁻¹𝒪_T ⟶ 𝒪_S` sends the section induced by `t` on `V ⊆ h⁻¹W` to
`h^♯(t)|_V`. -/
theorem ringedSpaceStructureMap_ambientSection {S T : RingedSpace.{u, u}} (h : S ⟶ T)
    {W : Opens T.carrier} {V : Opens S.carrier} (hV : V ≤ (Opens.map h.hom.base).obj W)
    (t : T.presheaf.obj (op W)) :
    ((ringedSpaceStructureMap h).hom.app (op V)).hom (ambientSection h.hom.base T.sheaf hV t) =
      (S.presheaf.map (homOfLE hV).op).hom ((h.hom.c.app (op W)).hom t) :=
  ConcreteCategory.congr_hom (ambientSection_comp_ringedSpaceStructureMap h hV) t

namespace Scheme

variable {X Y Y' : Scheme.{u}} (j : Y ⟶ Y') (f : X ⟶ Y)

/-- The unit of `(f ≫ j)⁻¹ ⊣ (f ≫ j)_*` followed by the reduction of the source is the
comorphism of `j` followed by the unit of `f⁻¹ ⊣ f_*`. -/
theorem unit_comp_map_liftSourceReduction :
    (sheafAdjunction (f.toLRSHom.toShHom ≫ j.toLRSHom.toShHom)).unit.app Y'.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.toLRSHom.toShHom.hom.base ⋙
          TopCat.Sheaf.pushforward CommRingCat.{u} j.toLRSHom.toShHom.hom.base).map
          (liftSourceReduction j f) =
      structureSheafMap j.toLRSHom.toShHom ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} j.toLRSHom.toShHom.hom.base).map
          ((sheafAdjunction f.toLRSHom.toShHom).unit.app Y.sheaf) := by
  let L := (sheafAdjunction j.toLRSHom.toShHom).comp (sheafAdjunction f.toLRSHom.toShHom)
  let R := TopCat.Sheaf.pushforward CommRingCat.{u} f.toLRSHom.toShHom.hom.base ⋙
    TopCat.Sheaf.pushforward CommRingCat.{u} j.toLRSHom.toShHom.hom.base
  have h1 : L.unit.app Y'.sheaf ≫ R.map
      (Stacks.SheafOfModules.inverseImageCompIso f.toLRSHom.toShHom j.toLRSHom.toShHom).inv =
      (sheafAdjunction (f.toLRSHom.toShHom ≫ j.toLRSHom.toShHom)).unit.app Y'.sheaf :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ Y'.sheaf
  have h2 : (sheafAdjunction (f.toLRSHom.toShHom ≫ j.toLRSHom.toShHom)).unit.app Y'.sheaf ≫
      R.map (Stacks.SheafOfModules.inverseImageCompIso f.toLRSHom.toShHom j.toLRSHom.toShHom).hom =
      L.unit.app Y'.sheaf := by
    refine (congrArg (· ≫ R.map _) h1.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (L.unit.app Y'.sheaf ≫ ·) ((R.map_comp _ _).symm.trans
      ((congrArg R.map (Iso.inv_hom_id _)).trans (R.map_id _)))).trans ?_
    exact Category.comp_id _
  have h3 : R.map (liftSourceReduction j f) =
      R.map (Stacks.SheafOfModules.inverseImageCompIso f.toLRSHom.toShHom j.toLRSHom.toShHom).hom ≫
        R.map (Stacks.SheafOfModules.inverseImageFirstRingMap f.toLRSHom.toShHom
          j.toLRSHom.toShHom) :=
    R.map_comp _ _
  let Rj := TopCat.Sheaf.pushforward CommRingCat.{u} j.toLRSHom.toShHom.hom.base
  have h4 : Rj.map ((sheafAdjunction f.toLRSHom.toShHom).unit.app
        ((TopCat.Sheaf.pullback CommRingCat.{u} j.toLRSHom.toShHom.hom.base).obj Y'.sheaf)) ≫
      R.map (Stacks.SheafOfModules.inverseImageFirstRingMap f.toLRSHom.toShHom
        j.toLRSHom.toShHom) =
      Rj.map (ringedSpaceStructureMap j.toLRSHom.toShHom) ≫
        Rj.map ((sheafAdjunction f.toLRSHom.toShHom).unit.app Y.sheaf) := by
    refine (Rj.map_comp _ _).symm.trans ?_
    refine (congrArg Rj.map ((sheafAdjunction f.toLRSHom.toShHom).unit_naturality
      (ringedSpaceStructureMap j.toLRSHom.toShHom))).trans ?_
    exact Rj.map_comp _ _
  refine (congrArg (_ ≫ ·) h3).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h2).trans ?_
  refine (congrArg (· ≫ _) (Adjunction.comp_unit_app _ _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) h4).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _)
    (Stacks.SheafOfModules.unit_comp_map_ringedSpaceStructureMap j.toLRSHom.toShHom)

/-- The reduction of the source `(f ≫ j)⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y`, precomposed with the induced-section
map from `𝒪_{Y'}(W)`, is the comorphism `j^♯` on `W` followed by the induced-section map from
`𝒪_Y(j⁻¹W)`. -/
theorem ambientSection_comp_liftSourceReduction {W : _root_.TopologicalSpace.Opens Y'.carrier}
    {V : _root_.TopologicalSpace.Opens X.carrier}
    (hV : V ≤ (_root_.TopologicalSpace.Opens.map (f ≫ j).toLRSHom.toShHom.hom.base).obj W) :
    ambientSection (f ≫ j).toLRSHom.toShHom.hom.base Y'.sheaf hV ≫
        (liftSourceReduction j f).hom.app (op V) =
      j.toLRSHom.toShHom.hom.c.app (op W) ≫
        ambientSection f.toLRSHom.toShHom.hom.base Y.sheaf hV := by
  rw [ambientSection_eq_unit_comp]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((liftSourceReduction j f).hom.naturality (homOfLE hV).op)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (congrArg (fun φ => φ.hom.app (op W))
    (unit_comp_map_liftSourceReduction j f))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) (ambientSection_eq_unit_comp f.toLRSHom.toShHom.hom.base Y.sheaf hV).symm

/-- **The reduction of the source on induced sections**: `f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y` takes the section
induced by `t` to the section induced by `j^♯(t)`. -/
theorem liftSourceReduction_ambientSection {W : _root_.TopologicalSpace.Opens Y'.carrier}
    {V : _root_.TopologicalSpace.Opens X.carrier}
    (hV : V ≤ (_root_.TopologicalSpace.Opens.map (f ≫ j).toLRSHom.toShHom.hom.base).obj W)
    (t : Y'.presheaf.obj (op W)) :
    ((liftSourceReduction j f).hom.app (op V)).hom
        (ambientSection (f ≫ j).toLRSHom.toShHom.hom.base Y'.sheaf hV t) =
      ambientSection f.toLRSHom.toShHom.hom.base Y.sheaf hV
        ((j.toLRSHom.toShHom.hom.c.app (op W)).hom t) :=
  ConcreteCategory.congr_hom (ambientSection_comp_liftSourceReduction j f hV) t

end Scheme

end AlgebraicGeometry

end
