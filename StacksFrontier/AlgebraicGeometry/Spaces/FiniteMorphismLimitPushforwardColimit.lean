module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitSystem

/-!
# A finite morphism as a limit of finite ones, with the direct images as a colimit

Let `π : Y ⟶ X` be a finite morphism of algebraic spaces over `S`, with `X` quasi-compact and
quasi-separated.  Then `Y` is a directed limit `Y = lim Y_i` of algebraic spaces
`π_i : Y_i ⟶ X`, finite and of finite presentation over `X`, along closed immersions
(Stacks 07VR).  The system may be chosen as `Y_i = \underline{Spec}_X(𝒜_i)` for a directed
system of finite `𝒪_X`-algebras of finite presentation `𝒜_i` with surjective transition maps
and colimit `π_* 𝒪_Y` (Stacks 086Z, Stacks 081V), so that `π_* 𝒪_Y = colim π_{i,*} 𝒪_{Y_i}`;
the morphisms `Y ⟶ Y_i` are then closed immersions.

## Main results

* `AlgebraicGeometry.Space.exists_affineOver_limit_pushforwardColimit_of_isFinite`: the limit
  presentation of a finite morphism to a quasi-compact quasi-separated space, read in the
  category of spaces affine over the target, with its closed immersions, and with the direct
  images of the structure sheaves forming a colimit with locally surjective transition maps.

## References

* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every projection of a limit cone over a cofiltered diagram of monomorphisms is a
monomorphism. -/
private theorem mono_π_of_isLimit_of_mono {C : Type*} [Category C] {J : Type*}
    [Category J] [IsCofiltered J] {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (hF : ∀ {i j : J} (g : i ⟶ j), Mono (F.map g)) (i : J) : Mono (c.π.app i) := by
  refine ⟨fun {T} a b hab => hc.hom_ext fun j => ?_⟩
  have := hF (IsCofiltered.minToLeft i j)
  have hk : a ≫ c.π.app (IsCofiltered.min i j) = b ≫ c.π.app (IsCofiltered.min i j) := by
    rw [← cancel_mono (F.map (IsCofiltered.minToLeft i j)), Category.assoc, Category.assoc,
      c.w, hab]
  rw [← c.w (IsCofiltered.minToRight i j), ← Category.assoc, hk, Category.assoc]

/-- Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over `S` with `Y` quasi-compact and
quasi-separated.  There is a directed preorder `I` and an inverse system `DA` of spaces
affine over `Y` indexed by `Iᵒᵖ`, with a cone `ι` from `X`, such that:

* the cone is a limit both in the spaces over `Y` and in presheaves, so `X = lim X_i`;
* every stage `X_i ⟶ Y` is finite and of finite presentation;
* the morphisms `X ⟶ X_i` and the transition morphisms are closed immersions;
* the direct images `f_{i,*} 𝒪_{X_i}`, with the maps to `f_* 𝒪_X` induced by the cone, form a
  colimit cocone of quasi-coherent `𝒪_Y`-algebras: `f_* 𝒪_X = colim f_{i,*} 𝒪_{X_i}`;
* every transition map `f_{j,*} 𝒪_{X_j} ⟶ f_{i,*} 𝒪_{X_i}` is locally surjective. -/
theorem exists_affineOver_limit_pushforwardColimit_of_isFinite
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hfin : IsFinite B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (DA : Iᵒᵖ ⥤ AffineOver B S hS ⟨Y, hY⟩)
      (ι : (Functor.const Iᵒᵖ).obj
        (⟨Over.mk (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) (X := ⟨X, hX⟩)
          (Y := ⟨Y, hY⟩) f), hfin.isAffineHom⟩ : AffineOver B S hS ⟨Y, hY⟩) ⟶ DA),
      Nonempty (IsLimit ((affineOverToOver B S hS ⟨Y, hY⟩).mapCone (Cone.mk _ ι))) ∧
      Nonempty (IsLimit
        ((affineOverToOver B S hS ⟨Y, hY⟩ ⋙ Over.forget Y).mapCone (Cone.mk _ ι))) ∧
      (∀ i, IsFinite B S hS (DA.obj i).obj.hom.hom ∧
        IsFinitePresentation B S hS (DA.obj i).obj.hom.hom) ∧
      (∀ i, IsClosedImmersion B S hS (ι.app i).hom.left.hom) ∧
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsClosedImmersion B S hS (DA.map g).hom.left.hom) ∧
      Nonempty (IsColimit ((quasicoherentPushforwardAlgebraFunctor B S hS ⟨Y, hY⟩).mapCocone
        (coconeRightOpOfCone (Cone.mk _ ι)))) ∧
      ∀ {i j : Iᵒᵖ} (g : i ⟶ j), Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y)
        ((quasicoherentPushforwardAlgebraFunctor B S hS ⟨Y, hY⟩).map
          (DA.map g).op).hom.right.hom := by
  classical
  set Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩ with hY'
  set X' : AlgebraicSpaces B S hS := ⟨X, hX⟩ with hX'
  set E := boundedAffineAlgebraAntiEquivalence B S hS with hE
  set Z : AffineOver B S hS Y' :=
    ⟨Over.mk (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) (X := X') (Y := Y') f),
      hfin.isAffineHom⟩ with hZ
  set Ab : BoundedQuasicoherentAlgebra B S hS Y' := (E.pushforward Y').obj (op Z) with hAb
  have hZfin : IsFinite B S hS Z.obj.hom.hom := hfin
  obtain ⟨I, hIpre, hIne, hIdir, D, φ, ⟨hcolim⟩, hDprops, hDsurj⟩ :=
    exists_directed_isFinite_isFinitePresentation_locallySurjective_of_isFinite B S hS Y'
      ((quasicoherentPushforwardAlgebraFunctor B S hS Y').obj (op Z)) hYqc hYqs
      (isFinite_pushforwardAlgebra_of_isFinite B S hS (ObjectProperty.homMk f : X' ⟶ Y') hfin)
  let _ : Preorder I := hIpre
  let _ : Nonempty I := hIne
  let _ : IsDirected I (· ≤ ·) := hIdir
  set incl := boundedQuasicoherentAlgebraInclusion B S hS Y' with hincl
  set Db : I ⥤ BoundedQuasicoherentAlgebra B S hS Y' :=
    boundedLift D (fun i => (hDprops i).1.isFiniteType) with hDb
  set cb : Cocone Db := boundedCocone D (fun i => (hDprops i).1.isFiniteType) Ab φ with hcbdef
  have hcblim : IsColimit cb :=
    isColimitBoundedCocone D (fun i => (hDprops i).1.isFiniteType) Ab φ hcolim
  set EQ := E.equivalence Y' with hEQ
  set DA : Iᵒᵖ ⥤ AffineOver B S hS Y' := (Db ⋙ EQ.inverse).leftOp with hDA
  have hstageEq : ∀ i : I, DA.obj (op i) =
      E.relativeSpec (D.obj i)
        (AlgebraSheaf.sectionsBelowCutoff_of_isFiniteType B S hS _ (hDprops i).1.isFiniteType) :=
    fun _ => rfl
  set c0 : Cone DA := coneLeftOpOfCocone (EQ.inverse.mapCocone cb) with hc0
  have hlim0 : IsLimit c0 := isLimitConeLeftOpOfCocone _ (isColimitOfPreserves EQ.inverse hcblim)
  set eA := (E.pushforwardIso Y').app (op Z) with heA
  set eZ : Z ≅ c0.pt := ((EQ.unitIso.app (op Z)) ≪≫ EQ.inverse.mapIso eA).unop.symm with heZ
  set cu : Cone DA := c0.extend eZ.hom with hcu
  have hculim : IsLimit cu :=
    IsLimit.ofIsoLimit hlim0 (Cone.ext eZ.symm (fun j => by
      change c0.π.app j = eZ.inv ≫ eZ.hom ≫ c0.π.app j
      rw [← Category.assoc, eZ.inv_hom_id, Category.id_comp]))
  have hDAfin : ∀ i : Iᵒᵖ, IsFinite B S hS (DA.obj i).obj.hom.hom := by
    rintro ⟨i⟩
    rw [hstageEq i]
    exact isFinite_affineOver_of_isFinite_pushforwardAlgebra B S hS _
      (AlgebraSheaf.IsFinite.of_iso (E.relativeSpecPushforwardIso (D.obj i) _).symm
        (hDprops i).1)
  have hDAfp : ∀ i : Iᵒᵖ, IsFinitePresentation B S hS (DA.obj i).obj.hom.hom := by
    rintro ⟨i⟩
    rw [hstageEq i]
    exact isFinitePresentation_affineOver_of_isFinitePresentation_pushforwardAlgebra B S hS _
      (AlgebraSheaf.IsFinitePresentation.of_iso
        (E.relativeSpecPushforwardIso (D.obj i) _).symm (hDprops i).2)
  have hsurj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), Presheaf.IsLocallySurjective
      (SmallEtale.topology B S hS Y) (D.map g.unop).hom.right.hom := by
    rintro ⟨i⟩ ⟨j⟩ g
    rw [← homOfLE_leOfHom g.unop]
    exact hDsurj j i _
  have hDAmono : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), Mono (DA.map g) := by
    intro i j g
    have hepi : Epi (D.map g.unop) := by
      have hls : Sheaf.IsLocallySurjective (D.map g.unop).hom.right := hsurj g
      have hepi' : Epi (D.map g.unop).hom.right := inferInstance
      refine ⟨fun {Z} p r hpr => ?_⟩
      apply ObjectProperty.hom_ext
      apply AlgebraSheaf.Hom.ext
      exact (cancel_epi (D.map g.unop).hom.right).mp
        (congrArg (fun t => t.hom.right) hpr)
    have hepib : Epi (Db.map g.unop) := Functor.epi_of_epi_map incl hepi
    have hd : DA.map g = (EQ.inverse.map (Db.map g.unop)).unop := rfl
    rw [hd]
    have : Epi (EQ.inverse.map (Db.map g.unop)) := EQ.inverse.map_epi _
    infer_instance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  obtain ⟨⟨hpre⟩, hclosed⟩ :=
    nonempty_isLimit_affineOverToOver_of_mono DA cu hculim hZfin hDAfin hDAmono
  have hpsh : IsLimit ((affineOverToOver B S hS Y' ⋙ Over.forget Y).mapCone cu) :=
    isLimitOfPreserves (Over.forget Y'.obj) hpre
  have hleg : ∀ i : Iᵒᵖ, IsClosedImmersion B S hS (cu.π.app i).hom.left.hom := by
    intro i
    have hmono : Mono (((affineOverToOver B S hS Y' ⋙ Over.forget Y).mapCone cu).π.app i) :=
      mono_π_of_isLimit_of_mono hpsh (fun g => mono_of_isClosedImmersion B S hS _ (hclosed g)) i
    have hmono' : Mono (cu.π.app i).hom.left.hom := hmono
    have hfin_closed : IsFinite B S hS (cu.π.app i).hom.left.hom →
        IsClosedImmersion B S hS (cu.π.app i).hom.left.hom := by
      intro hf
      have hr := (isFinite_iff_representable B S hS _ hX (DA.obj i).obj.left.property).mp hf
      refine ⟨hr.1, ?_⟩
      intro U V g a p hp
      have : Mono (yoneda.map p) := PullbackCone.mono_snd_of_is_pullback_of_mono hp.isLimit
      have : Mono p := yoneda.mono_of_mono_map inferInstance
      have hfinp : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p) :=
        hr.2.property g a p hp
      have : Mono ((BigFppfOver.toScheme B S hS).map p) :=
        (BigFppfOver.toScheme B S hS).map_mono p
      exact (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono _).mpr
        ⟨hfinp, inferInstance⟩
    refine hfin_closed ?_
    refine isFinite_of_comp_of_isSeparated B S hS (cu.π.app i).hom.left.hom
      (DA.obj i).obj.hom.hom ?_ ?_
    · have h := congrArg (fun t => t.hom) (Over.w (cu.π.app i).hom)
      rw [ObjectProperty.FullSubcategory.comp_hom] at h
      change IsFinite B S hS ((cu.π.app i).hom.left.hom ≫ (DA.obj i).obj.hom.hom)
      rw [h]
      exact hZfin
    · exact isSeparated_of_isFinite B S hS (DA.obj i).obj.hom.hom
        (DA.obj i).obj.left.property hY (hDAfin i)
  set K : I ⥤ BoundedQuasicoherentAlgebra B S hS Y' := DA.rightOp ⋙ EQ.functor with hK
  set β : Db ≅ K := NatIso.ofComponents (fun i => (EQ.counitIso.app (Db.obj i)).symm)
    (fun {i j} g => EQ.counitIso.inv.naturality (Db.map g)) with hβ
  have hinclcb : IsColimit (incl.mapCocone cb) := hcolim
  have : PreservesColimit Db incl := preservesColimit_of_preserves_colimit_cocone hcblim hinclcb
  have : PreservesColimit K incl := preservesColimit_of_iso_diagram incl β
  have hcolimK : IsColimit (EQ.functor.mapCocone (coconeRightOpOfCone cu)) :=
    isColimitOfPreserves EQ.functor (isColimitCoconeRightOpOfCone DA hculim)
  refine ⟨I, hIpre, hIne, hIdir, DA, cu.π, ⟨hpre⟩, ⟨hpsh⟩, fun i => ⟨hDAfin i, hDAfp i⟩,
    hleg, fun g => hclosed g, ⟨isColimitOfPreserves incl hcolimK⟩, ?_⟩
  rintro ⟨i⟩ ⟨j⟩ g
  let Φ : BoundedQuasicoherentAlgebra B S hS Y' ⥤ ((SmallEtale B S hS Y)ᵒᵖ ⥤ CommRingCat.{u}) :=
    incl ⋙ quasicoherentAlgebraInclusion B S hS Y' ⋙
      AlgebraSheaf.forget (B := B) (S := S) (hS := hS) (F := Y) (hF := hY) ⋙
        sheafToPresheaf _ _
  have hnat : K.map g.unop = β.inv.app j ≫ Db.map g.unop ≫ β.hom.app i :=
    (NatIso.naturality_1 β g.unop).symm
  have hmap : ((quasicoherentPushforwardAlgebraFunctor B S hS Y').map (DA.map g).op).hom.right.hom =
      Φ.map (β.inv.app j) ≫ Φ.map (Db.map g.unop) ≫ Φ.map (β.hom.app i) := by
    rw [← Φ.map_comp, ← Φ.map_comp, ← hnat]
    rfl
  have hD : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y)
      (Φ.map (Db.map g.unop)) := hsurj g
  rw [hmap]
  have := Presheaf.isLocallySurjective_of_iso (SmallEtale.topology B S hS Y) (Φ.map (β.inv.app j))
  have := Presheaf.isLocallySurjective_of_iso (SmallEtale.topology B S hS Y) (Φ.map (β.hom.app i))
  have := Presheaf.isLocallySurjective_comp (SmallEtale.topology B S hS Y)
    (Φ.map (Db.map g.unop)) (Φ.map (β.hom.app i))
  exact Presheaf.isLocallySurjective_comp (SmallEtale.topology B S hS Y)
    (Φ.map (β.inv.app j)) (Φ.map (Db.map g.unop) ≫ Φ.map (β.hom.app i))

end AlgebraicGeometry.Space

end
