module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubspace
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubspaceExistence
public import StacksFrontier.AlgebraicGeometry.Crystalline.BasisCriteria
public import StacksFrontier.AlgebraicGeometry.Crystalline.ClosedFiberPullback
public import StacksFrontier.AlgebraicGeometry.Crystalline.SpecDividedPowerScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.ClosedFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.IdealSheafQuasicoherent
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Gluing divided power schemes along an open presentation

A divided power scheme is a scheme together with a quasi-coherent ideal sheaf and a divided
power structure on it.  This module builds such a scheme from local data: a
`Crystalline.DividedPowerScheme.DividedPowerOpenPresentation` is a locally directed open cover
of a scheme `X` by divided power schemes whose transition maps induce the ideal of the smaller
chart from that of the larger one, and the main construction glues it to a single divided power
scheme with underlying scheme `X`, exhibited as the colimit of the charts.

The ideal of the glued scheme is the kernel of the comparison with the glued closed fibres,
which is quasi-coherent because that comparison is a closed immersion.  The divided power
structure is produced from the charts: the images of the affine opens of the charts form a basis
of `X`, each carries the divided powers of its chart transported along the isomorphism on
sections, and these agree on overlaps because the presentation is locally directed.  The
universal property is then checked on that basis.

## Main definitions

* `Crystalline.DividedPowerScheme.IsInducedOpen` — a morphism of divided power schemes which is
  an open immersion and whose source ideal is induced from the target's.
* `Crystalline.DividedPowerScheme.dividedPowerSchemeForget` — the forgetful functor from
  divided power schemes to schemes.
* `Crystalline.DividedPowerScheme.zeroDividedPowerScheme` — a scheme read as a divided power
  scheme with zero ideal, and `Crystalline.DividedPowerScheme.closedFiberFunctor`, the closed
  fibre as a functor to schemes.
* `Crystalline.DividedPowerScheme.DividedPowerOpenPresentation` — a locally directed open
  presentation of a scheme by divided power schemes.
* `Crystalline.DividedPowerScheme.DividedPowerOpenPresentation.glued` — the divided power scheme
  glued from such a presentation, with `gluedι` the charts' inclusions and `gluedMap` the
  criterion that compatibility with divided powers may be checked chart by chart.

## Main results

* `Crystalline.DividedPowerScheme.DividedPowerOpenPresentation.ideal_isQuasicoherent` — the
  glued ideal is quasi-coherent.
* `Crystalline.DividedPowerScheme.DividedPowerOpenPresentation.gluedι_isInducedOpen` — each
  chart is an induced open of the glued scheme.
* `Crystalline.DividedPowerScheme.DividedPowerOpenPresentation.isColimit` — the glued scheme is
  the colimit of the presentation's charts in divided power schemes.

## Implementation notes

The declarations here are deliberately public: they were extracted from the construction of
fibre products of divided power schemes, where they were private, because gluing a divided power
scheme from local charts is needed on its own — in particular to build products of crystalline
thickenings.

The transparency declarations are kept `local`, as they were in the module this was extracted
from; an importer that needs a glued construction to unfold during unification restates them.

## References

* [Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)
* [Stacks Project, Tag 07H1](https://stacks.math.columbia.edu/tag/07H1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Opposite
open scoped AlgebraicGeometry

universe u v w

namespace Crystalline.DividedPowerScheme

attribute [local implicit_reducible] specDividedPowerScheme toSpecDividedPowerScheme
  specDividedPowerSchemeUnit specDividedPowerHomEquiv
attribute [local implicit_reducible] dividedPowersOfSeparatingFamily
attribute [local implicit_reducible] idealTypeSheaf
attribute [local implicit_reducible] globalSectionsDPMorphism

open Opposite TopologicalSpace in
/-- The kernel of a morphism of sheaves of modules as a subsheaf of its source. -/
public noncomputable def kernelSubmodule {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf} (f : M ⟶ N) : M.Submodule where
  obj U := (f.val.app U).hom.ker
  map {U V} r := by
    intro x hx
    change (f.val.app V) (M.val.map r x) = 0
    rw [PresheafOfModules.naturality_apply]
    change (f.val.app U) x = 0 at hx
    rw [hx, map_zero]
    rfl
  isSheaf {U} x hs := by
    change (f.val.app U) x = 0
    apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
    intro z hz
    obtain ⟨V, g, hg, hzV⟩ := hs z hz
    refine ⟨V, leOfHom g, hzV, ?_⟩
    change N.val.map g.op ((f.val.app U) x) = N.val.map g.op 0
    rw [map_zero, ← PresheafOfModules.naturality_apply]
    exact hg

attribute [local implicit_reducible] kernelSubmodule

/-- The explicit kernel subsheaf satisfies the categorical kernel property. -/
public noncomputable def kernelSubmoduleIsLimit {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf} (f : M ⟶ N) :
    IsLimit (KernelFork.ofι (f := f) (kernelSubmodule f).ι (by
      ext U x
      exact x.property)) := by
  let K := kernelSubmodule f
  have hw : K.ι ≫ f = 0 := by
    ext U x
    exact x.property
  let lift {P : SheafOfModules.{u} X.ringCatSheaf} (g : P ⟶ M) (hg : g ≫ f = 0) :
      P ⟶ K.toSheafOfModules :=
    { val :=
      { app := fun U => ModuleCat.ofHom ((g.val.app U).hom.codRestrict (K.obj U)
          (fun x => congrArg (fun k : P ⟶ N => (k.val.app U).hom x) hg))
        naturality := by
          intro U V r
          ext x
          exact Subtype.ext (PresheafOfModules.naturality_apply g.val r x) } }
  apply KernelFork.IsLimit.ofι K.ι hw lift
  · intro P g hg
    ext U x
    rfl
  · intro P g hg m hm
    apply (cancel_mono K.ι).mp
    exact hm.trans (show lift g hg ≫ K.ι = g by ext U x; rfl).symm

attribute [local implicit_reducible] kernelSubmoduleIsLimit

/-- The sectionwise kernel is canonically isomorphic to the categorical kernel. -/
public noncomputable def kernelSubmoduleIso {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf} (f : M ⟶ N) :
    (kernelSubmodule f).toSheafOfModules ≅ kernel f :=
  (kernelSubmoduleIsLimit f).conePointUniqueUpToIso (limit.isLimit _)

attribute [local implicit_reducible] kernelSubmoduleIso

/-- A quasi-coherent submodule of the structure sheaf determines ideal-sheaf data
with the same sections on every affine open. -/
public theorem exists_idealSheafData_of_submodule (X : Scheme.{u})
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] :
    ∃ J : X.IdealSheafData, ∀ U : X.affineOpens,
      Crystalline.sectionIdeal X.sheaf I (op U.1) = J.ideal U :=
  ⟨Stacks.Divisors.idealSheafDataOfSubmodule I, fun _ => rfl⟩

/-- Quasi-coherent ideal sections commute with restriction between affine opens. -/
public theorem sectionIdeal_map_of_isQuasicoherent
    (X : Scheme.{u}) (I : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent]
    (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    (Crystalline.sectionIdeal X.sheaf I (op U.1)).map
        (X.presheaf.map (homOfLE h).op).hom =
      Crystalline.sectionIdeal X.sheaf I (op V.1) := by
  obtain ⟨J, hJ⟩ := exists_idealSheafData_of_submodule X I
  rw [hJ, hJ]
  exact J.map_ideal h

/-- An ideal transported along a composite, given the two successive transports. -/
public theorem ideal_map_eq_of_comp {R S T : CommRingCat.{u}}
    {φ : R ⟶ S} {ψ : S ⟶ T} {χ : R ⟶ T} (hχ : φ ≫ ψ = χ)
    {I : Ideal R} {K : Ideal S} {L : Ideal T}
    (h₁ : I.map φ.hom = K) (h₂ : K.map ψ.hom = L) : I.map χ.hom = L := by
  subst hχ h₁ h₂
  rw [CommRingCat.hom_comp, Ideal.map_map]

/-- Transporting an ideal of sections along two successive restriction maps is
transport along the restriction map of the composite. -/
public theorem ideal_map_appLE_appLE {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : Z.Opens} {V : Y.Opens} {W : X.Opens}
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (I : Ideal Γ(Z, U)) :
    (I.map (g.appLE U V e₁).hom).map (f.appLE V W e₂).hom =
      I.map ((f ≫ g).appLE U W (fun _ hx => e₁ (e₂ hx))).hom := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

/-- A divided-power morphism is compatible with restriction to a smaller source open. -/
public theorem dividedPowerHom_appLE {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y)
    (U : Y.scheme.Opens) (V : X.scheme.Opens) (h : V ≤ f.hom ⁻¹ᵁ U) :
    DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op U))
      (X.dividedPowers.dividedPowers (op V)) (f.hom.appLE U V h).hom :=
  DividedPowers.IsDPMorphism.comp _
    (X.dividedPowers.naturality (homOfLE h).op) (f.compatible U)

/-- Mapping an ideal of sections forward along an isomorphism of rings of sections is the same as
comapping it along the inverse isomorphism. -/
public theorem map_hom_eq_comap_inv {A B : CommRingCat.{u}} (e : A ≅ B) (J : Ideal A) :
    J.map e.hom.hom = J.comap e.inv.hom :=
  Ideal.map_comap_of_equiv e.commRingCatIsoToRingEquiv

/-- The ideal of an open restriction is generated by the restricted ideal sections. -/
public theorem idealSheafAsSubmodule_comap_open
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) [IsOpenImmersion f]
    (U : X.affineOpens) (V : Y.affineOpens) (h : V.1 ≤ f ⁻¹ᵁ U.1) :
    (I.ideal U).map (f.appLE U.1 V.1 h).hom =
      Crystalline.sectionIdeal Y.sheaf (idealSheafAsSubmodule (I.comap f)) (op V.1) := by
  change (I.ideal U).map (f.appLE U.1 V.1 h).hom =
    (idealSheafAsSubmodule (I.comap f)).toSubmodule.obj (op V.1)
  rw [idealSheafAsSubmodule_obj_affine, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  let W : X.affineOpens := ⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩
  have hW : W.1 ≤ U.1 := (f.image_mono h).trans (f.image_preimage_le _)
  have he : X.presheaf.map (homOfLE hW).op ≫ (f.appIso V.1).hom =
      f.appLE U.1 V.1 h := by
    apply (cancel_mono (f.appIso V.1).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Scheme.Hom.appLE_appIso_inv]
  have h1 : (I.ideal U).map (f.appLE U.1 V.1 h).hom =
      (I.ideal W).map (f.appIso V.1).hom.hom := by
    rw [← he, CommRingCat.hom_comp, ← Ideal.map_map]
    exact congrArg (fun K => Ideal.map (f.appIso V.1).hom.hom K) (I.map_ideal hW)
  rw [h1, map_hom_eq_comap_inv]

/-- Membership in an ideal is detected by a ring equivalence carrying it onto another. -/
public theorem mem_ideal_iff_map_equiv
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    (e : R ≃+* S) (h : I.map e = J) (x : R) : x ∈ I ↔ e x ∈ J := by
  rw [← h, Ideal.mem_map_of_equiv]
  exact ⟨fun hx => ⟨x, hx, rfl⟩,
    fun ⟨y, hy, he⟩ => e.injective he ▸ hy⟩

/-- Restriction to a smaller open of the target followed by the identification of
sections on the image is the restriction map of an open immersion. -/
public theorem map_comp_appIso_hom {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
    (W : Y.Opens) (V : X.Opens) (hB : i ''ᵁ W ≤ V) (h : W ≤ i ⁻¹ᵁ V) :
    X.presheaf.map (homOfLE hB).op ≫ (i.appIso W).hom = i.appLE V W h := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

/-- An open immersion of divided-power schemes with the induced ideal. -/
public structure IsInducedOpen {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y) : Prop where
  isOpenImmersion : IsOpenImmersion f.hom
  ideal_map (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
      (h : V.1 ≤ f.hom ⁻¹ᵁ U.1) :
    (Crystalline.sectionIdeal Y.scheme.sheaf Y.ideal (op U.1)).map
        (f.hom.appLE U.1 V.1 h).hom =
      Crystalline.sectionIdeal X.scheme.sheaf X.ideal (op V.1)

/-- Factorization through an induced open subscheme preserves divided powers. -/
public noncomputable def inducedOpenLift
    {X Y Z : DividedPowerScheme.{u}} (f : X ⟶ Y) (hf : IsInducedOpen f)
    (g : Z ⟶ Y) (k : Z.scheme ⟶ X.scheme) (hk : k ≫ f.hom = g.hom) : Z ⟶ X where
  hom := k
  compatible U := by
    have := hf.isOpenImmersion
    apply isDPMorphism_app_of_affine Z X k ?_ U
    intro V W h
    let V' : Y.scheme.affineOpens :=
      ⟨f.hom ''ᵁ V.1, V.2.image_of_isOpenImmersion f.hom⟩
    have hV : V.1 ≤ f.hom ⁻¹ᵁ V'.1 := fun x hx => ⟨x, hx, rfl⟩
    apply DividedPowers.IsDPMorphism.of_comp
      (Y.dividedPowers.dividedPowers (op V'.1))
      (X.dividedPowers.dividedPowers (op V.1))
      (Z.dividedPowers.dividedPowers (op W.1))
      (f.hom.appLE V'.1 V.1 hV).hom (k.appLE V.1 W.1 h).hom
      (hf.ideal_map V' V hV).symm (dividedPowerHom_appLE f V'.1 V.1 hV)
    have hW : W.1 ≤ g.hom ⁻¹ᵁ V'.1 := by
      rw [← hk]
      exact fun x hx => hV (h hx)
    have hcomp : (k.appLE V.1 W.1 h).hom.comp (f.hom.appLE V'.1 V.1 hV).hom =
        (g.hom.appLE V'.1 W.1 hW).hom := by
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
      simp only [hk]
    exact hcomp ▸ dividedPowerHom_appLE g V'.1 W.1 hW

attribute [local implicit_reducible] inducedOpenLift

/-- The functor forgetting the divided-power ideal and structure. -/
public def dividedPowerSchemeForget : DividedPowerScheme.{u} ⥤ Scheme.{u} where
  obj X := X.scheme
  map f := f.hom

attribute [local implicit_reducible] dividedPowerSchemeForget

/-- A section of the divided power ideal dies on the closed fibre. -/
public theorem closedFiberι_app_eq_zero (D : DividedPowerScheme.{u}) (U : D.scheme.Opens)
    (x : Γ(D.scheme, U)) (hx : x ∈ D.ideal.obj (op U)) : ((closedFiberι D).app U) x = 0 :=
  (closedFiberPresentation D).app_eq_zero_of_mem U x hx

/-- The zero ideal sheaf of a scheme, presented as the kernel of the comparison attached to
the identity, so that it comes with the quasi-coherence of such a kernel. -/
public noncomputable abbrev zeroIdeal (Z : Scheme.{u}) :=
  kernelSubmodule (SheafOfModules.unitToPushforwardObjUnit
    (𝟙 Z : Z ⟶ Z).toRingCatSheafHom)

/-- The zero ideal sheaf is quasi-coherent. -/
public theorem zeroIdeal_isQuasicoherent (Z : Scheme.{u}) :
    (zeroIdeal Z).toSheafOfModules.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso (kernelSubmoduleIso _).symm
    (AlgebraicGeometry.isQuasicoherent_kernel_unitToPushforwardObjUnit (𝟙 Z))

/-- The sections of the zero ideal sheaf over any open form the zero ideal. -/
public theorem zeroIdeal_section_eq_bot (Z : Scheme.{u}) (U : Z.Opens) :
    Crystalline.sectionIdeal Z.sheaf (zeroIdeal Z) (op U) = ⊥ := by
  have hBasis : TopologicalSpace.Opens.IsBasis
      (Set.range fun V : Z.affineOpens => V.1) := by
    simpa using Z.isBasis_affineOpens
  ext x
  constructor
  · intro hx
    apply section_ext_basis Z (fun V : Z.affineOpens => V.1)
      hBasis
    intro V hVU
    have hm := (zeroIdeal Z).map_mem (homOfLE hVU).op hx
    have hV : (zeroIdeal Z).obj (op V.1) = (𝟙 Z : Z ⟶ Z).ker.ideal V := by
      rw [Scheme.Hom.ker_apply]
      rfl
    have hker : (𝟙 Z : Z ⟶ Z).ker.ideal V = ⊥ := by
      rw [Scheme.Hom.ker_apply]
      ext y
      change (CommRingCat.Hom.hom (𝟙 Γ(Z, V))) y = 0 ↔ y = 0
      simp
    rw [hV, hker] at hm
    have hz : (Z.presheaf.map (homOfLE hVU).op).hom x = 0 := by
      change (Z.presheaf.map (homOfLE hVU).op).hom x ∈ (⊥ : Ideal Γ(Z, V.1)) at hm
      simpa using hm
    rw [hz]
    symm
    exact map_zero _
  · rintro rfl
    exact (Crystalline.sectionIdeal Z.sheaf (zeroIdeal Z) (op U)).zero_mem

/-- Being a divided power morphism is transported along equalities of the two ideals. -/
public theorem dpMorphism_transport_ideals
    {R T : Type*} [CommRing R] [CommRing T] {I I' : Ideal R} {J J' : Ideal T}
    (eI : I = I') (eJ : J = J') {γ : DividedPowers I'} {δ : DividedPowers J'}
    (f : R →+* T) (h : DividedPowers.IsDPMorphism γ δ f) :
    DividedPowers.IsDPMorphism (eI ▸ γ) (eJ ▸ δ) f := by
  cases eI
  cases eJ
  exact h

/-- Every scheme is a divided-power scheme with zero ideal. -/
public noncomputable def zeroDividedPowerScheme
    (Z : Scheme.{u}) : DividedPowerScheme.{u} where
  scheme := Z
  ideal := zeroIdeal Z
  isQuasicoherent := zeroIdeal_isQuasicoherent Z
  dividedPowers := {
    dividedPowers := fun U =>
      (zeroIdeal_section_eq_bot Z U.unop) ▸
        dividedPowersBot (Z.sheaf.obj.obj U)
    naturality := by
      intro U V r
      have h : DividedPowers.IsDPMorphism
          (dividedPowersBot (Z.sheaf.obj.obj U))
          (dividedPowersBot (Z.sheaf.obj.obj V))
          (Z.sheaf.obj.map r).hom := by
        refine ⟨?_, ?_⟩
        · simp
        · intro n x hx
          obtain rfl : x = 0 := by simpa using hx
          cases n <;> simp [dividedPowersBot]
      exact dpMorphism_transport_ideals (zeroIdeal_section_eq_bot Z U.unop)
        (zeroIdeal_section_eq_bot Z V.unop) _ h
  }

attribute [local implicit_reducible] zeroDividedPowerScheme

/-- A morphism into the closed fibre, composed with the closed-fibre inclusion, kills the
divided power ideal on sections. -/
public theorem zeroDividedPowerScheme_map_kills
    {Z : Scheme.{u}} {X : DividedPowerScheme.{u}}
    (g : Z ⟶ closedFiber X) (U : X.scheme.Opens)
    (x : Γ(X.scheme, U)) (hx : x ∈ X.ideal.obj (op U)) :
    ((g ≫ closedFiberι X).app U) x = 0 := by
  rw [Scheme.Hom.comp_app]
  change g.app (closedFiberι X ⁻¹ᵁ U)
    ((closedFiberι X).app U x) = 0
  rw [closedFiberι_app_eq_zero X U x hx]
  exact map_zero _

/-- A morphism of schemes into the closed fibre of `X`, read as a morphism of divided power
schemes out of its source with the zero ideal. -/
public noncomputable def zeroDividedPowerScheme_map
    {Z : Scheme.{u}} {X : DividedPowerScheme.{u}}
    (g : Z ⟶ closedFiber X) : zeroDividedPowerScheme Z ⟶ X where
  hom := g ≫ closedFiberι X
  compatible U := by
    let k := g ≫ closedFiberι X
    have hkill (a : Γ(X.scheme, U))
        (ha : a ∈ Crystalline.sectionIdeal X.scheme.sheaf X.ideal (op U)) :
        k.app U a = 0 := zeroDividedPowerScheme_map_kills g U a ha
    have hmap :
        (Crystalline.sectionIdeal X.scheme.sheaf X.ideal (op U)).map (k.app U).hom ≤
        Crystalline.sectionIdeal Z.sheaf (zeroIdeal Z) (op (k ⁻¹ᵁ U)) := by
      rw [zeroIdeal_section_eq_bot Z (k ⁻¹ᵁ U)]
      apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change (k.app U).hom a ∈ (⊥ : Ideal Γ(Z, k ⁻¹ᵁ U))
      exact Ideal.mem_bot.mpr (hkill a ha)
    refine ⟨hmap, ?_⟩
    intro n a ha
    cases n with
    | zero =>
      have hzero := zeroIdeal_section_eq_bot Z (k ⁻¹ᵁ U)
      let hleft := hzero ▸ dividedPowersBot
        (Z.sheaf.obj.obj (op (k ⁻¹ᵁ U)))
      change hleft.dpow 0 ((k.app U).hom a) = (k.app U).hom
        ((X.dividedPowers.dividedPowers (op U)).dpow 0 a)
      rw [hleft.dpow_zero (hmap (Ideal.mem_map_of_mem (k.app U).hom ha)),
        (X.dividedPowers.dividedPowers (op U)).dpow_zero ha]
      exact (map_one (k.app U).hom).symm
    | succ n =>
      have ha' := (X.dividedPowers.dividedPowers (op U)).dpow_mem
        (Nat.succ_ne_zero n) ha
      have hmem := ((zeroDividedPowerScheme Z).dividedPowers.dividedPowers
        (op (k ⁻¹ᵁ U))).dpow_mem (Nat.succ_ne_zero n)
        (hmap (Ideal.mem_map_of_mem (k.app U).hom ha))
      change ((zeroDividedPowerScheme Z).dividedPowers.dividedPowers
          (op (k ⁻¹ᵁ U))).dpow (n + 1) ((k.app U).hom a) ∈
        Crystalline.sectionIdeal Z.sheaf (zeroIdeal Z) (op (k ⁻¹ᵁ U)) at hmem
      rw [zeroIdeal_section_eq_bot] at hmem
      have hleft : ((zeroDividedPowerScheme Z).dividedPowers.dividedPowers
          (op (k ⁻¹ᵁ U))).dpow (n + 1) ((k.app U).hom a) = 0 :=
        Ideal.mem_bot.mp hmem
      change ((zeroDividedPowerScheme Z).dividedPowers.dividedPowers
          (op (k ⁻¹ᵁ U))).dpow (n + 1) ((k.app U).hom a) =
        (k.app U).hom ((X.dividedPowers.dividedPowers (op U)).dpow (n + 1) a)
      rw [hleft]
      exact (hkill _ ha').symm

attribute [local implicit_reducible] zeroDividedPowerScheme_map

/-- The sections of the ideal of a scheme read with the zero divided power ideal form the zero
ideal. -/
public theorem zeroDividedPowerScheme_section_eq_bot (Z : Scheme.{u})
    (U : (zeroDividedPowerScheme Z).scheme.Opens) :
    Crystalline.sectionIdeal (zeroDividedPowerScheme Z).scheme.sheaf
      (zeroDividedPowerScheme Z).ideal (op U) = ⊥ :=
  zeroIdeal_section_eq_bot Z U

/-- The closed fibre of a scheme with the zero divided power ideal is the scheme itself: the
identity is a closed immersion and cuts out the zero ideal on sections. -/
public noncomputable def zeroClosedFiberPresentation (Z : Scheme.{u}) :
    ClosedFiberPresentation (zeroDividedPowerScheme Z) where
  carrier := Z
  ι := (𝟙 Z : Z ⟶ Z)
  isClosedImmersion := inferInstanceAs (IsClosedImmersion (𝟙 Z : Z ⟶ Z))
  app_eq_zero_of_mem V s hs := by
    rw [zeroDividedPowerScheme_section_eq_bot] at hs
    rw [Ideal.mem_bot.mp hs]
    exact map_zero _
  mem_of_app_eq_zero V s hs := by
    rw [zeroDividedPowerScheme_section_eq_bot]
    refine Ideal.mem_bot.mpr ?_
    have h : ∀ (W : Z.Opens) (y : Γ(Z, W)), ((𝟙 Z : Z ⟶ Z).app W).hom y = y := by
      intro W y
      simp only [Scheme.Hom.id_app]
      exact CategoryTheory.id_apply y
    exact (h V.1 s).symm.trans hs

attribute [local implicit_reducible] zeroClosedFiberPresentation

/-- A morphism out of a scheme with the zero divided power ideal factors uniquely through the
closed fibre of the target. -/
public noncomputable def zeroDividedPowerScheme_map_factorSpec
    {Z : Scheme.{u}} {X : DividedPowerScheme.{u}}
    (φ : zeroDividedPowerScheme Z ⟶ X) :
    {g : Z ⟶ closedFiber X // g ≫ closedFiberι X = φ.hom} :=
  ⟨((zeroClosedFiberPresentation Z).map (closedFiberPresentation X) φ).1,
    ((zeroClosedFiberPresentation Z).map (closedFiberPresentation X) φ).2.trans
      (Category.id_comp φ.hom)⟩

attribute [local implicit_reducible] zeroDividedPowerScheme_map_factorSpec

/-- The factorization of a morphism out of a scheme with the zero divided power ideal through
the closed fibre of the target. -/
public noncomputable def zeroDividedPowerScheme_map_factor
    {Z : Scheme.{u}} {X : DividedPowerScheme.{u}}
    (φ : zeroDividedPowerScheme Z ⟶ X) : Z ⟶ closedFiber X :=
  (zeroDividedPowerScheme_map_factorSpec φ).val

attribute [local implicit_reducible] zeroDividedPowerScheme_map_factor

/-- The factorization through the closed fibre recovers the original morphism. -/
public theorem zeroDividedPowerScheme_map_factor_comp
    {Z : Scheme.{u}} {X : DividedPowerScheme.{u}}
    (φ : zeroDividedPowerScheme Z ⟶ X) :
    zeroDividedPowerScheme_map_factor φ ≫ closedFiberι X = φ.hom :=
  (zeroDividedPowerScheme_map_factorSpec φ).property

/-- Closed fibres form a functor. -/
public def closedFiberFunctor : DividedPowerScheme.{u} ⥤ Scheme.{u} where
  obj := closedFiber
  map := closedFiberMap
  map_id X := by
    apply (cancel_mono (closedFiberι X)).mp
    rw [closedFiberMap_comp_closedFiberι, DividedPowerScheme.Hom.id_hom,
      Category.comp_id, Category.id_comp]
  map_comp {X Y Z} f g := by
    apply (cancel_mono (closedFiberι Z)).mp
    rw [closedFiberMap_comp_closedFiberι, DividedPowerScheme.Hom.comp_hom]
    calc
      _ = (closedFiberι X ≫ f.hom) ≫ g.hom := (Category.assoc _ _ _).symm
      _ = (closedFiberMap f ≫ closedFiberι Y) ≫ g.hom :=
        congrArg (fun k => k ≫ g.hom) (closedFiberMap_comp_closedFiberι f).symm
      _ = _ := by rw [Category.assoc, Category.assoc, closedFiberMap_comp_closedFiberι]

attribute [local implicit_reducible] closedFiberFunctor

/-- An induced open immersion gives a cartesian square on closed-fibre inclusions. -/
public theorem closedFiberι_isPullback_of_inducedOpen
    {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y) (hf : IsInducedOpen f) :
    IsPullback (closedFiberι X) (closedFiberMap f)
      f.hom (closedFiberι Y) := by
  have hw := (closedFiberMap_comp_closedFiberι f).symm
  let lift (s : PullbackCone f.hom (closedFiberι Y)) :=
    zeroDividedPowerScheme_map_factor
      (inducedOpenLift f hf (zeroDividedPowerScheme_map s.snd) s.fst s.condition)
  have hl (s : PullbackCone f.hom (closedFiberι Y)) :
      lift s ≫ closedFiberι X = s.fst :=
    zeroDividedPowerScheme_map_factor_comp _
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw lift hl ?_ ?_⟩⟩
  · intro s
    apply (cancel_mono (closedFiberι Y)).mp
    rw [Category.assoc, closedFiberMap_comp_closedFiberι, ← Category.assoc, hl, s.condition]
  · intro s m hm _
    apply (cancel_mono (closedFiberι X)).mp
    exact hm.trans (hl s).symm

/-- Over an affine open, the kernel of the closed-fibre inclusion is the divided power ideal. -/
public theorem closedFiberι_ker_ideal (X : DividedPowerScheme.{u})
    (U : X.scheme.affineOpens) :
    (closedFiberι X).ker.ideal U =
      Crystalline.sectionIdeal X.scheme.sheaf X.ideal (op U.1) := by
  rw [Scheme.Hom.ker_apply]
  refine SetLike.ext fun s => ?_
  rw [RingHom.mem_ker]
  exact (closedFiberPresentation X).app_eq_zero_iff U s

/-- Conversely, an open immersion whose square on closed-fibre inclusions is cartesian has the
induced ideal. -/
public theorem isInducedOpen_of_closedFiber_isPullback
    {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f.hom]
    (H : IsPullback (closedFiberι X) (closedFiberMap f) f.hom (closedFiberι Y)) :
    IsInducedOpen f := by
  refine ⟨inferInstance, ?_⟩
  intro U V h
  have hk := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (closedFiberι Y) (closedFiberι X) (closedFiberMap f) f.hom H V
  rw [closedFiberι_ker_ideal] at hk
  have hmap := idealSheafAsSubmodule_comap_open (closedFiberι Y).ker f.hom U V h
  rw [closedFiberι_ker_ideal] at hmap
  refine hmap.trans ?_
  change (idealSheafAsSubmodule ((closedFiberι Y).ker.comap f.hom)).toSubmodule.obj (op V.1) = _
  rw [idealSheafAsSubmodule_obj_affine, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact hk.symm

/-- An isomorphism of divided power schemes is an induced open immersion. -/
public theorem isInducedOpen_of_isIso {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y)
    [IsIso f] : IsInducedOpen f := by
  have : IsIso f.hom := dividedPowerSchemeForget.map_isIso f
  have : IsIso (closedFiberMap f) := closedFiberFunctor.map_isIso f
  exact isInducedOpen_of_closedFiber_isPullback f <|
    IsPullback.of_vert_isIso ⟨(closedFiberMap_comp_closedFiberι f).symm⟩

/-- Induced open immersions are closed under composition. -/
public theorem IsInducedOpen.comp {X Y Z : DividedPowerScheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsInducedOpen f) (hg : IsInducedOpen g) :
    IsInducedOpen (f ≫ g) := by
  have := hf.isOpenImmersion
  have := hg.isOpenImmersion
  refine ⟨inferInstanceAs (IsOpenImmersion (f.hom ≫ g.hom)), ?_⟩
  intro U V h
  let W : Y.scheme.affineOpens := ⟨f.hom ''ᵁ V.1, V.2.image_of_isOpenImmersion f.hom⟩
  have hW : W.1 ≤ g.hom ⁻¹ᵁ U.1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact h hx
  have hV : V.1 ≤ f.hom ⁻¹ᵁ W.1 := fun x hx => ⟨x, hx, rfl⟩
  rw [← hf.ideal_map W V hV, ← hg.ideal_map U W hW]
  exact (ideal_map_appLE_appLE f.hom g.hom hW hV _).symm

/-- A locally directed open presentation by divided-power schemes. -/
public structure DividedPowerOpenPresentation (J : Type u) [Category.{u} J]
    (X : Scheme.{u}) where
  /-- The diagram of divided power schemes forming the charts. -/
  functor : J ⥤ DividedPowerScheme.{u}
  /-- The cocone from the underlying schemes of the charts to `X`. -/
  ι : functor ⋙ dividedPowerSchemeForget ⟶ (CategoryTheory.Functor.const J).obj X
  /-- Each chart maps to `X` by an open immersion. -/
  isOpen (i : J) : IsOpenImmersion (ι.app i)
  /-- Every point of `X` lies in the image of some chart. -/
  surjective (x : X) : ∃ (i : J) (y : (functor.obj i).scheme), ι.app i y = x
  /-- Every transition map is an induced open immersion. -/
  induced {i j : J} (h : i ⟶ j) : IsInducedOpen (functor.map h)
  /-- Two points of charts with the same image in `X` come from a common point of a third chart
  mapping to both. -/
  directed {i j : J} (xi : (functor.obj i).scheme) (xj : (functor.obj j).scheme)
      (h : ι.app i xi = ι.app j xj) :
    ∃ (k : J) (ki : k ⟶ i) (kj : k ⟶ j) (xk : (functor.obj k).scheme),
      (functor.map ki).hom xk = xi ∧ (functor.map kj).hom xk = xj

/-- The charts of an open presentation are open immersions. -/
public instance {J : Type u} [Category.{u} J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (i : J) : IsOpenImmersion (d.ι.app i) := d.isOpen i

/-- The underlying open cover of the base scheme given by an open presentation. -/
public abbrev DividedPowerOpenPresentation.cover
    {J : Type u} [Category.{u} J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) : X.OpenCover where
  I₀ := J
  X i := (d.functor.obj i).scheme
  f := d.ι.app
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨d.surjective, d.isOpen⟩

/-- The cover underlying an open presentation is locally directed, with the transition maps
coming from the presentation's functor. -/
public instance {J : Type u} [Category.{u} J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) : d.cover.LocallyDirected where
  trans h := (d.functor.map h).hom
  trans_id i := congrArg DividedPowerScheme.Hom.hom (d.functor.map_id i)
  trans_comp h k := congrArg DividedPowerScheme.Hom.hom (d.functor.map_comp h k)
  w h := (d.ι.naturality h).trans (Category.comp_id _)
  property_trans h := (d.induced h).isOpenImmersion
  directed {i j} z := by
    let xi := pullback.fst (d.cover.f i) (d.cover.f j) z
    let xj := pullback.snd (d.cover.f i) (d.cover.f j) z
    obtain ⟨k, ki, kj, xk, hi, hj⟩ := d.directed xi xj
      (congrArg (fun f : pullback (d.cover.f i) (d.cover.f j) ⟶ X => f z) pullback.condition)
    refine ⟨k, ki, kj, xk, ?_⟩
    have := d.isOpen j
    apply (pullback.fst (d.cover.f i) (d.cover.f j)).injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hi

/-- The closed fibres in an open presentation form relative gluing data. -/
public def DividedPowerOpenPresentation.closedFiberGluing
    {J : Type u} [Category.{u} J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) :
    d.cover.RelativeGluingData where
  functor := d.functor ⋙ closedFiberFunctor
  natTrans :=
    { app i := closedFiberι (d.functor.obj i)
      naturality _ _ h := closedFiberMap_comp_closedFiberι (d.functor.map h) }
  equifibered _ _ h := (closedFiberι_isPullback_of_inducedOpen _ (d.induced h)).flip

attribute [local implicit_reducible] DividedPowerOpenPresentation.closedFiberGluing

/-- The comparison from the glued closed fibres to the base is a closed immersion. -/
public theorem DividedPowerOpenPresentation.closedFiberGluing_isClosedImmersion
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) :
    IsClosedImmersion d.closedFiberGluing.toBase := by
  apply IsZariskiLocalAtTarget.of_openCover d.cover
  intro i
  let e := (d.closedFiberGluing.isPullback_natTrans_ι_toBase i).flip.isoPullback
  have he : d.cover.pullbackHom d.closedFiberGluing.toBase i =
      e.inv ≫ closedFiberι (d.functor.obj i) := by
    apply (cancel_epi e.hom).mp
    rw [e.hom_inv_id_assoc]
    exact (d.closedFiberGluing.isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_snd
  rw [he]
  exact @IsClosedImmersion.comp _ _ _ e.inv (closedFiberι (d.functor.obj i))
    inferInstance inferInstance

/-- The ideal of the glued closed fibre is quasi-coherent. -/
public noncomputable def DividedPowerOpenPresentation.ideal
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) :
    (SheafOfModules.unit X.ringCatSheaf).Submodule :=
  kernelSubmodule (SheafOfModules.unitToPushforwardObjUnit
    d.closedFiberGluing.toBase.toRingCatSheafHom)

attribute [local implicit_reducible] DividedPowerOpenPresentation.ideal

/-- The glued ideal is quasi-coherent, being the kernel of a closed immersion. -/
public theorem DividedPowerOpenPresentation.ideal_isQuasicoherent
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) : d.ideal.toSheafOfModules.IsQuasicoherent := by
  have := d.closedFiberGluing_isClosedImmersion
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (kernelSubmoduleIso _).symm
    (AlgebraicGeometry.isQuasicoherent_kernel_unitToPushforwardObjUnit d.closedFiberGluing.toBase)

/-- Over an affine open of a chart, the glued ideal restricts to the ideal of that chart. -/
public theorem DividedPowerOpenPresentation.ideal_map_appIso
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (i : J)
    (U : (d.functor.obj i).scheme.affineOpens) :
    (Crystalline.sectionIdeal X.sheaf d.ideal (op (d.ι.app i ''ᵁ U.1))).map
        ((d.ι.app i).appIso U.1).hom.hom =
      Crystalline.sectionIdeal (d.functor.obj i).scheme.sheaf
        (d.functor.obj i).ideal (op U.1) := by
  have := d.isOpen i
  have := d.closedFiberGluing_isClosedImmersion
  have h := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    d.closedFiberGluing.toBase (closedFiberι (d.functor.obj i))
    (d.closedFiberGluing.cover.f i) (d.ι.app i)
    (d.closedFiberGluing.isPullback_natTrans_ι_toBase i) U
  rw [← closedFiberι_ker_ideal, h]
  have he : Crystalline.sectionIdeal X.sheaf d.ideal (op (d.ι.app i ''ᵁ U.1)) =
      d.closedFiberGluing.toBase.ker.ideal
        ⟨d.ι.app i ''ᵁ U.1, U.2.image_of_isOpenImmersion _⟩ := by
    rw [Scheme.Hom.ker_apply]
    rfl
  rw [he]
  exact Ideal.map_comap_of_equiv ((d.ι.app i).appIso U.1).commRingCatIsoToRingEquiv

/-- Divided powers pulled back along a ring equivalence carrying `I` onto `J`. -/
public noncomputable def dividedPowersOfRingEquiv
    {R A : Type*} [CommRing R] [CommRing A] (I : Ideal R) (J : Ideal A)
    (e : R ≃+* A) (h : I.map e = J) (γ : DividedPowers J) : DividedPowers I :=
  (DividedPowers.equiv h).symm γ

/-- Comparison of the two identifications of sections attached to a commuting triangle of open
immersions. -/
public theorem appIso_comp_appLE_of_comp
    {X Y Z : Scheme.{u}} (i : X ⟶ Z) (j : Y ⟶ Z) [IsOpenImmersion i]
    [IsOpenImmersion j] (k : Y ⟶ X) (hk : k ≫ i = j)
    (U : X.Opens) (V : Y.Opens) (h : V ≤ k ⁻¹ᵁ U)
    (hUV : j ''ᵁ V ≤ i ''ᵁ U) :
    Z.presheaf.map (homOfLE hUV).op ≫ (j.appIso V).hom =
      (i.appIso U).hom ≫ k.appLE U V h := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_comp_appLE]
  simp only [hk]

/-- A map is a divided power morphism as soon as it is so after composing with an injective
divided power morphism. -/
public theorem isDPMorphism_of_comp_injective
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    {I : Ideal A} {J : Ideal B} {K : Ideal C}
    {γ : DividedPowers I} {δ : DividedPowers J} {ε : DividedPowers K}
    (f : A →+* B) (g : B →+* C) (hg : Function.Injective g)
    (hI : I.map f ≤ J) (hδ : DividedPowers.IsDPMorphism δ ε g)
    (hγ : DividedPowers.IsDPMorphism γ ε (g.comp f)) :
    DividedPowers.IsDPMorphism γ δ f := by
  refine ⟨hI, ?_⟩
  intro n x hx
  apply hg
  exact (hδ.map_dpow (hI (Ideal.mem_map_of_mem _ hx))).trans (hγ.map_dpow hx).symm

/-- An index for the basis of the base scheme attached to an open presentation: a chart
together with an affine open of it. -/
public abbrev DividedPowerOpenPresentation.basisIndex
    {J : Type u} [Category.{u} J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) :=
  (i : J) × (d.functor.obj i).scheme.affineOpens

/-- The open of the base scheme attached to a basis index: the image of the affine open under
the chart's inclusion. -/
public abbrev DividedPowerOpenPresentation.basisOpen
    {J : Type u} [Category.{u} J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (a : d.basisIndex) : X.Opens :=
  d.ι.app a.1 ''ᵁ a.2.1

/-- The opens attached to the basis indices of an open presentation form a basis of the base. -/
public theorem DividedPowerOpenPresentation.isBasis
    {J : Type u} [Category.{u} J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) :
    TopologicalSpace.Opens.IsBasis (Set.range d.basisOpen) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨i, y, rfl⟩ := d.surjective x
  obtain ⟨V, hV, hy, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (d.functor.obj i).scheme.isBasis_affineOpens (U := d.ι.app i ⁻¹ᵁ U) hx
  refine ⟨d.ι.app i ''ᵁ V, ⟨⟨i, ⟨V, hV⟩⟩, rfl⟩, ⟨y, hy, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hVU hz

-- Transporting the divided powers of a chart along the isomorphism on sections over a basis
-- open unfolds the gluing data of the presentation, which is expensive.
/-- The transition maps of an open presentation are compatible with the chart inclusions. -/
public theorem DividedPowerOpenPresentation.map_ι
    {J : Type u} [Category.{u} J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) {i j : J} (h : i ⟶ j) :
    (d.functor.map h).hom ≫ d.ι.app j = d.ι.app i :=
  (d.ι.naturality h).trans (Category.comp_id _)

/-- The divided powers on a basis open: those of the chart, transported along the
identification of sections. -/
public noncomputable def DividedPowerOpenPresentation.basisDividedPowers
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (a : d.basisIndex) :
    DividedPowers (Crystalline.sectionIdeal X.sheaf d.ideal (op (d.basisOpen a))) :=
  dividedPowersOfRingEquiv _ _ ((d.ι.app a.1).appIso a.2.1).commRingCatIsoToRingEquiv
    (d.ideal_map_appIso a.1 a.2)
    ((d.functor.obj a.1).dividedPowers.dividedPowers (op a.2.1))

attribute [local implicit_reducible] DividedPowerOpenPresentation.basisDividedPowers

/-- The identification of sections over a basis open with those of its chart is a divided power
morphism. -/
public theorem DividedPowerOpenPresentation.basisDividedPowers_isDPMorphism
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (a : d.basisIndex) :
    DividedPowers.IsDPMorphism (d.basisDividedPowers a)
      ((d.functor.obj a.1).dividedPowers.dividedPowers (op a.2.1))
      ((d.ι.app a.1).appIso a.2.1).hom.hom := by
  refine ⟨(d.ideal_map_appIso a.1 a.2).le, ?_⟩
  intro n x hx
  exact (((d.ι.app a.1).appIso a.2.1).commRingCatIsoToRingEquiv.apply_symm_apply _).symm

/-- A transition map of the presentation carrying one affine open into another orders the two
basis opens. -/
public theorem DividedPowerOpenPresentation.basisOpen_le
    {J : Type u} [Category.{u} J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (a b : d.basisIndex) (h : b.1 ⟶ a.1)
    (hU : b.2.1 ≤ (d.functor.map h).hom ⁻¹ᵁ a.2.1) :
    d.basisOpen b ≤ d.basisOpen a := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨(d.functor.map h).hom y, hU hy, ?_⟩
  exact congrArg (fun f : (d.functor.obj b.1).scheme ⟶ X => f y) (d.map_ι h)

/-- The basis divided powers are compatible with the restriction along a transition map of the
presentation. -/
public theorem DividedPowerOpenPresentation.basisDividedPowers_map
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (a b : d.basisIndex) (h : b.1 ⟶ a.1)
    (hU : b.2.1 ≤ (d.functor.map h).hom ⁻¹ᵁ a.2.1) :
    DividedPowers.IsDPMorphism (d.basisDividedPowers a) (d.basisDividedPowers b)
      (X.presheaf.map (homOfLE (d.basisOpen_le a b h hU)).op).hom := by
  let r := (X.presheaf.map (homOfLE (d.basisOpen_le a b h hU)).op).hom
  have hr : (Crystalline.sectionIdeal X.sheaf d.ideal (op (d.basisOpen a))).map r ≤
      Crystalline.sectionIdeal X.sheaf d.ideal (op (d.basisOpen b)) :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => d.ideal.map_mem
      (homOfLE (d.basisOpen_le a b h hU)).op hx
  apply isDPMorphism_of_comp_injective r ((d.ι.app b.1).appIso b.2.1).hom.hom
    ((d.ι.app b.1).appIso b.2.1).commRingCatIsoToRingEquiv.injective hr
    (d.basisDividedPowers_isDPMorphism b)
  dsimp only [r]
  rw [← CommRingCat.hom_comp, appIso_comp_appLE_of_comp (Z := X) _ _ _ (d.map_ι h) a.2.1 b.2.1 hU]
  exact DividedPowers.IsDPMorphism.comp _
    (dividedPowerHom_appLE (d.functor.map h) a.2.1 b.2.1 hU)
    (d.basisDividedPowers_isDPMorphism a)

/-- The basis divided powers are compatible with every inclusion of basis opens, not only with
those coming from a transition map: local directedness refines any overlap to a common chart. -/
public theorem DividedPowerOpenPresentation.basisDividedPowers_naturality
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (a b : d.basisIndex)
    (r : d.basisOpen b ⟶ d.basisOpen a) :
    DividedPowers.IsDPMorphism (d.basisDividedPowers a) (d.basisDividedPowers b)
      (X.presheaf.map r.op).hom := by
  refine ⟨Ideal.map_le_iff_le_comap.mpr (fun x hx => d.ideal.map_mem r.op hx), ?_⟩
  intro n x hx
  apply TopCat.Presheaf.IsSheaf.section_ext X.sheaf.property
  intro z hz
  obtain ⟨ya, hya, hza⟩ := leOfHom r hz
  obtain ⟨yb, hyb, hzb⟩ := hz
  obtain ⟨k, ka, kb, yk, hka, hkb⟩ := d.directed ya yb (hza.trans hzb.symm)
  have hyk : yk ∈ (d.functor.map ka).hom ⁻¹ᵁ a.2.1 ⊓
      (d.functor.map kb).hom ⁻¹ᵁ b.2.1 := by
    constructor
    · change (d.functor.map ka).hom yk ∈ a.2.1
      rwa [hka]
    · change (d.functor.map kb).hom yk ∈ b.2.1
      rwa [hkb]
  obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (d.functor.obj k).scheme.isBasis_affineOpens hyk
  let c : d.basisIndex := ⟨k, ⟨W, hW⟩⟩
  have hcaU : c.2.1 ≤ (d.functor.map ka).hom ⁻¹ᵁ a.2.1 := hWU.trans inf_le_left
  have hcbU : c.2.1 ≤ (d.functor.map kb).hom ⁻¹ᵁ b.2.1 := hWU.trans inf_le_right
  have hca := d.basisOpen_le a c ka hcaU
  have hcb := d.basisOpen_le b c kb hcbU
  have hac := d.basisDividedPowers_map a c ka hcaU
  have hbc := d.basisDividedPowers_map b c kb hcbU
  have hzc : z ∈ d.basisOpen c := by
    refine ⟨yk, hyW, ?_⟩
    have ht := congrArg (fun f : (d.functor.obj k).scheme ⟶ X => f yk) (d.map_ι kb)
    exact ht.symm.trans ((congrArg (d.ι.app b.1) hkb).trans hzb)
  have hecomp (y : Γ(X, d.basisOpen a)) :
      X.presheaf.map (homOfLE hcb).op (X.presheaf.map r.op y) =
        X.presheaf.map (homOfLE hca).op y := by
    rw [← CategoryTheory.comp_apply, ← CategoryTheory.Functor.map_comp]
    rfl
  refine ⟨d.basisOpen c, hcb, hzc, ?_⟩
  change X.presheaf.map (homOfLE hcb).op
      ((d.basisDividedPowers b).dpow n (X.presheaf.map r.op x)) =
    X.presheaf.map (homOfLE hcb).op
      (X.presheaf.map r.op ((d.basisDividedPowers a).dpow n x))
  exact (hbc.map_dpow (d.ideal.map_mem r.op hx)).trans
    ((congrArg ((d.basisDividedPowers c).dpow n) (hecomp x)).trans
      ((hac.map_dpow hx).symm.trans (hecomp _).symm))

/-- The divided power structure glued from the charts of an open presentation. -/
public noncomputable def DividedPowerOpenPresentation.dividedPowerStructure
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) :
    Crystalline.DividedPowerStructure.{u, u, u} X.sheaf d.ideal :=
  dividedPowerStructureOfBasis X d.ideal d.basisOpen d.isBasis
    d.basisDividedPowers d.basisDividedPowers_naturality

/-- The glued divided power structure restricts to the chosen divided powers on each basis
open. -/
public theorem DividedPowerOpenPresentation.dividedPowerStructure_dividedPowers
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (a : d.basisIndex) :
    d.dividedPowerStructure.dividedPowers (op (d.basisOpen a)) = d.basisDividedPowers a :=
  dividedPowerStructureOfBasis_dividedPowers X d.ideal d.basisOpen d.isBasis
    d.basisDividedPowers d.basisDividedPowers_naturality a

/-- The divided-power scheme obtained by gluing an open presentation. -/
public noncomputable def DividedPowerOpenPresentation.glued
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) : DividedPowerScheme.{u} where
  scheme := X
  ideal := d.ideal
  isQuasicoherent := d.ideal_isQuasicoherent
  dividedPowers := d.dividedPowerStructure

/-- The identification of sections of the glued scheme over a basis open with those of its
chart is a divided power morphism. -/
public theorem DividedPowerOpenPresentation.glued_appIso_isDPMorphism
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (a : d.basisIndex) :
    DividedPowers.IsDPMorphism
      (d.glued.dividedPowers.dividedPowers (op (d.basisOpen a)))
      ((d.functor.obj a.1).dividedPowers.dividedPowers (op a.2.1))
      ((d.ι.app a.1).appIso a.2.1).hom.hom := by
  change DividedPowers.IsDPMorphism
    (d.dividedPowerStructure.dividedPowers (op (d.basisOpen a))) _ _
  rw [d.dividedPowerStructure_dividedPowers a]
  exact d.basisDividedPowers_isDPMorphism a

/-- The open charts map naturally to the glued divided-power scheme. -/
public noncomputable def DividedPowerOpenPresentation.gluedι
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (i : J) : d.functor.obj i ⟶ d.glued where
  hom := d.ι.app i
  compatible U := by
    apply isDPMorphism_app_of_affine (d.functor.obj i) d.glued (d.ι.app i) ?_ U
    intro V W h
    have hB : d.basisOpen ⟨i, W⟩ ≤ V.1 := by
      rintro _ ⟨y, hy, rfl⟩
      exact h hy
    have hm := DividedPowers.IsDPMorphism.comp _ (d.glued_appIso_isDPMorphism ⟨i, W⟩)
      (d.glued.dividedPowers.naturality (homOfLE hB).op)
    have he : X.presheaf.map (homOfLE hB).op ≫ ((d.ι.app i).appIso W.1).hom =
        (d.ι.app i).appLE V.1 W.1 h :=
      map_comp_appIso_hom (d.ι.app i) W.1 V.1 hB h
    change DividedPowers.IsDPMorphism _ _ (CommRingCat.Hom.hom
      (X.presheaf.map (homOfLE hB).op ≫ ((d.ι.app i).appIso W.1).hom)) at hm
    rwa [he] at hm

/-- The ideal of a chart is induced from the glued ideal along any affine open
of the base containing the image of the chart open. -/
public theorem DividedPowerOpenPresentation.ideal_map_appLE
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (i : J)
    (W : (d.functor.obj i).scheme.affineOpens) (V : X.affineOpens)
    (hB : d.basisOpen ⟨i, W⟩ ≤ V.1) (h : W.1 ≤ d.ι.app i ⁻¹ᵁ V.1) :
    (Crystalline.sectionIdeal X.sheaf d.ideal (op V.1)).map
        ((d.ι.app i).appLE V.1 W.1 h).hom =
      Crystalline.sectionIdeal (d.functor.obj i).scheme.sheaf
        (d.functor.obj i).ideal (op W.1) := by
  have := d.ideal_isQuasicoherent
  have hI := sectionIdeal_map_of_isQuasicoherent X d.ideal V
    ⟨d.basisOpen ⟨i, W⟩, W.2.image_of_isOpenImmersion (d.ι.app i)⟩ hB
  have he : X.presheaf.map (homOfLE hB).op ≫ ((d.ι.app i).appIso W.1).hom =
      (d.ι.app i).appLE V.1 W.1 h :=
    map_comp_appIso_hom (d.ι.app i) W.1 V.1 hB h
  exact ideal_map_eq_of_comp he hI (d.ideal_map_appIso i W)

/-- Each chart is an induced open of the glued scheme. -/
public theorem DividedPowerOpenPresentation.gluedι_isInducedOpen
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (i : J) : IsInducedOpen (d.gluedι i) := by
  refine ⟨d.isOpen i, ?_⟩
  intro V W h
  exact d.ideal_map_appLE i W V
    (((d.ι.app i).image_mono h).trans ((d.ι.app i).image_preimage_le _)) h

/-- Compatibility with divided powers may be checked on the charts of an open presentation. -/
public noncomputable def DividedPowerOpenPresentation.gluedMap
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) (Y : DividedPowerScheme.{u})
    (f : X ⟶ Y.scheme) (m : ∀ i, d.functor.obj i ⟶ Y)
    (hm : ∀ i, d.ι.app i ≫ f = (m i).hom) : d.glued ⟶ Y where
  hom := f
  compatible U := by
    have hU (a : d.basisIndex) (h : d.basisOpen a ≤ f ⁻¹ᵁ U) :
        a.2.1 ≤ (m a.1).hom ⁻¹ᵁ U := by
      rw [← hm a.1]
      exact fun x hx => h ⟨x, hx, rfl⟩
    have he_apply (a : d.basisIndex) (h : d.basisOpen a ≤ f ⁻¹ᵁ U) (x : Γ(Y.scheme, U)) :
        ((d.ι.app a.1).appIso a.2.1).hom (X.presheaf.map (homOfLE h).op (f.app U x)) =
          (m a.1).hom.appLE U a.2.1 (hU a h) x := by
      change (f.appLE U (d.basisOpen a) h ≫ ((d.ι.app a.1).appIso a.2.1).hom) x = _
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
      simp only [hm a.1]
    have hmem (x : Γ(Y.scheme, U)) (hx : x ∈ Y.ideal.obj (op U)) :
        f.app U x ∈ d.ideal.obj (op (f ⁻¹ᵁ U)) := by
      apply (mem_ideal_basis X d.ideal d.basisOpen d.isBasis _).mpr
      intro a h
      apply (mem_ideal_iff_map_equiv _ _
        ((d.ι.app a.1).appIso a.2.1).commRingCatIsoToRingEquiv
        (d.ideal_map_appIso a.1 a.2) _).mpr
      change ((d.ι.app a.1).appIso a.2.1).hom
        (X.presheaf.map (homOfLE h).op (f.app U x)) ∈ _
      rw [he_apply]
      exact (dividedPowerHom_appLE (m a.1) U a.2.1 (hU a h)).ideal_comp
        (Ideal.mem_map_of_mem _ hx)
    refine ⟨Ideal.map_le_iff_le_comap.mpr hmem, ?_⟩
    intro n x hx
    apply section_ext_basis X d.basisOpen d.isBasis
    intro a h
    apply ((d.ι.app a.1).appIso a.2.1).commRingCatIsoToRingEquiv.injective
    have hres := DividedPowers.IsDPMorphism.comp _ (d.glued_appIso_isDPMorphism a)
      (d.glued.dividedPowers.naturality (homOfLE h).op)
    change ((d.ι.app a.1).appIso a.2.1).hom
        (X.presheaf.map (homOfLE h).op
          ((d.glued.dividedPowers.dividedPowers (op (f ⁻¹ᵁ U))).dpow n (f.app U x))) =
      ((d.ι.app a.1).appIso a.2.1).hom
        (X.presheaf.map (homOfLE h).op
          (f.app U ((Y.dividedPowers.dividedPowers (op U)).dpow n x)))
    have s2 : ((d.functor.obj a.1).dividedPowers.dividedPowers (op a.2.1)).dpow n
          (((d.ι.app a.1).appIso a.2.1).hom
            (X.presheaf.map (homOfLE h).op (f.app U x))) =
        ((d.functor.obj a.1).dividedPowers.dividedPowers (op a.2.1)).dpow n
          ((m a.1).hom.appLE U a.2.1 (hU a h) x) :=
      congrArg _ (he_apply a h x)
    have s3 : ((d.functor.obj a.1).dividedPowers.dividedPowers (op a.2.1)).dpow n
          ((m a.1).hom.appLE U a.2.1 (hU a h) x) =
        (m a.1).hom.appLE U a.2.1 (hU a h)
          ((Y.dividedPowers.dividedPowers (op U)).dpow n x) :=
      ((dividedPowerHom_appLE (m a.1) U a.2.1 (hU a h)).map_dpow hx).symm
    exact (hres.map_dpow (hmem x hx)).trans (s2.trans (s3.trans
      (he_apply a h ((Y.dividedPowers.dividedPowers (op U)).dpow n x)).symm))

attribute [local implicit_reducible] DividedPowerOpenPresentation.gluedMap

/-- The natural cocone from an open presentation to its glued scheme. -/
public noncomputable def DividedPowerOpenPresentation.cocone
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) : Cocone d.functor where
  pt := d.glued
  ι :=
    { app := d.gluedι
      naturality _ _ h := by
        apply DividedPowerScheme.Hom.ext
        exact (d.map_ι h).trans (Category.comp_id _).symm }

attribute [local implicit_reducible] DividedPowerOpenPresentation.cocone

/-- The glued divided power scheme is the colimit of the presentation's charts: a cocone is
descended on underlying schemes and the result is compatible with divided powers chart by
chart. -/
public noncomputable def DividedPowerOpenPresentation.isColimit
    {J : Type u} [Category.{u} J] [Quiver.IsThin J] {X : Scheme.{u}}
    (d : DividedPowerOpenPresentation J X) : IsColimit d.cocone where
  desc s := d.gluedMap s.pt
    (d.cover.isColimitCoconeOfLocallyDirected.desc
      (dividedPowerSchemeForget.mapCocone s)) s.ι.app
    (d.cover.isColimitCoconeOfLocallyDirected.fac (dividedPowerSchemeForget.mapCocone s))
  fac s i := by
    apply DividedPowerScheme.Hom.ext
    exact d.cover.isColimitCoconeOfLocallyDirected.fac
      (dividedPowerSchemeForget.mapCocone s) i
  uniq s m hm := by
    apply DividedPowerScheme.Hom.ext
    change m.hom = d.cover.isColimitCoconeOfLocallyDirected.desc
      (dividedPowerSchemeForget.mapCocone s)
    exact d.cover.isColimitCoconeOfLocallyDirected.uniq
      (dividedPowerSchemeForget.mapCocone s) m.hom
      (fun i => congrArg DividedPowerScheme.Hom.hom (hm i))

attribute [local implicit_reducible] DividedPowerOpenPresentation.isColimit

end Crystalline.DividedPowerScheme

end
