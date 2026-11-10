module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.IndQuasiAffineSections

/-!
# Flat affine base change of the functions on an intersection of opens

Consider a cartesian square of schemes whose right-hand column is the morphism of affine schemes
induced by a flat ring map `A ⟶ B`, and let `E` be an intersection of a nonempty family of
quasi-compact opens of the quasi-separated scheme `Y` at the bottom left. Then the functions on
the inverse image of `E` in `X` are obtained from the functions on `E` by base change along
`A ⟶ B`.

The proof presents `E` by a family of quasi-compact opens that is directed under reverse
inclusion, so that both sides are filtered colimits over that family: the functions on `E` are
the colimit of the functions on the members, the functions on the inverse image of `E` are the
colimit of the functions on their inverse images, and base change along a flat affine morphism
identifies the two colimit diagrams member by member.

## Main definitions

* `AlgebraicGeometry.toSectionsOnSubset` is the canonical map from the coordinate ring of an
  affine scheme to the functions on a subset of a scheme mapping to it.

## Main results

* `AlgebraicGeometry.sectionsRingOnSubset_preimage_iInter_iso_pushout` identifies the functions
  on the inverse image of the intersection with the tensor product obtained by base change.

## Implementation notes

The tensor product `Γ(E, 𝒪_Y|_E) ⊗_A B` is expressed as the pushout of commutative rings along
the two structure maps. The two equations characterizing the resulting isomorphism say that it is
the canonical base-change map: one gives its restriction to `B`, the other its restriction along
every open neighbourhood of the intersection.

Member by member the comparison is the canonical map
`Γ(Y, U) ⊗_A B ⟶ Γ(X, f⁻¹ U)`, which is `AlgebraicGeometry.pushoutSection`; flatness of `A ⟶ B`
and quasi-separatedness of `Y` make it an isomorphism. The index category of the presenting
family is used twice, once for `Y` and once for `X`, and the functor between the two copies is
final, which is what lets the colimit over the family of inverse images be computed over the
family itself.

## References

* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- The canonical map from the coordinate ring of an affine scheme to the functions on a subset
of a scheme mapping to that affine scheme. -/
noncomputable def toSectionsOnSubset {A : CommRingCat.{u}} {X : Scheme.{u}}
    (h : X ⟶ Scheme.Spec.obj (op A)) (E : Set X) : A ⟶ X.sectionsRingOnSubset E :=
  (Scheme.ΓSpecIso A).inv ≫ h.appTop ≫ X.restrictToSubset E

/-- For a cartesian square over a flat morphism of affine schemes and a quasi-compact open `U` of
a quasi-separated base, the canonical map `Γ(Y, U) ⊗_A B ⟶ Γ(X, f⁻¹ U)` is an isomorphism. -/
private theorem isIso_pushoutSection_specMap_of_isCompact
    {A B : CommRingCat.{u}} (φ : A ⟶ B) {X Y : Scheme.{u}}
    (g : X ⟶ Scheme.Spec.obj (op B)) (f : X ⟶ Y)
    (h : Y ⟶ Scheme.Spec.obj (op A))
    (H : IsPullback g f (Scheme.Spec.map φ.op) h)
    (U : Y.Opens) (hU : IsCompact (U : Set Y)) [QuasiSeparatedSpace Y]
    (hφ : φ.hom.Flat) :
    IsIso (AlgebraicGeometry.pushoutSection H.flip
      (show (⊤ : (Scheme.Spec.obj (op B)).Opens) ≤
        (Scheme.Spec.map φ.op) ⁻¹ᵁ (⊤ : (Scheme.Spec.obj (op A)).Opens) from by simp)
      (show U ≤ h ⁻¹ᵁ (⊤ : (Scheme.Spec.obj (op A)).Opens) from by simp)
      (show f ⁻¹ᵁ U = f ⁻¹ᵁ U ⊓
        (g ⁻¹ᵁ (⊤ : (Scheme.Spec.obj (op B)).Opens)) from by simp)) := by
  have : Flat (Scheme.Spec.map φ.op) := Flat.SpecMap_iff.2 hφ
  exact isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H.flip _ _ _
    (isAffineOpen_top _) (isAffineOpen_top _) hU
    ((isQuasiSeparated_univ (α := Y)).of_subset (Set.subset_univ _))

/-- Restricting the pullback of a global function to a subset through an open containing it is
the same as restricting it directly. -/
theorem Scheme.Hom.appLE_top_comp_restrictOpenToSubset {Z S : Scheme.{u}} (k : Z ⟶ S)
    (E : Set Z) (U : Z.Opens) (hE : E ⊆ U) (hU : U ≤ k ⁻¹ᵁ ⊤) :
    k.appLE ⊤ U hU ≫ Z.restrictOpenToSubset E U hE = k.appTop ≫ Z.restrictToSubset E := by
  change (k.appTop ≫ Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) ≫
      Z.restrictOpenToSubset E U hE = k.appTop ≫ Z.restrictOpenToSubset E ⊤ (Set.subset_univ E)
  rw [Category.assoc, Scheme.map_comp_restrictOpenToSubset E le_top hE]

/-- Restricting the pullback of a global function along an inclusion of opens. -/
private theorem appLE_top_eq_appLE_top_comp_map {Z S : Scheme.{u}} (k : Z ⟶ S) {U V : Z.Opens}
    (m : V ≤ U) (hU : U ≤ k ⁻¹ᵁ ⊤) (hV : V ≤ k ⁻¹ᵁ ⊤) :
    k.appLE ⊤ V hV = k.appLE ⊤ U hU ≫ Z.presheaf.map (homOfLE m).op :=
  (Scheme.Hom.appLE_map ..).symm

/-- The functor from the reverse-inclusion index of a family of opens to the reverse-inclusion
index of the family of their inverse images. -/
def intersectionIndexPreimage {X Y : Scheme.{u}} (f : X ⟶ Y) {J : Type u} (W : J → Y.Opens) :
    intersectionIndex W ⥤ intersectionIndex (fun s ↦ f ⁻¹ᵁ W s) where
  obj s := ⟨s.val⟩
  map m := homOfLE fun _ hx ↦ m.le hx
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- For a family of opens directed under reverse inclusion, passing to inverse images is a final
functor of reverse-inclusion indices. -/
theorem final_intersectionIndexPreimage {X Y : Scheme.{u}} (f : X ⟶ Y) {J : Type u}
    (W : J → Y.Opens) (hW : ∀ s t, ∃ r, (W r : Set Y) ⊆ W s ∩ W t) :
    (intersectionIndexPreimage f W).Final := by
  refine ⟨fun j ↦ ?_⟩
  let C := StructuredArrow j (intersectionIndexPreimage f W)
  have : IsFilteredOrEmpty C :=
    { cocone_objs := by
        intro x y
        obtain ⟨r, hr⟩ := hW x.right.val y.right.val
        let fx : x.right ⟶ (⟨r⟩ : intersectionIndex W) := homOfLE (Set.subset_inter_iff.mp hr).1
        let fy : y.right ⟶ (⟨r⟩ : intersectionIndex W) := homOfLE (Set.subset_inter_iff.mp hr).2
        exact ⟨StructuredArrow.mk (x.hom ≫ (intersectionIndexPreimage f W).map fx),
          StructuredArrow.homMk fx, StructuredArrow.homMk fy, trivial⟩
      cocone_maps := fun _ y _ _ ↦
        ⟨y, 𝟙 _, StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)⟩ }
  have : Nonempty C := ⟨StructuredArrow.mk (Y := (⟨j.val⟩ : intersectionIndex W)) (𝟙 j)⟩
  have : IsFiltered C := IsFiltered.mk
  exact IsFiltered.isConnected C

section pushoutIsoOfIsoSpan

variable {C : Type*} [Category C] {A A' B B' Z : C} (eA : A ≅ A') (eB : B ≅ B') (a : A' ⟶ Z)
  (ψ : A' ⟶ B') (φ : A ⟶ B) (hψ : eA.hom ≫ ψ = φ ≫ eB.hom) [HasPushout (eA.hom ≫ a) φ]
  [HasPushout a ψ]

/-- Pushouts of two spans whose sources are identified compatibly by isomorphisms agree. -/
noncomputable def pushoutIsoOfIsoSpan : pushout (eA.hom ≫ a) φ ≅ pushout a ψ where
  hom := pushout.desc (pushout.inl a ψ) (eB.hom ≫ pushout.inr a ψ)
    (by rw [Category.assoc, pushout.condition, reassoc_of% hψ])
  inv := pushout.desc (pushout.inl (eA.hom ≫ a) φ) (eB.inv ≫ pushout.inr (eA.hom ≫ a) φ) (by
    have hψ' : eA.inv ≫ φ = ψ ≫ eB.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, hψ]
      simp
    rw [← reassoc_of% hψ', ← pushout.condition]
    simp)
  hom_inv_id := by
    apply pushout.hom_ext
    · simp only [pushout.inl_desc_assoc, pushout.inl_desc, Category.comp_id]
    · simp only [pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc,
        Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply pushout.hom_ext
    · simp only [pushout.inl_desc_assoc, pushout.inl_desc, Category.comp_id]
    · simp only [pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc,
        Iso.inv_hom_id_assoc, Category.comp_id]

/-- The isomorphism `pushoutIsoOfIsoSpan` carries the first coprojection to the first
coprojection. -/
theorem inl_pushoutIsoOfIsoSpan_hom :
    pushout.inl (eA.hom ≫ a) φ ≫ (pushoutIsoOfIsoSpan eA eB a ψ φ hψ).hom = pushout.inl a ψ :=
  pushout.inl_desc _ _ _

/-- The isomorphism `pushoutIsoOfIsoSpan` carries the second coprojection to the composite of
`eB.hom` with the second coprojection. -/
theorem inr_pushoutIsoOfIsoSpan_hom :
    pushout.inr (eA.hom ≫ a) φ ≫ (pushoutIsoOfIsoSpan eA eB a ψ φ hψ).hom =
      eB.hom ≫ pushout.inr a ψ :=
  pushout.inr_desc _ _ _

end pushoutIsoOfIsoSpan

/-- **Stacks Project, Tag 0APJ.** In a cartesian square of schemes over the affine schemes
`Spec B ⟶ Spec A`, where `A ⟶ B` is flat, formation of sections over a nonempty intersection of
quasi-compact opens commutes with base change. -/
@[stacks 0APJ]
theorem sectionsRingOnSubset_preimage_iInter_iso_pushout
    {A B : CommRingCat.{u}} (φ : A ⟶ B) {X Y : Scheme.{u}}
    (g : X ⟶ Scheme.Spec.obj (op B)) (f : X ⟶ Y)
    (h : Y ⟶ Scheme.Spec.obj (op A))
    (H : IsPullback g f (Scheme.Spec.map φ.op) h)
    {ι : Type v} [Nonempty ι] (V : ι → Y.Opens)
    (hV : ∀ i, IsCompact (V i : Set Y)) [QuasiSeparatedSpace Y]
    (hφ : φ.hom.Flat) :
    ∃ e : pushout (toSectionsOnSubset h (⋂ i, (V i : Set Y))) φ ≅
        X.sectionsRingOnSubset (f ⁻¹' (⋂ i, (V i : Set Y))),
      (pushout.inr _ _ ≫ e.hom =
        toSectionsOnSubset g (f ⁻¹' (⋂ i, (V i : Set Y)))) ∧
      (∀ (U : Y.Opens) (hU : (⋂ i, (V i : Set Y)) ⊆ U),
        Y.restrictOpenToSubset (⋂ i, (V i : Set Y)) U hU ≫
            pushout.inl _ _ ≫ e.hom =
          f.appLE U (f ⁻¹ᵁ U) le_rfl ≫
            X.restrictOpenToSubset (f ⁻¹' (⋂ i, (V i : Set Y))) (f ⁻¹ᵁ U) (by
              intro x hx
              exact Set.mem_preimage.mpr (hU (Set.mem_preimage.mp hx)))) := by
  classical
  let E : Set Y := ⋂ i, (V i : Set Y)
  obtain ⟨J, hJ, W, hWcompact, hWdir, hE⟩ :=
    exists_directed_quasiCompact_open_presentation V hV E rfl
  have : Nonempty J := hJ
  have : QuasiSeparated f :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) H (by infer_instance)
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiCompact f :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) H (by infer_instance)
  have hWprecompact (s : J) : IsCompact (f ⁻¹' (W s : Set Y)) :=
    QuasiCompact.isCompact_preimage (f := f) _ (W s).isOpen (hWcompact s)
  have hWdirX (s t : J) :
      ∃ r, ((f ⁻¹ᵁ W r : X.Opens) : Set X) ⊆ (f ⁻¹ᵁ W s) ∩ (f ⁻¹ᵁ W t) := by
    obtain ⟨r, hr⟩ := hWdir s t
    exact ⟨r, fun x hx ↦ ⟨(hr hx).1, (hr hx).2⟩⟩
  let Eₓ : Set X := f ⁻¹' E
  have hEₓ : Eₓ = ⋂ s : J, (f ⁻¹ᵁ W s : Set X) := by
    ext x
    simp only [Eₓ, Set.mem_preimage, Set.mem_iInter]
    rw [hE]
    simp
  let JY := intersectionIndex W
  let JX := intersectionIndex (fun s : J ↦ f ⁻¹ᵁ W s)
  have : Nonempty JY := inferInstanceAs (Nonempty (intersectionIndex W))
  have : Nonempty JX := inferInstanceAs (Nonempty (intersectionIndex _))
  have : IsFiltered JY := filtered_intersectionIndex W hWdir
  have : IsConnected JY := IsFiltered.isConnected JY
  have : IsFiltered JX := filtered_intersectionIndex _ hWdirX
  have : IsConnected JX := IsFiltered.isConnected JX
  let FY := Y.sectionsRingDiagram W
  let FX := X.sectionsRingDiagram (fun s ↦ f ⁻¹ᵁ W s)
  let wY (s : JY) : Y.Opens := W s.val
  let wX (s : JX) : X.Opens := f ⁻¹ᵁ W s.val
  let ψ : Γ(Scheme.Spec.obj (op A), ⊤) ⟶ Γ(Scheme.Spec.obj (op B), ⊤) :=
    (Scheme.Spec.map φ.op).appLE ⊤ ⊤ (by simp)
  let a (s : JY) : Γ(Scheme.Spec.obj (op A), ⊤) ⟶ FY.obj s :=
    h.appLE ⊤ (wY s) (by simp)
  have hXtopX : ∀ s : JX, wX s ≤ g ⁻¹ᵁ (⊤ : (Scheme.Spec.obj (op B)).Opens) :=
    fun _ ↦ by simp
  let b (s : JX) : Γ(Scheme.Spec.obj (op B), ⊤) ⟶ FX.obj s :=
    g.appLE ⊤ (wX s) (hXtopX s)
  let sA : (Functor.const JY).obj Γ(Scheme.Spec.obj (op A), ⊤) ⟶ FY :=
    { app := a
      naturality := by
        intro s t m
        exact (Category.id_comp _).trans (appLE_top_eq_appLE_top_comp_map h m.le _ _) }
  let sB : (Functor.const JX).obj Γ(Scheme.Spec.obj (op B), ⊤) ⟶ FX :=
    { app := b
      naturality := by
        intro s t m
        exact (Category.id_comp _).trans (appLE_top_eq_appLE_top_comp_map g m.le _ _) }
  let DY := Under.lift FY sA
  let PY := DY ⋙ Under.pushout ψ ⋙ Under.forget _
  let inlP : ∀ s : JY, FY.obj s ⟶ PY.obj s := fun s ↦ pushout.inl (DY.obj s).hom ψ
  let inrP : ∀ s : JY, Γ(Scheme.Spec.obj (op B), ⊤) ⟶ PY.obj s :=
    fun s ↦ pushout.inr (DY.obj s).hom ψ
  have homExtP : ∀ {s : JY} {R : CommRingCat.{u}} {k l : PY.obj s ⟶ R},
      inlP s ≫ k = inlP s ≫ l → inrP s ≫ k = inrP s ≫ l → k = l :=
    fun h₀ h₁ ↦ pushout.hom_ext h₀ h₁
  let L : JY ⥤ JX := intersectionIndexPreimage f W
  have hLpre (s : JY) : wX (L.obj s) = f ⁻¹ᵁ wY s := rfl
  let fLE : ∀ s : JY, FY.obj s ⟶ (L ⋙ FX).obj s :=
    fun s ↦ f.appLE (wY s) (wX (L.obj s)) (hLpre s).le
  let gLE : ∀ s : JY, Γ(Scheme.Spec.obj (op B), ⊤) ⟶ (L ⋙ FX).obj s := fun s ↦ b (L.obj s)
  have hfLEnat : ∀ {s t : JY} (m : s ⟶ t), FY.map m ≫ fLE t = fLE s ≫ (L ⋙ FX).map m := by
    intro s t m
    change Y.presheaf.map (homOfLE m.le).op ≫ f.appLE (wY t) (wX (L.obj t)) (hLpre t).le =
      f.appLE (wY s) (wX (L.obj s)) (hLpre s).le ≫
        X.presheaf.map (homOfLE (L.map m).le).op
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  have hgLEnat : ∀ {s t : JY} (m : s ⟶ t), gLE t = gLE s ≫ (L ⋙ FX).map m :=
    fun m ↦ appLE_top_eq_appLE_top_comp_map g (L.map m).le _ _
  let p (s : JY) : PY.obj s ⟶ (L ⋙ FX).obj s :=
    pushoutSection H.flip
      (show (⊤ : (Scheme.Spec.obj (op B)).Opens) ≤
        (Scheme.Spec.map φ.op) ⁻¹ᵁ (⊤ : (Scheme.Spec.obj (op A)).Opens) from by simp)
      (show wY s ≤ h ⁻¹ᵁ (⊤ : (Scheme.Spec.obj (op A)).Opens) from by simp)
      (show wX (L.obj s) = wX (L.obj s) ⊓
        (g ⁻¹ᵁ (⊤ : (Scheme.Spec.obj (op B)).Opens)) from by simp)
  have hpIso (s : JY) : IsIso (p s) := by
    dsimp [p, PY, DY]
    exact isIso_pushoutSection_specMap_of_isCompact φ g f h H (wY s) (hWcompact s.val) hφ
  have hpInl (s : JY) : inlP s ≫ p s = fLE s := by
    dsimp [inlP, fLE, p, a, ψ, wY, wX, L, AlgebraicGeometry.pushoutSection,
      Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact pushout.inl_desc _ _ _
  have hpInr (s : JY) : inrP s ≫ p s = gLE s := by
    dsimp [inrP, gLE, p, a, ψ, wY, wX, L, AlgebraicGeometry.pushoutSection,
      Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact pushout.inr_desc _ _ _
  let hpNat : PY ⟶ L ⋙ FX :=
    { app := p
      naturality := by
        intro s t m
        have hinl : inlP s ≫ PY.map m = FY.map m ≫ inlP t := by
          change pushout.inl (DY.obj s).hom ψ ≫
              Under.Hom.right ((Under.pushout ψ).map (DY.map m)) =
            Under.Hom.right (DY.map m) ≫ pushout.inl (DY.obj t).hom ψ
          dsimp [Under.pushout, DY]
          simp only [Under.homMk_right, Under.lift_map]
          exact pushout.inl_desc _ _ _
        have hinr : inrP s ≫ PY.map m = inrP t := by
          change pushout.inr (DY.obj s).hom ψ ≫
              Under.Hom.right ((Under.pushout ψ).map (DY.map m)) =
            pushout.inr (DY.obj t).hom ψ
          dsimp [Under.pushout, DY]
          simp only [Under.homMk_right, Under.lift_map]
          exact pushout.inr_desc _ _ _
        refine homExtP ?_ ?_
        · rw [reassoc_of% hinl, hpInl t, hfLEnat m, ← hpInl s, Category.assoc]
        · rw [reassoc_of% hinr, hpInr t, hgLEnat m, ← hpInr s, Category.assoc] }
  let α : PY ≅ L ⋙ FX := NatIso.ofComponents (fun s ↦ have := hpIso s; asIso (p s)) (by
    intro s t m
    have happ (i : JY) : hpNat.app i = p i := rfl
    simpa only [asIso_hom, happ] using hpNat.naturality m)
  obtain ⟨eY, heY⟩ := colimit_sectionsRing_iso_sectionsRingOnSubset Y W hWcompact hWdir E hE
  obtain ⟨eX, heX⟩ := colimit_sectionsRing_iso_sectionsRingOnSubset X
    (fun s ↦ f ⁻¹ᵁ W s) hWprecompact hWdirX Eₓ hEₓ
  let aE : Γ(Scheme.Spec.obj (op A), ⊤) ⟶ Y.sectionsRingOnSubset E :=
    h.appTop ≫ Y.restrictToSubset E
  let bE : Γ(Scheme.Spec.obj (op B), ⊤) ⟶ X.sectionsRingOnSubset Eₓ :=
    g.appTop ≫ X.restrictToSubset Eₓ
  let cY : Cocone FY := (colimit.cocone FY).extend eY.hom
  let hcY : IsColimit cY := IsColimit.extendIso _ (colimit.isColimit FY)
  let cX : Cocone FX := (colimit.cocone FX).extend eX.hom
  let hcX : IsColimit cX := IsColimit.extendIso _ (colimit.isColimit FX)
  have hEsub (t : J) : E ⊆ W t := by
    rw [hE]
    exact Set.iInter_subset _ t
  have hEₓsub (t : J) : Eₓ ⊆ f ⁻¹ᵁ W t := fun _ hx ↦ hEsub t hx
  have hcYι (s : JY) : cY.ι.app s = Y.stageToSubset W E hEsub s := heY s
  have hcXι (t : JX) : cX.ι.app t = X.stageToSubset (fun u ↦ f ⁻¹ᵁ W u) Eₓ hEₓsub t := heX t
  have hpY (s : JY) : a s ≫ cY.ι.app s = aE := by
    rw [hcYι s]
    exact Scheme.Hom.appLE_top_comp_restrictOpenToSubset h E (W s.val) (hEsub s.val) _
  let cYUnder : Cocone DY := Under.liftCocone FY sA cY aE hpY
  have hcYUnder : IsColimit cYUnder := Under.isColimitLiftCocone FY sA cY aE hpY hcY
  let cPUnder := (Under.pushout ψ).mapCocone cYUnder
  have hcPUnder : IsColimit cPUnder := isColimitOfPreserves _ hcYUnder
  let cP : Cocone PY := (Under.forget _).mapCocone cPUnder
  have hcP : IsColimit cP := isColimitOfPreserves _ hcPUnder
  have hLfinal : L.Final := final_intersectionIndexPreimage f W hWdir
  let cXwhisker : Cocone (L ⋙ FX) := cX.whisker L
  have hcXwhisker : IsColimit cXwhisker :=
    (Functor.Final.isColimitWhiskerEquiv L cX).symm hcX
  let cXsrc : Cocone PY := (Cocone.precompose α.hom).obj cXwhisker
  have hcXsrc : IsColimit cXsrc :=
    (IsColimit.equivOfNatIsoOfIso α.symm cXwhisker cXsrc (Iso.refl _)).toFun hcXwhisker
  let e0 : cP.pt ≅ cXsrc.pt := IsColimit.coconePointsIsoOfNatIso hcP hcXsrc (Iso.refl _)
  have hψ' : (Scheme.ΓSpecIso A).hom ≫ φ = ψ ≫ (Scheme.ΓSpecIso B).hom := by
    simpa [ψ, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      (Scheme.ΓSpecIso_naturality φ).symm
  have hψ : (Scheme.ΓSpecIso A).inv ≫ ψ = φ ≫ (Scheme.ΓSpecIso B).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, hψ']
  let qIso : pushout (toSectionsOnSubset h E) φ ≅ pushout aE ψ :=
    pushoutIsoOfIsoSpan (Scheme.ΓSpecIso A).symm (Scheme.ΓSpecIso B).symm aE ψ φ hψ
  let e : pushout (toSectionsOnSubset h E) φ ≅ X.sectionsRingOnSubset Eₓ := qIso ≪≫ e0
  have hPInr (s : JY) : inrP s ≫ cP.ι.app s = pushout.inr aE ψ := by
    change pushout.inr (DY.obj s).hom ψ ≫
      Under.Hom.right ((Under.pushout ψ).map (cYUnder.ι.app s)) = pushout.inr aE ψ
    dsimp [Under.pushout]
    exact pushout.inr_desc _ _ _
  have hPInl (s : JY) :
      inlP s ≫ cP.ι.app s = Y.stageToSubset W E hEsub s ≫ pushout.inl aE ψ := by
    rw [← hcYι s]
    exact pushout.inl_desc _ _ _
  have he0app (s : JY) : cP.ι.app s ≫ e0.hom = p s ≫ cX.ι.app (L.obj s) := by
    simp [e0, cXsrc, cXwhisker, α]
  have hbStage (s : JX) :
      b s ≫ X.stageToSubset (fun t ↦ f ⁻¹ᵁ W t) Eₓ hEₓsub s = bE :=
    Scheme.Hom.appLE_top_comp_restrictOpenToSubset g Eₓ (wX s) (hEₓsub s.val) _
  have hBglobal : pushout.inr aE ψ ≫ e0.hom = bE := by
    let s : JY := Classical.choice (inferInstance : Nonempty JY)
    have h1 : pushout.inr aE ψ ≫ e0.hom = (inrP s ≫ cP.ι.app s) ≫ e0.hom :=
      congrArg (fun k ↦ k ≫ e0.hom) (hPInr s).symm
    have h2 : (inrP s ≫ cP.ι.app s) ≫ e0.hom = (inrP s ≫ p s) ≫ cX.ι.app (L.obj s) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun k ↦ inrP s ≫ k) (he0app s)).trans (Category.assoc _ _ _).symm)
    have h3 : (inrP s ≫ p s) ≫ cX.ι.app (L.obj s) = bE := by
      rw [hpInr s, hcXι (L.obj s)]
      exact hbStage (L.obj s)
    exact h1.trans (h2.trans h3)
  refine ⟨e, ?_, ?_⟩
  · have hqInr : pushout.inr (toSectionsOnSubset h E) φ ≫ qIso.hom =
        (Scheme.ΓSpecIso B).inv ≫ pushout.inr aE ψ :=
      inr_pushoutIsoOfIsoSpan_hom (Scheme.ΓSpecIso A).symm (Scheme.ΓSpecIso B).symm aE ψ φ hψ
    calc
      pushout.inr (toSectionsOnSubset h E) φ ≫ e.hom =
          (pushout.inr (toSectionsOnSubset h E) φ ≫ qIso.hom) ≫ e0.hom :=
            (Category.assoc _ _ _).symm
      _ = ((Scheme.ΓSpecIso B).inv ≫ pushout.inr aE ψ) ≫ e0.hom :=
            congrArg (fun k ↦ k ≫ e0.hom) hqInr
      _ = (Scheme.ΓSpecIso B).inv ≫ pushout.inr aE ψ ≫ e0.hom := Category.assoc _ _ _
      _ = (Scheme.ΓSpecIso B).inv ≫ bE :=
            congrArg (fun k ↦ (Scheme.ΓSpecIso B).inv ≫ k) hBglobal
      _ = toSectionsOnSubset g Eₓ := rfl
  · intro U hU
    obtain ⟨i, hi⟩ := exists_opens_le_of_iInter_subset W hWcompact hWdir E hE U hU
    let s : JY := ⟨i⟩
    have hsi : wY s ≤ U := hi
    have hXstage : Eₓ ⊆ wX (L.obj s) := hEₓsub s.val
    have hpre : wX (L.obj s) ≤ f ⁻¹ᵁ U := f.preimage_mono hsi
    let r : Γ(Y, U) ⟶ Γ(Y, wY s) :=
      Y.presheaf.map (homOfLE hsi).op
    have hr : r ≫ Y.stageToSubset W E hEsub s =
        Y.restrictOpenToSubset E U hU := by
      dsimp [r]
      exact Scheme.map_comp_restrictOpenToSubset E hsi (hEsub s.val)
    have hfactor :
        f.appLE U (f ⁻¹ᵁ U) le_rfl ≫
          X.restrictOpenToSubset Eₓ (f ⁻¹ᵁ U) (by
            intro x hx
            apply hU
            change f x ∈ E at hx
            exact hx) =
        r ≫ f.appLE (wY s) (wX (L.obj s)) (hLpre s).le ≫
          X.stageToSubset (fun t ↦ f ⁻¹ᵁ W t) Eₓ hEₓsub (L.obj s) := by
      calc
        _ = (f.appLE U (f ⁻¹ᵁ U) le_rfl ≫ X.presheaf.map (homOfLE hpre).op) ≫
              X.restrictOpenToSubset Eₓ (wX (L.obj s)) hXstage := by
                rw [Category.assoc,
                  Scheme.map_comp_restrictOpenToSubset Eₓ hpre hXstage]
        _ = f.appLE U (wX (L.obj s)) hpre ≫
              X.restrictOpenToSubset Eₓ (wX (L.obj s)) hXstage := by
                rw [Scheme.Hom.appLE_map (f := f) (U := U) (V := f ⁻¹ᵁ U)
                  (V' := wX (L.obj s)) (e := le_rfl) (i := (homOfLE hpre).op)]
        _ = r ≫ f.appLE (wY s) (wX (L.obj s)) (hLpre s).le ≫
              X.restrictOpenToSubset Eₓ (wX (L.obj s)) hXstage := by
                simp [r]
        _ = r ≫ f.appLE (wY s) (wX (L.obj s)) (hLpre s).le ≫
              X.stageToSubset (fun t ↦ f ⁻¹ᵁ W t) Eₓ hEₓsub (L.obj s) := rfl
    have hqInl : pushout.inl (toSectionsOnSubset h E) φ ≫ qIso.hom = pushout.inl aE ψ :=
      inl_pushoutIsoOfIsoSpan_hom (Scheme.ΓSpecIso A).symm (Scheme.ΓSpecIso B).symm aE ψ φ hψ
    have hql : pushout.inl (toSectionsOnSubset h E) φ ≫ e.hom =
        pushout.inl aE ψ ≫ e0.hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ e0.hom) hqInl)
    have step1 : Y.restrictOpenToSubset E U hU ≫
          pushout.inl (toSectionsOnSubset h E) φ ≫ e.hom =
        r ≫ inlP s ≫ cP.ι.app s ≫ e0.hom :=
      calc
        Y.restrictOpenToSubset E U hU ≫
            pushout.inl (toSectionsOnSubset h E) φ ≫ e.hom =
            Y.restrictOpenToSubset E U hU ≫ pushout.inl aE ψ ≫ e0.hom :=
              congrArg (fun k ↦ Y.restrictOpenToSubset E U hU ≫ k) hql
        _ = (r ≫ Y.stageToSubset W E hEsub s) ≫ pushout.inl aE ψ ≫ e0.hom :=
              congrArg (fun k ↦ k ≫ pushout.inl aE ψ ≫ e0.hom) hr.symm
        _ = r ≫ (Y.stageToSubset W E hEsub s ≫ pushout.inl aE ψ) ≫ e0.hom :=
              (Category.assoc _ _ _).trans
                (congrArg (fun k ↦ r ≫ k) (Category.assoc _ _ _).symm)
        _ = r ≫ (inlP s ≫ cP.ι.app s) ≫ e0.hom :=
              congrArg (fun k ↦ r ≫ k ≫ e0.hom) (hPInl s).symm
        _ = r ≫ inlP s ≫ cP.ι.app s ≫ e0.hom :=
              congrArg (fun k ↦ r ≫ k) (Category.assoc _ _ _)
    have step2 : r ≫ inlP s ≫ cP.ι.app s ≫ e0.hom =
        r ≫ fLE s ≫ X.stageToSubset (fun t ↦ f ⁻¹ᵁ W t) Eₓ hEₓsub (L.obj s) :=
      calc
        r ≫ inlP s ≫ cP.ι.app s ≫ e0.hom =
            r ≫ inlP s ≫ p s ≫ cX.ι.app (L.obj s) :=
              congrArg (fun k ↦ r ≫ inlP s ≫ k) (he0app s)
        _ = r ≫ (inlP s ≫ p s) ≫ cX.ι.app (L.obj s) :=
              congrArg (fun k ↦ r ≫ k) (Category.assoc _ _ _).symm
        _ = r ≫ fLE s ≫ cX.ι.app (L.obj s) :=
              congrArg (fun k ↦ r ≫ k ≫ cX.ι.app (L.obj s)) (hpInl s)
        _ = r ≫ fLE s ≫ X.stageToSubset (fun t ↦ f ⁻¹ᵁ W t) Eₓ hEₓsub (L.obj s) :=
              congrArg (fun k ↦ r ≫ fLE s ≫ k) (hcXι (L.obj s))
    exact step1.trans (step2.trans hfactor.symm)

end AlgebraicGeometry

end
