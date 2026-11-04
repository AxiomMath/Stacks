module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Maps.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalExtensionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalUniqueness
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus

/-!
# Birational morphisms are isomorphisms on dense opens

A birational morphism between schemes with finitely many irreducible components restricts to an
isomorphism between dense open subschemes if it is locally of finite type with reduced target,
or if it is locally of finite presentation. Over a base, a compatible birational morphism under
the same hypotheses makes the schemes birational over that base.

## Main results

* `AlgebraicGeometry.exists_dense_opens_isIso_resLE_of_isBirational`: a birational morphism
  satisfying either hypothesis restricts to an isomorphism `f.resLE V U hUV` between dense opens
  `U` of the source and `V` of the target.
* `AlgebraicGeometry.birationalOver_of_isBirational`: a birational morphism over a base satisfying
  either hypothesis makes the schemes birational over that base.

## References

* [Stacks Project, Tag 0BAC](https://stacks.math.columbia.edu/tag/0BAC)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry


private lemma exists_pairwise_disjoint_generic_opens (T : Type*) [TopologicalSpace T]
    [T0Space T] [Finite (irreducibleComponents T)] :
    ∃ V : genericPoints T → Opens T,
      (∀ x, x.1 ∈ V x) ∧ Pairwise (fun x y ↦ Disjoint (V x) (V y)) := by
  classical
  let C := irreducibleComponents T
  have hC : C.Finite := Set.toFinite _
  let V : genericPoints T → Opens T := fun x ↦
    ⟨(⋃₀ (C \ {(genericPoints.component x).1}))ᶜ, by
      rw [Set.sUnion_eq_biUnion]
      exact (hC.sdiff.isClosed_biUnion fun Z hZ ↦
        isClosed_of_mem_irreducibleComponents Z hZ.1).isOpen_compl⟩
  have hV (x : genericPoints T) : (V x : Set T) ⊆ (genericPoints.component x).1 :=
    subset_closure.trans (closure_sUnion_irreducibleComponents_sdiff_singleton hC
      _ (genericPoints.component x).2).le
  refine ⟨V, ?_, ?_⟩
  · intro x
    apply ((genericPoints.isGenericPoint x).mem_open_set_iff (V x).2).mpr
    have hn : (V x : Set T).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro he
      have hc := closure_sUnion_irreducibleComponents_sdiff_singleton hC
        _ (genericPoints.component x).2
      change closure (V x : Set T) = _ at hc
      rw [he, closure_empty] at hc
      exact (genericPoints.component x).2.1.nonempty.ne_empty hc.symm
    exact hn.mono (fun z hz ↦ ⟨hV x hz, hz⟩)
  · intro x y hxy
    rw [← Opens.coe_disjoint]
    exact Set.disjoint_left.mpr fun z hz hz' ↦ hz (Set.mem_sUnion.mpr
      ⟨_, ⟨(genericPoints.component y).2,
        fun e ↦ hxy (genericPoints.component_injective (Subtype.ext e.symm))⟩, hV y hz'⟩)

private lemma exists_dense_opens_of_isOpenImmersion_at_genericPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Finite (irreducibleComponents Y)]
    (hf : Set.BijOn f (genericPoints X) (genericPoints Y))
    (hlocal : ∀ x : genericPoints X,
      ∃ U : X.Opens, x.1 ∈ U ∧ IsOpenImmersion (U.ι ≫ f)) :
    ∃ (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V),
      Dense (U : Set X) ∧ Dense (V : Set Y) ∧ IsIso (f.resLE V U hUV) := by
  classical
  obtain ⟨V, hV, hdisj⟩ := exists_pairwise_disjoint_generic_opens Y
  choose A hA hAf using hlocal
  let j : genericPoints X → genericPoints Y := fun x ↦ ⟨f x.1, hf.mapsTo x.2⟩
  let W : genericPoints X → X.Opens := fun x ↦ A x ⊓ f ⁻¹ᵁ V (j x)
  let U : X.Opens := ⨆ x, W x
  have hWU (x) : W x ≤ U := le_iSup W x
  have hd (T : Scheme.{u}) : Dense (genericPoints T) :=
    dense_iff_closure_eq.mpr genericPoints.closure
  have hW (x) : x.1 ∈ W x := ⟨hA x, hV (j x)⟩
  have hWf (x) : IsOpenImmersion ((W x).ι ≫ f) := by
    have he : (W x).ι ≫ f = X.homOfLE (show W x ≤ A x from inf_le_left) ≫
        ((A x).ι ≫ f) := by simp
    rw [he]; infer_instance
  have hfU : Function.Injective (U.ι ≫ f) := by
    intro a b hab
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp a.2
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp b.2
    have hj : j i = j k := by
      by_contra hne
      exact Set.disjoint_left.mp (Opens.coe_disjoint.mpr (hdisj hne)) hi.2 (by
        change f a.1 = f b.1 at hab
        rw [hab]
        exact hk.2)
    obtain rfl : i = k := Subtype.ext (hf.injOn i.2 k.2 (congrArg Subtype.val hj))
    exact Subtype.ext <| congrArg (W i).ι (((W i).ι ≫ f).isOpenEmbedding.injective
      (show ((W i).ι ≫ f) ⟨a.1, hi⟩ = ((W i).ι ≫ f) ⟨b.1, hk⟩ from hab))
  have hopen : IsOpenImmersion (U.ι ≫ f) := by
    apply IsOpenImmersion.of_forall_source_exists _ hfU
    intro a
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp a.2
    refine ⟨(W i).toScheme, X.homOfLE (hWU i), inferInstance, ?_, ?_⟩
    · exact ⟨⟨a.1, hi⟩, Subtype.ext (by simp)⟩
    · simpa using hWf i
  let V' := (U.ι ≫ f).opensRange
  have hUV : U ≤ f ⁻¹ᵁ V' := fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
  refine ⟨U, V', hUV, ?_, ?_, ?_⟩
  · exact (hd X).mono
      (fun x hx ↦ hWU ⟨x, hx⟩ (hW ⟨x, hx⟩))
  · apply (hd Y).mono
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hf.surjOn hy
    exact ⟨⟨x, hWU ⟨x, hx⟩ (hW ⟨x, hx⟩)⟩, rfl⟩
  · have : IsOpenImmersion (f.resLE V' U hUV ≫ V'.ι) := by simpa
    have : IsOpenImmersion (f.resLE V' U hUV) := IsOpenImmersion.of_comp _ V'.ι
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    apply top_unique
    intro y _
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext ((f.coe_resLE_apply hUV x).trans hx)⟩

/-- A birational morphism between schemes with finitely many irreducible components is an
isomorphism between dense open subschemes, provided that it is locally of finite type with reduced
target or locally of finite presentation. -/
@[stacks 0BAC "dense open isomorphism"]
public theorem exists_dense_opens_isIso_resLE_of_isBirational
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (hf : IsBirational f)
    (hfin : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V),
      Dense (U : Set X) ∧ Dense (V : Set Y) ∧ IsIso (f.resLE V U hUV) := by
  apply exists_dense_opens_of_isOpenImmersion_at_genericPoints f hf.bijOn
  intro x
  let y : Y := f x.1
  have hxy : f x.1 = y := rfl
  let s : Y := (𝟙 Y) y
  have hxs : (𝟙 Y) y = s := rfl
  have hys : f x.1 = s := rfl
  have : IsIso (f.stalkMap x.1) := hf.isIso_stalkMap x.1 x.2
  let theta : CommRingCat.of (Y.presheaf.stalk s) ⟶ CommRingCat.of (X.presheaf.stalk x.1) :=
    eqToHom (congrArg (fun z : Y ↦ Y.presheaf.stalk z) hys).symm ≫ f.stalkMap x.1
  let psi : CommRingCat.of (Y.presheaf.stalk s) ⟶ CommRingCat.of (Y.presheaf.stalk y) :=
    eqToHom (congrArg (fun z : Y ↦ Y.presheaf.stalk z) hxs).symm ≫
      Scheme.Hom.stalkMap (𝟙 Y) y
  have : IsIso theta := by
    dsimp [theta]
    infer_instance
  let phi : X.presheaf.stalk x.1 →+* Y.presheaf.stalk y := (inv theta ≫ psi).hom
  have hphi : IsLocalHom phi := by
    dsimp [phi]
    infer_instance
  have hphiS : phi.comp
      ((f.stalkMap x.1).hom.comp
        (eqToHom (congrArg (fun z : Y ↦ Y.presheaf.stalk z) hys).symm).hom) =
      (Scheme.Hom.stalkMap (𝟙 Y) y).hom.comp
        (eqToHom (congrArg (fun z : Y ↦ Y.presheaf.stalk z) hxs).symm).hom := by
    show (inv theta ≫ psi).hom.comp theta.hom = psi.hom
    rw [← CommRingCat.hom_comp]
    simp
  have hext : ∃ (U : Y.Opens) (hyU : y ∈ U) (g : (U : Scheme) ⟶ X)
      (_ : g ≫ f = U.ι) (hgx : g ⟨y, hyU⟩ = x.1),
      ((U.stalkIso ⟨y, hyU⟩).hom.hom.comp
          ((g.stalkMap ⟨y, hyU⟩).hom.comp
            (eqToHom (congrArg (fun z : X ↦ X.presheaf.stalk z) hgx).symm).hom)) = phi := by
    rcases hfin with htype | hpres
    · exact exists_open_morphism_inducing_localHom_of_isReduced
        (𝟙 Y) f s y x.1 hxs hys phi hphi hphiS htype.1 htype.2 (Set.toFinite _)
    · exact exists_open_morphism_inducing_localHom_of_locallyOfFinitePresentation
        (𝟙 Y) f s y x.1 hxs hys phi hphi hphiS hpres
  obtain ⟨U, hyU, g, hgf, hgx, -⟩ := hext
  let D : X.Opens := f ⁻¹ᵁ U
  have hxD : x.1 ∈ D := hyU
  let z : D.toScheme := ⟨x.1, hxD⟩
  let a : D.toScheme ⟶ U.toScheme := f.resLE U D le_rfl
  let k : D.toScheme ⟶ X := a ≫ g
  have hkbase : k ≫ f = D.ι ≫ f := by
    dsimp [k, a]
    rw [Category.assoc, hgf, Scheme.Hom.resLE_comp_ι]
  have hfx : D.ι z = x.1 := rfl
  have hgx' : k z = x.1 := by
    show g (a z) = x.1
    have haz : a z = ⟨y, hyU⟩ := by
      apply Subtype.ext
      show ((Scheme.Hom.resLE f U D le_rfl) z).1 = y
      rw [Scheme.Hom.coe_resLE_apply]
    rw [haz, hgx]
  obtain ⟨W, hzW, hW⟩ := exists_open_eq_of_stalkMap_eq
    (D.ι ≫ f) f D.ι k rfl hkbase y z x.1 hxy hxy hfx hgx' (by
      have hpt : D.ι z = k z := hfx.trans hgx'.symm
      have hs := Scheme.Hom.stalkMap_congr (D.ι ≫ f) (k ≫ f) hkbase.symm z z rfl
      rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hs
      have hcompPt : (D.ι ≫ f) z = (k ≫ f) z := hkbase.symm ▸ rfl
      have hs' : f.stalkMap (D.ι z) ≫ D.ι.stalkMap z =
          (Y.presheaf.stalkCongr (.of_eq hcompPt)).hom ≫
            f.stalkMap (k z) ≫ k.stalkMap z := by
        simpa using hs
      have hfpt := f.stalkMap_congr_point (D.ι z) (k z) hpt
      have hspec : X.presheaf.stalkSpecializes
          (Inseparable.of_eq hpt.symm).specializes =
          (X.presheaf.stalkCongr (.of_eq hpt)).hom := rfl
      have : IsIso (f.stalkMap (D.ι z)) :=
        hf.isIso_stalkMap (D.ι z) (by simp [hfx])
      apply (cancel_epi (f.stalkMap (D.ι z))).mp
      rw [hspec]
      have hreplace :
          ((Y.presheaf.stalkCongr (.of_eq hcompPt)).hom ≫
            f.stalkMap (k z)) ≫ k.stalkMap z =
          (f.stalkMap (D.ι z) ≫
            (X.presheaf.stalkCongr (.of_eq hpt)).hom) ≫ k.stalkMap z :=
        congrArg (fun q ↦ q ≫ k.stalkMap z) hfpt.symm
      exact hs'.trans hreplace) (Or.inl (hfin.elim And.left fun _ ↦ inferInstance))
  refine ⟨D.ι ''ᵁ W, ⟨z, hzW, rfl⟩, ?_⟩
  let q : W.toScheme ⟶ U.toScheme := W.ι ≫ a
  let j : W.toScheme ⟶ X := W.ι ≫ D.ι
  let O : X.Opens := D.ι ''ᵁ W
  have hj : j = q ≫ g := by
    dsimp [j, q, k] at hW ⊢
    simpa only [Category.assoc] using hW
  have hjq : j ≫ f = q ≫ U.ι := by rw [hj, Category.assoc, hgf]
  have : IsOpenImmersion j := by
    dsimp [j]
    infer_instance
  have hqInj : Function.Injective q := fun v w hvw ↦ j.isOpenEmbedding.injective <| by
    simpa [hj, Scheme.Hom.comp_apply] using congrArg g hvw
  have hqOpen : IsOpenMap q := by
    intro T hT
    have himage : q '' T = g ⁻¹' (j '' T) := by
      ext u
      constructor
      · rintro ⟨v, hvT, rfl⟩
        exact ⟨v, hvT, by simp [hj]⟩
      · rintro ⟨v, hvT, hgv⟩
        refine ⟨v, hvT, ?_⟩
        apply U.ι.isOpenEmbedding.injective
        calc
          U.ι (q v) = f (j v) := by simp only [← Scheme.Hom.comp_apply, hjq]
          _ = f (g u) := congrArg f hgv
          _ = U.ι u := by simp only [← Scheme.Hom.comp_apply, hgf]
    rw [himage]
    exact (j.isOpenEmbedding.isOpenMap T hT).preimage g.continuous
  have hqEmbedding : IsOpenEmbedding q :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap q.continuous hqInj hqOpen
  have hqStalk (v : W.toScheme) : IsIso (q.stalkMap v) := by
    let u : U.toScheme := q v
    have hleft : IsIso (f.stalkMap (g u) ≫ g.stalkMap u) := by
      have hi : IsIso ((g ≫ f).stalkMap u) := by
        rw [hgf]
        infer_instance
      rwa [Scheme.Hom.stalkMap_comp] at hi
    have hright : IsIso (g.stalkMap u ≫ q.stalkMap v) := by
      have hi : IsIso (j.stalkMap v) := inferInstance
      rwa [hj, Scheme.Hom.stalkMap_comp] at hi
    have : IsIso (g.stalkMap u) :=
      isIso_of_isIso_comp_left_and_right (f.stalkMap (g u))
        (g.stalkMap u) (q.stalkMap v)
    exact IsIso.of_isIso_comp_left (g.stalkMap u) (q.stalkMap v)
  have : IsOpenImmersion q :=
    IsOpenImmersion.iff_isIso_stalkMap.mpr ⟨hqEmbedding, hqStalk⟩
  have : IsOpenImmersion ((W.ι ≫ D.ι) ≫ f) := by
    rw [hjq]
    infer_instance
  let e : W.toScheme ≅ O.toScheme := D.ι.isoImage W
  have he : e.hom ≫ O.ι = W.ι ≫ D.ι := Scheme.Hom.isoImage_hom_ι D.ι W
  convert (inferInstance : IsOpenImmersion (e.inv ≫ ((W.ι ≫ D.ι) ≫ f))) using 1
  rw [← he]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

/-- A birational morphism of schemes over a base, under either finiteness hypothesis of the
theorem, makes the schemes birational over that base. -/
@[stacks 0BAC "over-base consequence"]
public theorem birationalOver_of_isBirational
    {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (f : X ⟶ Y)
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (hf : IsBirational f) (hfS : f ≫ sY = sX)
    (hfin : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    Scheme.BirationalOver sX sY := by
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf hfin
  let e : U.toScheme ≅ V.toScheme := asIso (f.resLE V U hUV)
  refine ⟨⟨U, hU, V, hV, e⟩, ?_⟩
  dsimp [Scheme.PartialIso.IsOver, e]
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hfS]


end AlgebraicGeometry
