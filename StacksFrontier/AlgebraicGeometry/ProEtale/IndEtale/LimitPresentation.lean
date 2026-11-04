module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleCover
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.Permanence
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtale

/-!
# Ind-étale morphisms of affine schemes as limits of étale ones

Let `S` be an affine scheme.  A morphism `f : V ⟶ S` from an affine scheme is ind-étale on global
sections, i.e. `Γ(S) → Γ(V)` is a filtered colimit of étale ring maps, exactly when `V` is the
limit of a cofiltered system of affine schemes étale over `S`.  We also prove Proposition 097Z in
geometric form: a weakly étale morphism of affine schemes is refined by a surjective weakly étale
morphism which is ind-étale over the base.

Ind-étaleness of a ring map is `CategoryTheory.MorphismProperty.ind` of `CommRingCat.etale`, with
index categories in the universe of the rings.  A limit presentation of `V` over `S` is a functor
`D` to schemes with a natural transformation to the constant functor on `S` and a limit cone with
vertex `V`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_surjective_weaklyEtale_indEtale_appTop`: Proposition 097Z
  for a morphism of affine schemes.
* `AlgebraicGeometry.ProEtale.exists_isLimit_of_indEtale_appTop`: an ind-étale morphism of affine
  schemes is a cofiltered limit of affine schemes étale over the base.
* `AlgebraicGeometry.ProEtale.indEtale_appTop_of_isLimit`: conversely, a cofiltered limit of
  affine schemes étale over an affine base, which is itself affine, is ind-étale over the base.

## References

* [Stacks Project, Tag 097Z](https://stacks.math.columbia.edu/tag/097Z)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProEtale

/-- An isomorphism of rings is ind-étale. -/
lemma indEtale_of_isIso {R T : CommRingCat.{u}} (e : R ⟶ T) [IsIso e] :
    MorphismProperty.ind.{u} CommRingCat.etale e :=
  MorphismProperty.le_ind _ _ (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso e))

/-- **Proposition 097Z for a morphism of affine schemes.** A weakly étale morphism `f : V ⟶ U`
of affine schemes is refined by a surjective weakly étale morphism `q : W ⟶ V` from an affine
scheme such that `q ≫ f` is ind-étale on global sections. -/
theorem exists_surjective_weaklyEtale_indEtale_appTop {U V : Scheme.{u}} [IsAffine U]
    [IsAffine V] (f : V ⟶ U) [WeaklyEtale f] :
    ∃ (W : Scheme.{u}) (q : W ⟶ V), IsAffine W ∧ Surjective q ∧ WeaklyEtale q ∧
      MorphismProperty.ind.{u} CommRingCat.etale (q ≫ f).appTop := by
  obtain ⟨B', hB', g, hgff, hindV, hindU⟩ :=
    exists_faithfullyFlat_indEtale_extension f.appTop.hom (weaklyEtale_appTop_of_isAffine f)
  let : CommRing B' := hB'
  let q : Spec (CommRingCat.of B') ⟶ V :=
    Stacks.Smooth.homEquivOfIsAffine.symm
      (CommRingCat.ofHom g ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).inv)
  have hq : q.appTop = CommRingCat.ofHom g ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).inv :=
    Stacks.Smooth.homEquivOfIsAffine.apply_symm_apply _
  have hiso := indEtale_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B')).inv
  have hindq : MorphismProperty.ind.{u} CommRingCat.etale q.appTop := by
    rw [hq]
    exact CommRingCat.ind_etale_comp _ _
      ((MorphismProperty.ind_iff_ind_underMk _).mpr hindV) hiso
  have hffr : q.appTop.hom.FaithfullyFlat := by
    rw [hq]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _ hgff
      (RingHom.FaithfullyFlat.of_bijective (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of B')).inv))
  have hsurj : Surjective q :=
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mpr hffr).2
  have hwq : WeaklyEtale q :=
    (MorphismProperty.arrow_mk_iso_iff (P := @WeaklyEtale) (arrowIsoSpecΓOfIsAffine q)).mpr
      (weaklyEtale_specMap_of_ind_etale _ ((MorphismProperty.ind_iff_ind_underMk _).mp hindq))
  refine ⟨_, q, inferInstance, hsurj, hwq, ?_⟩
  rw [Scheme.Hom.comp_appTop, hq, ← Category.assoc]
  exact CommRingCat.ind_etale_comp _ _
    ((MorphismProperty.ind_iff_ind_underMk _).mpr hindU) hiso

/-- **An ind-étale morphism of affine schemes is a limit of étale ones.** If `f : V ⟶ S` is a
morphism of affine schemes which is ind-étale on global sections, then `V` is the limit of a
cofiltered system of affine schemes étale over `S`, compatibly with `f`. -/
theorem exists_isLimit_of_indEtale_appTop {S V : Scheme.{u}} [IsAffine S] [IsAffine V]
    (f : V ⟶ S) (hf : MorphismProperty.ind.{u} CommRingCat.etale f.appTop) :
    ∃ (A : Type u) (_ : SmallCategory A) (_ : IsCofiltered A) (D : A ⥤ Scheme.{u})
      (d : D ⟶ (Functor.const A).obj S) (p : (Functor.const A).obj V ⟶ D),
      (∀ a, IsAffine (D.obj a)) ∧ (∀ a, Etale (d.app a)) ∧ (∀ a, p.app a ≫ d.app a = f) ∧
        Nonempty (IsLimit (Cone.mk V p)) := by
  rw [MorphismProperty.ind_iff_ind_underMk] at hf
  obtain ⟨J, _, _, pres, hpres⟩ := hf
  let D : Jᵒᵖ ⥤ Scheme.{u} := (pres.diag ⋙ Under.forget Γ(S, ⊤)).op ⋙ Scheme.Spec
  let d : D ⟶ (Functor.const Jᵒᵖ).obj S :=
    { app a := Spec.map (pres.diag.obj a.unop).hom ≫ S.isoSpec.inv
      naturality {a b} g := by
        dsimp [D]
        rw [Category.comp_id, ← Category.assoc, ← Spec.map_comp, Under.w] }
  let p : (Functor.const Jᵒᵖ).obj V ⟶ D :=
    { app a := V.isoSpec.hom ≫ Spec.map (pres.ι.app a.unop).right
      naturality {a b} g := by
        dsimp [D]
        rw [Category.id_comp, Category.assoc, ← Spec.map_comp, ← Under.comp_right,
          pres.ι.naturality g.unop]
        simp }
  have hL : IsLimit (Scheme.Spec.mapCone
      ((Under.forget Γ(S, ⊤)).mapCocone (Cocone.mk _ pres.ι)).op) :=
    isLimitOfPreserves Scheme.Spec (isColimitOfPreserves (Under.forget Γ(S, ⊤))
      pres.isColimit).op
  refine ⟨Jᵒᵖ, inferInstance, inferInstance, D, d, p,
    fun a ↦ inferInstanceAs (IsAffine (Spec _)), fun a ↦ ?_, fun a ↦ ?_,
    ⟨IsLimit.ofIsoLimit hL (Cone.ext V.isoSpec.symm fun a ↦ ?_)⟩⟩
  · have : Etale (Spec.map (pres.diag.obj a.unop).hom) :=
      HasRingHomProperty.Spec_iff.mpr (hpres a.unop)
    have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    change Etale (Spec.map (pres.diag.obj a.unop).hom ≫ S.isoSpec.inv)
    rwa [MorphismProperty.cancel_right_of_respectsIso (@Etale)]
  · change (V.isoSpec.hom ≫ Spec.map (pres.ι.app a.unop).right) ≫
      Spec.map (pres.diag.obj a.unop).hom ≫ S.isoSpec.inv = f
    rw [Category.assoc, ← Spec.map_comp_assoc, Under.w (pres.ι.app a.unop)]
    simp [Scheme.isoSpec_hom_naturality_assoc]
  · exact (V.isoSpec.inv_hom_id_assoc _).symm

/-- **A limit of étale affine schemes is ind-étale.** If an affine scheme `V` over an affine
scheme `S` is the limit of a cofiltered system of affine schemes étale over `S`, compatibly with
the structure morphisms, then `V ⟶ S` is ind-étale on global sections. -/
theorem indEtale_appTop_of_isLimit {S V : Scheme.{u}} [IsAffine S] [IsAffine V] (f : V ⟶ S)
    {A : Type u} [SmallCategory A] [IsCofiltered A] (D : A ⥤ Scheme.{u})
    (d : D ⟶ (Functor.const A).obj S) (p : (Functor.const A).obj V ⟶ D)
    [∀ a, IsAffine (D.obj a)] (hd : ∀ a, Etale (d.app a)) (hpd : ∀ a, p.app a ≫ d.app a = f)
    (hc : IsLimit (Cone.mk V p)) :
    MorphismProperty.ind.{u} CommRingCat.etale f.appTop := by
  rw [MorphismProperty.ind_iff_ind_underMk]
  change ObjectProperty.ind.{u} (fun C : Under Γ(S, ⊤) ↦ C.hom.hom.Etale) _
  rw [CommRingCat.ind_under_iff_exists_factorization _ etale_under_le_finitePresentation]
  intro T hT φ
  let a : V ⟶ Spec T.right :=
    Stacks.Smooth.homEquivOfIsAffine.symm ((Scheme.ΓSpecIso T.right).hom ≫ φ.right)
  have ha : a.appTop = (Scheme.ΓSpecIso T.right).hom ≫ φ.right :=
    Stacks.Smooth.homEquivOfIsAffine.apply_symm_apply _
  let t : Spec T.right ⟶ S := Spec.map T.hom ≫ S.isoSpec.inv
  have : LocallyOfFinitePresentation (Spec.map T.hom) :=
    HasRingHomProperty.Spec_iff.mpr hT
  have hat : a ≫ t = f := by
    refine ext_of_isAffine ?_
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Stacks.Modules.isoSpec_inv_appTop, ha]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]
    exact Under.w φ
  obtain ⟨i, g, hg₁, hg₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D d t
    (Cone.mk V p) hc a (by ext i; simp [hpd, hat])
  have := hd i
  have : IsAffine (((Functor.const A).obj S).obj i) := inferInstanceAs (IsAffine S)
  refine ⟨Under.mk (d.app i).appTop,
    Under.homMk ((Scheme.ΓSpecIso T.right).inv ≫ g.appTop) ?_,
    Under.homMk (p.app i).appTop ?_, ?_, HasRingHomProperty.iff_of_isAffine.mp (hd i)⟩
  · dsimp
    rw [← hg₂, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Stacks.Modules.isoSpec_inv_appTop]
    simp only [← Category.assoc]
    congr 1
    rw [Iso.eq_inv_comp, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · dsimp
    rw [← Scheme.Hom.comp_appTop, hpd]
  · ext : 1
    change ((Scheme.ΓSpecIso T.right).inv ≫ g.appTop) ≫ (p.app i).appTop = φ.right
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, hg₁, ha, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.ProEtale
