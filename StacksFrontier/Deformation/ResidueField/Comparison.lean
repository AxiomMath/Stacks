module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Functoriality
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.ResidueField.Basic
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# Smoothness and fibre products after change of residue field

The comparison functor for a change of residue field preserves
surjections and fibre products, and smoothness is preserved across the change.

## Main definitions

* `changeOfFieldsBasedFunctor` is the functor induced on the
  categorical pullbacks by a functor over the original base.

## Main results

* `comparisonFunctor_map_surjective` states preservation of surjective
  ring maps.
* `comparisonFunctor_pullbackRingEquiv` identifies the two explicit
  fiber-product rings.
* `comparisonFunctor_pullbackRingEquiv_fst` and
  `comparisonFunctor_pullbackRingEquiv_snd` identify its canonical
  projections.
* `isSmooth_changeOfFields` says that this induced functor is smooth
  when the original functor is smooth.

## Implementation notes

### The comparison functor preserves surjections and fiber products

The source's fiber-product identity is expressed as an equivalence between two
explicit `RingHom.pullback` rings, for every cospan. The left-hand residue map is
the residue map through the first projection; compatibility of the cospan makes
this equal to the map through the second projection. The projection formulas
characterize the equivalence canonically and hence its naturality.

### Smoothness after change of residue field

The source works with categories cofibered in groupoids. The smoothness lifting
property itself makes sense for arbitrary categories over the base, so the result
is stated at that generality. The changed projections are cofibered in groupoids
when the original projections are, by Tag 07W8. The induced functor acts on the
first component of each categorical pullback and leaves the algebra component
unchanged.

## References

* [Stacks Project, Tag 07WD](https://stacks.math.columbia.edu/tag/07WD)
-/

@[expose] public section

namespace Deformation

/-! ### The comparison functor preserves surjections and fiber products -/

section
open CategoryTheory CategoryTheory.Limits
universe u v w x

/-- The comparison functor sends a surjective morphism of Artinian local algebras
with residue field `l` to a surjective morphism with residue field `k`. -/
theorem comparisonFunctor_map_surjective (S : ChangeOfFieldsSituation.{u, v, w})
    {B₁ B₂ : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (f : B₁ ⟶ B₂) (hf : Function.Surjective f.hom) :
    Function.Surjective ((comparisonFunctor S).functor.map f).hom := by
  let F := comparisonFunctor.{u, v, w, x} S
  intro y
  let p := F.pullbackEquiv B₂ y
  let b₂ := p.val.1
  let c := p.val.2
  have hp : residueMap S B₂ b₂ = algebraMap S.k S.l c := p.property
  obtain ⟨b₁, hb₁⟩ := hf b₂
  have hres : residueMap S B₁ b₁ = algebraMap S.k S.l c := by
    dsimp [residueMap] at hp ⊢
    rw [← f.residue_comm b₁, hb₁]
    exact hp
  let z : F.functor.obj B₁ := (F.pullbackEquiv B₁).symm ⟨(b₁, c), hres⟩
  refine ⟨z, ?_⟩
  apply (F.pullbackEquiv B₂).injective
  apply Subtype.ext
  apply Prod.ext
  · rw [F.map_fst]
    change f.hom ((F.pullbackEquiv B₁ z).val.1) = b₂
    simpa [z] using hb₁
  · rw [F.map_snd]
    change ((F.pullbackEquiv B₁) z).val.2 = c
    simp [z]

private structure ComparisonFunctorPullbackData
    (S : ChangeOfFieldsSituation.{u, v, w})
    {B₁ B₂ B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (f : B₁ ⟶ B) (g : B₂ ⟶ B) where
  equiv :
    let F := (comparisonFunctor.{u, v, w, x} S).functor
    RingHom.pullback
        ((residueMap S B₁).comp
          (RingHom.pullbackFst f.hom.toRingHom g.hom.toRingHom))
        (algebraMap S.k S.l) ≃+*
      RingHom.pullback (F.map f).hom.toRingHom (F.map g).hom.toRingHom
  fst :
    let F := comparisonFunctor.{u, v, w, x} S
    ∀ a, ((F.pullbackEquiv B₁) ((equiv a).val.1)).val = (a.val.1.val.1, a.val.2)
  snd :
    let F := comparisonFunctor.{u, v, w, x} S
    ∀ a, ((F.pullbackEquiv B₂) ((equiv a).val.2)).val = (a.val.1.val.2, a.val.2)

attribute [-simp] ComparisonFunctorPullbackData.mk.injEq
  ComparisonFunctorPullbackData.mk.sizeOf_spec

/-- The canonical comparison between the two rings obtained by applying residue-field
restriction and forming a fiber product in either order. -/
noncomputable def comparisonFunctor_pullbackRingEquiv
    (S : ChangeOfFieldsSituation.{u, v, w})
    {B₁ B₂ B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (f : B₁ ⟶ B) (g : B₂ ⟶ B) :
    let F := (comparisonFunctor.{u, v, w, x} S).functor
    RingHom.pullback
        ((residueMap S B₁).comp
          (RingHom.pullbackFst f.hom.toRingHom g.hom.toRingHom))
        (algebraMap S.k S.l) ≃+*
      RingHom.pullback (F.map f).hom.toRingHom (F.map g).hom.toRingHom := by
  let F := comparisonFunctor.{u, v, w, x} S
  let D := RingHom.pullback
    ((residueMap S B₁).comp
      (RingHom.pullbackFst f.hom.toRingHom g.hom.toRingHom))
    (algebraMap S.k S.l)
  let E := RingHom.pullback (F.functor.map f).hom.toRingHom (F.functor.map g).hom.toRingHom
  have hres₁ (a : D) : residueMap S B₁ a.val.1.val.1 =
      algebraMap S.k S.l a.val.2 := by
    have ha := a.property
    change residueMap S B₁ a.val.1.val.1 = _ at ha
    exact ha
  have hcompat (a : D) : f.hom a.val.1.val.1 = g.hom a.val.1.val.2 := a.val.1.property
  have hres₂ (a : D) : residueMap S B₂ a.val.1.val.2 =
      algebraMap S.k S.l a.val.2 := by
    calc
      residueMap S B₂ a.val.1.val.2 =
          residueMap S B (g.hom a.val.1.val.2) := by
            simpa [residueMap] using (g.residue_comm a.val.1.val.2).symm
      _ = residueMap S B (f.hom a.val.1.val.1) := by rw [hcompat a]
      _ = residueMap S B₁ a.val.1.val.1 := by
        simpa [residueMap] using f.residue_comm a.val.1.val.1
      _ = algebraMap S.k S.l a.val.2 := hres₁ a
  let q₁ := (RingHom.pullbackFst f.hom.toRingHom g.hom.toRingHom).comp
    (RingHom.pullbackFst
      ((residueMap S B₁).comp
        (RingHom.pullbackFst f.hom.toRingHom g.hom.toRingHom))
      (algebraMap S.k S.l))
  let q₂ := (RingHom.pullbackSnd f.hom.toRingHom g.hom.toRingHom).comp
    (RingHom.pullbackFst
      ((residueMap S B₁).comp
        (RingHom.pullbackFst f.hom.toRingHom g.hom.toRingHom))
      (algebraMap S.k S.l))
  let qₖ := RingHom.pullbackSnd
    ((residueMap S B₁).comp
      (RingHom.pullbackFst f.hom.toRingHom g.hom.toRingHom))
    (algebraMap S.k S.l)
  let e₁ := (RingHom.prod q₁ qₖ).codRestrict
    ((residueMap S B₁).pullback (algebraMap S.k S.l))
    (by intro a; change residueMap S B₁ a.val.1.val.1 =
      algebraMap S.k S.l a.val.2; exact hres₁ a)
  let e₂ := (RingHom.prod q₂ qₖ).codRestrict
    ((residueMap S B₂).pullback (algebraMap S.k S.l))
    (by intro a; change residueMap S B₂ a.val.1.val.2 =
      algebraMap S.k S.l a.val.2; exact hres₂ a)
  let u₁ := (F.pullbackEquiv B₁).symm.toRingHom.comp e₁
  let u₂ := (F.pullbackEquiv B₂).symm.toRingHom.comp e₂
  have hu₁ (a : D) : (F.pullbackEquiv B₁ (u₁ a)).val = (a.val.1.val.1, a.val.2) := by
    change (F.pullbackEquiv B₁ ((F.pullbackEquiv B₁).symm (e₁ a))).val = _
    rw [RingEquiv.apply_symm_apply]
    change (q₁ a, qₖ a) = _
    constructor
  have hu₂ (a : D) : (F.pullbackEquiv B₂ (u₂ a)).val = (a.val.1.val.2, a.val.2) := by
    change (F.pullbackEquiv B₂ ((F.pullbackEquiv B₂).symm (e₂ a))).val = _
    rw [RingEquiv.apply_symm_apply]
    change (q₂ a, qₖ a) = _
    constructor
  have hmap (a : D) : (F.functor.map f).hom (u₁ a) = (F.functor.map g).hom (u₂ a) := by
    apply (F.pullbackEquiv B).injective
    apply Subtype.ext
    apply Prod.ext
    · rw [F.map_fst f, F.map_fst g]
      rw [hu₁, hu₂]
      exact hcompat a
    · rw [F.map_snd f, F.map_snd g]
      rw [hu₁, hu₂]
  let forward : D →+* E := (RingHom.prod u₁ u₂).codRestrict E hmap
  have hforward₁ (a : D) :
      (F.pullbackEquiv B₁ ((forward a).val.1)).val = (a.val.1.val.1, a.val.2) := by
    change (F.pullbackEquiv B₁ (u₁ a)).val = _
    exact hu₁ a
  have hforward₂ (a : D) :
      (F.pullbackEquiv B₂ ((forward a).val.2)).val = (a.val.1.val.2, a.val.2) := by
    change (F.pullbackEquiv B₂ (u₂ a)).val = _
    exact hu₂ a
  let p₁ (z : E) := F.pullbackEquiv B₁ z.val.1
  let p₂ (z : E) := F.pullbackEquiv B₂ z.val.2
  have hfirst (z : E) : f.hom (p₁ z).val.1 = g.hom (p₂ z).val.1 := by
      have hh := congrArg (fun t => (F.pullbackEquiv B t).val.1) z.property
      change (F.pullbackEquiv B ((F.functor.map f).hom z.val.1)).val.1 =
        (F.pullbackEquiv B ((F.functor.map g).hom z.val.2)).val.1 at hh
      rw [F.map_fst f, F.map_fst g] at hh
      simpa [p₁, p₂] using hh
  have hsecond (z : E) : (p₁ z).val.2 = (p₂ z).val.2 := by
      have hh := congrArg (fun t => (F.pullbackEquiv B t).val.2) z.property
      change (F.pullbackEquiv B ((F.functor.map f).hom z.val.1)).val.2 =
        (F.pullbackEquiv B ((F.functor.map g).hom z.val.2)).val.2 at hh
      rw [F.map_snd f, F.map_snd g] at hh
      simpa [p₁, p₂] using hh
  let backward : E → D := fun z => by
    refine ⟨((⟨((p₁ z).val.1, (p₂ z).val.1), hfirst z⟩ :
      RingHom.pullback f.hom.toRingHom g.hom.toRingHom), (p₁ z).val.2), ?_⟩
    change residueMap S B₁ (p₁ z).val.1 =
      algebraMap S.k S.l (p₁ z).val.2
    exact (p₁ z).property
  have left_inv (a : D) : backward (forward a) = a := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · change (F.pullbackEquiv B₁ ((forward a).val.1)).val.1 = a.val.1.val.1
        rw [hforward₁]
      · change (F.pullbackEquiv B₂ ((forward a).val.2)).val.1 = a.val.1.val.2
        rw [hforward₂]
    · change (F.pullbackEquiv B₁ ((forward a).val.1)).val.2 = a.val.2
      rw [hforward₁]
  have right_inv (z : E) : forward (backward z) = z := by
    apply Subtype.ext
    apply Prod.ext
    · change u₁ (backward z) = z.val.1
      apply (F.pullbackEquiv B₁).injective
      apply Subtype.ext
      apply Prod.ext
      · change (F.pullbackEquiv B₁ (u₁ (backward z))).val.1 = (p₁ z).val.1
        rw [hu₁]
      · change (F.pullbackEquiv B₁ (u₁ (backward z))).val.2 = (p₁ z).val.2
        rw [hu₁]
    · change u₂ (backward z) = z.val.2
      apply (F.pullbackEquiv B₂).injective
      apply Subtype.ext
      apply Prod.ext
      · change (F.pullbackEquiv B₂ (u₂ (backward z))).val.1 = (p₂ z).val.1
        rw [hu₂]
      · change (F.pullbackEquiv B₂ (u₂ (backward z))).val.2 = (p₂ z).val.2
        rw [hu₂]
        exact hsecond z
  let equiv := RingEquiv.mk ⟨forward, backward, left_inv, right_inv⟩
    (fun a b => forward.map_mul a b) (fun a b => forward.map_add a b)
  exact equiv

private noncomputable def comparisonFunctor_pullbackRingEquivData
    (S : ChangeOfFieldsSituation.{u, v, w})
    {B₁ B₂ B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (f : B₁ ⟶ B) (g : B₂ ⟶ B) : ComparisonFunctorPullbackData S f g :=
  ⟨comparisonFunctor_pullbackRingEquiv S f g,
    fun _ => congrArg Subtype.val (RingEquiv.apply_symm_apply _ _),
    fun _ => congrArg Subtype.val (RingEquiv.apply_symm_apply _ _)⟩

private theorem comparisonFunctor_pullbackRingEquivData_fst
    (S : ChangeOfFieldsSituation.{u, v, w})
    {B₁ B₂ B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (f : B₁ ⟶ B) (g : B₂ ⟶ B) :
    let F := comparisonFunctor.{u, v, w, x} S
    ∀ a, ((F.pullbackEquiv B₁)
        (((comparisonFunctor_pullbackRingEquiv S f g) a).val.1)).val =
      (a.val.1.val.1, a.val.2) := by
  intro F a
  exact (comparisonFunctor_pullbackRingEquivData S f g).fst a

/-- The comparison equivalence commutes with the first fiber-product projection,
on both the algebra and residue-field coordinates. -/
alias comparisonFunctor_pullbackRingEquiv_fst := comparisonFunctor_pullbackRingEquivData_fst

private theorem comparisonFunctor_pullbackRingEquivData_snd
    (S : ChangeOfFieldsSituation.{u, v, w})
    {B₁ B₂ B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (f : B₁ ⟶ B) (g : B₂ ⟶ B) :
    let F := comparisonFunctor.{u, v, w, x} S
    ∀ a, ((F.pullbackEquiv B₂)
        (((comparisonFunctor_pullbackRingEquiv S f g) a).val.2)).val =
      (a.val.1.val.2, a.val.2) := by
  intro F a
  exact (comparisonFunctor_pullbackRingEquivData S f g).snd a

/-- The comparison equivalence commutes with the second fiber-product projection,
on both the algebra and residue-field coordinates. -/
alias comparisonFunctor_pullbackRingEquiv_snd := comparisonFunctor_pullbackRingEquivData_snd

end

/-! ### Smoothness after change of residue field -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w x u₁ v₁ u₂ v₂

/-- The morphism obtained by changing the residue field of both categories
over the base. -/
public def changeOfFieldsBasedFunctor
    (S : ChangeOfFieldsSituation.{u, v, w})
    {𝓕 : BasedCategory.{v₁, u₁}
      (ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)}
    {𝓖 : BasedCategory.{v₂, u₂}
      (ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)}
    (φ : BasedFunctor 𝓕 𝓖) :
    BasedFunctor
      (BasedCategory.ofFunctor (changeOfFieldsProjection S 𝓕.p))
      (BasedCategory.ofFunctor (changeOfFieldsProjection S 𝓖.p)) where
  toFunctor :=
    CategoricalPullback.map 𝓕.p (comparisonFunctor S).functor
      φ.toFunctor (𝟭 _) (𝟭 _) 𝓖.p (comparisonFunctor S).functor
      (Iso.refl _) (eqToIso φ.w.symm)
  w := by
    apply CategoryTheory.Functor.ext
    · intro P Q f
      rfl
    · intro P
      rfl

/-- **Stacks Project, Tag 07WD.** A smooth morphism of categories over the
Artinian algebras with residue field `k` remains smooth after changing the
residue field to `l`. -/
@[stacks 07WD]
public theorem isSmooth_changeOfFields
    (S : ChangeOfFieldsSituation.{u, v, w})
    {𝓕 : BasedCategory.{v₁, u₁}
      (ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)}
    {𝓖 : BasedCategory.{v₂, u₂}
      (ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)}
    (φ : BasedFunctor 𝓕 𝓖) (hφ : IsSmooth φ) :
    IsSmooth (changeOfFieldsBasedFunctor S φ) := by
  intro B A f hf y x g hg
  let : (changeOfFieldsProjection S 𝓖.p).IsHomLift f g := hg
  have hB : y.snd = B := by
    change (changeOfFieldsProjection S 𝓖.p).obj y = B
    exact IsHomLift.domain_eq (changeOfFieldsProjection S 𝓖.p) f g
  have hA : x.snd = A := by
    change (changeOfFieldsProjection S 𝓖.p).obj
      ((changeOfFieldsBasedFunctor S φ).obj x) = A
    exact IsHomLift.codomain_eq (changeOfFieldsProjection S 𝓖.p) f g
  subst B
  subst A
  let yCP : CategoricalPullback 𝓖.p (comparisonFunctor S).functor := by
    exact y
  have hgsnd : (changeOfFieldsProjection S 𝓖.p).map g = f := by
    change (changeOfFieldsProjection S 𝓖.p).obj y ⟶
      (changeOfFieldsProjection S 𝓖.p).obj
        ((changeOfFieldsBasedFunctor S φ).obj x) at f
    have hf' : f = (changeOfFieldsProjection S 𝓖.p).map g := by
      let : (changeOfFieldsProjection S 𝓖.p).IsHomLift f g := hg
      exact IsHomLift.eq_of_isHomLift (changeOfFieldsProjection S 𝓖.p) f g
    change (changeOfFieldsProjection S 𝓖.p).map g = f
    exact hf'.symm
  let z : CategoricalPullback 𝓖.p (comparisonFunctor S).functor :=
    (changeOfFieldsBasedFunctor S φ).toFunctor.obj x
  have hconj : 𝓖.p.map g.fst = y.iso.hom ≫
      (comparisonFunctor S).functor.map f ≫ z.iso.inv := by
    calc
      𝓖.p.map g.fst = (𝓖.p.map g.fst ≫ z.iso.hom) ≫ z.iso.inv := by simp
      _ = (y.iso.hom ≫ (comparisonFunctor S).functor.map g.snd) ≫ z.iso.inv := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ z.iso.inv) g.w
      _ = y.iso.hom ≫ (comparisonFunctor S).functor.map f ≫ z.iso.inv := by
        rw [← hgsnd]
        rfl
  have hMf : Function.Surjective ((comparisonFunctor S).functor.map f).hom :=
    comparisonFunctor_map_surjective S f hf
  have hsurj : Function.Surjective (𝓖.p.map g.fst).hom := by
    rw [hconj]
    intro b
    obtain ⟨a, ha⟩ := hMf ((z.iso.hom).hom b)
    refine ⟨(y.iso.inv).hom a, ?_⟩
    change (z.iso.inv).hom (((comparisonFunctor S).functor.map f).hom
      ((y.iso.hom).hom ((y.iso.inv).hom a))) = b
    have hy : (y.iso.hom).hom ((y.iso.inv).hom a) = a := by
      change (y.iso.inv ≫ y.iso.hom).hom a = a
      rw [y.iso.inv_hom_id]
      rfl
    rw [hy, ha]
    change (z.iso.hom ≫ z.iso.inv).hom b = b
    rw [z.iso.hom_inv_id]
    rfl
  let : 𝓖.p.IsHomLift (𝓖.p.map g.fst) g.fst := inferInstance
  obtain ⟨x', h, a, hh, ha, hcomm⟩ := hφ (𝓖.p.map g.fst) hsurj y.fst x.fst g.fst
    (inferInstance : 𝓖.p.IsHomLift (𝓖.p.map g.fst) g.fst)
  have hxdom : 𝓕.p.obj x' = 𝓖.p.obj y.fst := by
    simpa using (IsHomLift.domain_eq 𝓕.p (𝓖.p.map g.fst) h)
  let : 𝓕.p.IsHomLift (𝓖.p.map g.fst) h := hh
  have hcod : 𝓕.p.obj x.fst = 𝓖.p.obj (φ.obj x.fst) :=
    (BasedFunctor.w_obj φ x.fst).symm
  have hmap : 𝓕.p.map h =
      eqToHom hxdom ≫ 𝓖.p.map g.fst ≫ eqToHom hcod.symm := by
    let : 𝓕.p.IsHomLift (𝓖.p.map g.fst) h := hh
    simpa [hxdom, hcod] using
      (IsHomLift.fac' 𝓕.p (𝓖.p.map g.fst) h)
  have hziso : z.iso.hom = eqToHom hcod.symm ≫ x.iso.hom := by
    have hh := CategoricalPullback.map_obj_iso_hom
        (H := 𝓕.p) (I := (comparisonFunctor S).functor)
      (L := φ.toFunctor) (K := 𝟭 _) (M := 𝟭 _) (F := 𝓖.p)
      (G := (comparisonFunctor S).functor)
      (α := Iso.refl _) (β := eqToIso φ.w.symm) x
    simpa [z, changeOfFieldsBasedFunctor] using hh
  have hcancel : z.iso.inv ≫ eqToHom hcod.symm ≫ x.iso.hom = 𝟙 _ := by
    have hh := congrArg (fun q => z.iso.inv ≫ q) hziso
    exact hh.symm.trans z.iso.inv_hom_id
  have hcod' : 𝓕.p.obj x' = 𝓖.p.obj (φ.obj x') :=
    (BasedFunctor.w_obj φ x').symm
  have habase : 𝓖.p.map a = eqToHom hcod'.symm ≫ eqToHom hxdom := by
    let : 𝓖.p.IsHomLift (𝟙 (𝓖.p.obj y.fst)) a := ha
    simpa [hcod', hxdom] using
      (IsHomLift.fac' 𝓖.p (𝟙 (𝓖.p.obj y.fst)) a)
  let xNewCP : CategoricalPullback 𝓕.p (comparisonFunctor S).functor :=
    ⟨x', yCP.snd, (eqToIso hxdom) ≪≫ yCP.iso⟩
  let xNew : (BasedCategory.ofFunctor (changeOfFieldsProjection S 𝓕.p)).obj := by
    change CategoricalPullback 𝓕.p (comparisonFunctor S).functor
    exact xNewCP
  have hxNewIso : xNew.iso.hom = eqToHom hxdom ≫ y.iso.hom := by
    change (eqToIso hxdom ≪≫ y.iso).hom = _
    simp
  have hxNewCPIso : xNewCP.iso.hom = eqToHom hxdom ≫ yCP.iso.hom := by
    change (eqToIso hxdom ≪≫ yCP.iso).hom = _
    simp
  let hNew : xNew ⟶ x := by
    refine ⟨h, f, ?_⟩
    calc
      _ = eqToHom hxdom ≫ y.iso.hom ≫ (comparisonFunctor S).functor.map f ≫
          (z.iso.inv ≫ eqToHom hcod.symm ≫ x.iso.hom) := by
        rw [hmap, hconj]
        cat_disch
      _ = eqToHom hxdom ≫ y.iso.hom ≫ (comparisonFunctor S).functor.map f := by
        have hh := congrArg
          (fun q => (eqToHom hxdom ≫ y.iso.hom ≫
            (comparisonFunctor S).functor.map f) ≫ q) hcancel
        calc
          _ = (eqToHom hxdom ≫ y.iso.hom ≫
              (comparisonFunctor S).functor.map f) ≫
                (z.iso.inv ≫ (eqToHom hcod.symm ≫ x.iso.hom)) := rfl
          _ = (eqToHom hxdom ≫ y.iso.hom ≫
              (comparisonFunctor S).functor.map f) ≫ 𝟙 _ := hh
          _ = _ := by simp
      _ = xNew.iso.hom ≫ (comparisonFunctor S).functor.map f := by
        rw [hxNewIso]
        simp [Category.assoc]
  have hchangeIso :
      ((CategoricalPullback.map 𝓕.p (comparisonFunctor S).functor
        φ.toFunctor (𝟭 _) (𝟭 _) 𝓖.p (comparisonFunctor S).functor
        (Iso.refl _) (eqToIso φ.w.symm)).obj xNewCP).iso.hom =
        eqToHom hcod'.symm ≫ xNewCP.iso.hom := by
    have hβ : (eqToIso φ.w.symm).inv.app x' = eqToHom hcod'.symm := by
      rw [eqToIso.inv, eqToHom_app]
    rw [CategoricalPullback.map_obj_iso_hom]
    simp only [Iso.refl_inv]
    rw [hβ]
    simp
  let aNew : (changeOfFieldsBasedFunctor S φ).obj xNew ⟶ y := by
    refine ⟨a, 𝟙 yCP.snd, ?_⟩
    change 𝓖.p.map a ≫ yCP.iso.hom =
      ((CategoricalPullback.map 𝓕.p (comparisonFunctor S).functor
        φ.toFunctor (𝟭 _) (𝟭 _) 𝓖.p (comparisonFunctor S).functor
        (Iso.refl _) (eqToIso φ.w.symm)).obj xNewCP).iso.hom ≫
        (comparisonFunctor S).functor.map (𝟙 yCP.snd)
    have habaseComp := congrArg (fun q => q ≫ yCP.iso.hom) habase
    rw [habaseComp, hchangeIso, hxNewCPIso]
    have hmapid : (comparisonFunctor S).functor.map (𝟙 yCP.snd) = 𝟙 _ :=
      (comparisonFunctor S).functor.map_id yCP.snd
    let t := eqToHom hcod'.symm ≫ eqToHom hxdom ≫ yCP.iso.hom
    have hmapid' := congrArg (fun q => t ≫ q) hmapid
    calc
      _ = t := Category.assoc _ _ _
      _ = t ≫ (comparisonFunctor S).functor.map (𝟙 yCP.snd) := by
        calc
          t = t ≫ 𝟙 _ := by simp
          _ = t ≫ (comparisonFunctor S).functor.map (𝟙 yCP.snd) := hmapid'.symm
  refine ⟨xNew, hNew, aNew, ?_, ?_, ?_⟩
  · exact IsHomLift.map (changeOfFieldsProjection S 𝓕.p) hNew
  · exact IsHomLift.map (changeOfFieldsProjection S 𝓖.p) aNew
  · apply CategoricalPullback.hom_ext
    · change φ.map h = a ≫ g.fst
      exact hcomm
    · change f = g.snd
      change g.snd = f at hgsnd
      exact hgsnd.symm

end

end Deformation
