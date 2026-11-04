module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityOpen

/-!
# Versality of an element of Artin's contraction functor is local on the scheme

In the situation of Stacks 0GH8 let `F` be Artin's contraction functor of Stacks 0GHA and let
`ξ ∈ F(V)`. For an open `O ⊆ V`, the restriction `ξ|_O ∈ F(O)` is versal at a point of `O`
exactly when `ξ` is versal there: every lifting problem for versality at that point lives over
spectra of Artinian local rings mapping into `O`. This is the invariance of versality under
restriction to an open subscheme (`Deformation.Artin.isVersalAt_iff_restrict` for categories
fibred in groupoids) for the category over schemes attached to `F`, which is not fibred in
groupoids over all schemes; it lets the proof of Stacks 0GIA shrink `V` to an open in which a
finite type point is closed, as Lemma 0GI9 requires.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.restrictElement`: the restriction `ξ|_O`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.isVersalAt_restrictElement_iff`: `ξ|_O` is versal
  at `u` exactly when `ξ` is versal at the image of `u`.

## References

* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 0GIA](https://stacks.math.columbia.edu/tag/0GIA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- The restriction `ξ|_O ∈ F(O)` of an element `ξ ∈ F(V)` to an open `O ⊆ V`. -/
def restrictElement (x : (contractionFunctor c).Elementsᵒᵖ)
    (O : x.unop.1.unop.obj.left.obj.Opens) : (contractionFunctor c).Elementsᵒᵖ :=
  haveI : IsLocallyNoetherian x.unop.1.unop.obj.left.obj := x.unop.1.unop.property
  op ⟨op ⟨BigFppfOver.openSubObj B S hS x.unop.1.unop.obj O,
      inferInstanceAs (IsLocallyNoetherian (O : Scheme.{u}))⟩,
    mapTriple c (BigFppfOver.openSubHom B S hS x.unop.1.unop.obj O) x.unop.2⟩

/-- The arrow `ξ|_O ⟶ ξ` of the category over schemes attached to `F`. -/
def restrictElementHom (x : (contractionFunctor c).Elementsᵒᵖ)
    (O : x.unop.1.unop.obj.left.obj.Opens) : restrictElement c x O ⟶ x :=
  Quiver.Hom.op ⟨(ObjectProperty.homMk (BigFppfOver.openSubHom B S hS x.unop.1.unop.obj O) :
    (restrictElement c x O).unop.1.unop ⟶ x.unop.1.unop).op, rfl⟩

/-- Arrows into `ξ|_O` are determined by their composites with `ξ|_O ⟶ ξ`. -/
private theorem eq_of_comp_restrictElementHom_eq (x : (contractionFunctor c).Elementsᵒᵖ)
    (O : x.unop.1.unop.obj.left.obj.Opens) {y : (contractionFunctor c).Elementsᵒᵖ}
    {f g : y ⟶ restrictElement c x O}
    (h : f ≫ restrictElementHom c x O = g ≫ restrictElementHom c x O) : f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply BigFppfOver.eq_of_comp_openSubHom_eq O
  exact congrArg (fun m : y ⟶ x => m.unop.1.unop.hom) h

/-- An arrow `y ⟶ ξ` whose image lies in `O` factors through `ξ|_O ⟶ ξ`. -/
private theorem exists_comp_restrictElementHom_eq (x : (contractionFunctor c).Elementsᵒᵖ)
    (O : x.unop.1.unop.obj.left.obj.Opens) {y : (contractionFunctor c).Elementsᵒᵖ} (a : y ⟶ x)
    (h : Set.range ((BigFppfOver.toScheme B S hS).map a.unop.1.unop.hom) ⊆
      (O : Set x.unop.1.unop.obj.left.obj)) :
    ∃ a₁ : y ⟶ restrictElement c x O, a₁ ≫ restrictElementHom c x O = a := by
  obtain ⟨φ₁, hφ₁⟩ := BigFppfOver.exists_comp_openSubHom_eq O a.unop.1.unop.hom h
  have hy₁ : mapTriple c φ₁ (restrictElement c x O).unop.2 = y.unop.2 :=
    (mapTriple_comp c φ₁ _ x.unop.2).symm.trans
      ((congrArg (fun m => mapTriple c m x.unop.2) hφ₁).trans a.unop.2)
  refine ⟨Quiver.Hom.op
    ⟨(ObjectProperty.homMk φ₁ : y.unop.1.unop ⟶ (restrictElement c x O).unop.1.unop).op, hy₁⟩, ?_⟩
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  exact hφ₁

/-- **The lifting problems for `ξ|_O` are those for `ξ` landing in `O`.** Over a chart
`Spec Λ ⟶ S`, the lifting property of `ξ|_O` at a residue point `κ` of `O` is that of `ξ` at `κ`
followed by the inclusion `O ⟶ V`. -/
theorem liftsAtResiduePoint_restrictElement_iff {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S) (x : (contractionFunctor c).Elementsᵒᵖ)
    (O : x.unop.1.unop.obj.left.obj.Opens)
    (κ : Spec (.of k) ⟶
      ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj
        (restrictElement c x O)).left) :
    Deformation.Artin.LiftsAtResiduePoint iΛ
        (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
        ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj
          (restrictElement c x O)) (restrictElement c x O) rfl κ ↔
      Deformation.Artin.LiftsAtResiduePoint iΛ
        (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
        ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x) x rfl
        (κ ≫ ((Over.post B.inclusion).map
          (BigFppfOver.openSubHom B S hS x.unop.1.unop.obj O)).left) := by
  let ξ : Triple c x.unop.1.unop.obj := x.unop.2
  let ι₁ := BigFppfOver.openSubHom B S hS x.unop.1.unop.obj O
  let j := ((Over.post B.inclusion).map ι₁).left
  have : Mono j := inferInstanceAs (Mono O.ι)
  have hjrange : ∀ w, j w ∈ (O : Set x.unop.1.unop.obj.left.obj) := fun w => by
    rw [← Scheme.Opens.range_ι O]
    exact ⟨w, rfl⟩
  constructor
  · intro hU A A' f hf y z hy hz i hi a ha
    have : Subsingleton ((BigFppfOver.toScheme B S hS).obj y.unop.1.unop.obj) :=
      subsingleton_of_over_spec hy
    let φ := a.unop.1.unop.hom
    have ha' := ha
    simp only [Deformation.Artin.schemeMap, eqToHom_refl, Category.comp_id] at ha'
    obtain ⟨t₀, ht₀⟩ := exists_map_eq_of_comp_eq (T := y.unop.1.unop.obj)
      (V := x.unop.1.unop.obj) (congrArg Over.left hy).symm _ φ _ ha'
      (IsLocalRing.closedPoint k)
    have hrange : Set.range ((BigFppfOver.toScheme B S hS).map φ) ⊆
        (O : Set x.unop.1.unop.obj.left.obj) := by
      rintro _ ⟨t₁, rfl⟩
      rw [Subsingleton.elim t₁ t₀, ht₀]
      exact hjrange _
    obtain ⟨a₁, ha₁x⟩ := exists_comp_restrictElementHom_eq c x O a hrange
    let φ₁ : y.unop.1.unop.obj ⟶ BigFppfOver.openSubObj B S hS x.unop.1.unop.obj O :=
      a₁.unop.1.unop.hom
    have hφ₁ : φ₁ ≫ ι₁ = φ := congrArg (fun m : y ⟶ x => m.unop.1.unop.hom) ha₁x
    have ha₁ : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
        Deformation.Artin.schemeMap
          (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) hy rfl a₁ = κ := by
      have key : (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
          Deformation.Artin.schemeMap
            (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) hy rfl a₁ :
            Spec (.of k) ⟶ ((Over.post B.inclusion).obj
              (BigFppfOver.openSubObj B S hS x.unop.1.unop.obj O)).left) ≫ j =
            κ ≫ ((Over.post B.inclusion).map
              (BigFppfOver.openSubHom B S hS x.unop.1.unop.obj O)).left := by
        rw [← ha']
        simp only [Deformation.Artin.schemeMap, Category.assoc]
        congr 2
        show ((Over.post B.inclusion).map φ₁ ≫ (Over.post B.inclusion).map ι₁).left =
          ((Over.post B.inclusion).map φ).left
        rw [← Functor.map_comp, hφ₁]
      exact (cancel_mono j).1 key
    obtain ⟨b₁, hb₁⟩ := hU A A' f hf y z hy hz i hi a₁ ha₁
    exact ⟨b₁ ≫ restrictElementHom c x O, by rw [← Category.assoc, hb₁, ha₁x]⟩
  · intro hU A A' f hf y z hy hz i hi a₁ ha₁
    have : Subsingleton ((BigFppfOver.toScheme B S hS).obj y.unop.1.unop.obj) :=
      subsingleton_of_over_spec hy
    have : Subsingleton ((BigFppfOver.toScheme B S hS).obj z.unop.1.unop.obj) :=
      subsingleton_of_over_spec hz
    let φ₁ := a₁.unop.1.unop.hom
    have hy₁ : mapTriple c φ₁ (mapTriple c ι₁ ξ) = y.unop.2 := a₁.unop.2
    have hya : mapTriple c (φ₁ ≫ ι₁) ξ = y.unop.2 := (mapTriple_comp c φ₁ ι₁ ξ).trans hy₁
    let a : y ⟶ x := Quiver.Hom.op
      ⟨(ObjectProperty.homMk (φ₁ ≫ ι₁) : y.unop.1.unop ⟶ x.unop.1.unop).op, hya⟩
    have ha : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
        Deformation.Artin.schemeMap
          (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) hy rfl a =
        κ ≫ j := by
      rw [← ha₁]
      simp only [Deformation.Artin.schemeMap, eqToHom_refl, Category.comp_id]
      rfl
    obtain ⟨b, hb⟩ := hU A A' f hf y z hy hz i hi a ha
    let φ' := b.unop.1.unop.hom
    have hcomp : i.unop.1.unop.hom ≫ φ' = φ₁ ≫ ι₁ :=
      congrArg (fun m : y ⟶ x => m.unop.1.unop.hom) hb
    have ha₁' := ha₁
    simp only [Deformation.Artin.schemeMap, eqToHom_refl, Category.comp_id] at ha₁'
    obtain ⟨t₀, -⟩ := exists_map_eq_of_comp_eq (T := y.unop.1.unop.obj)
      (V := (restrictElement c x O).unop.1.unop.obj) (congrArg Over.left hy).symm _ φ₁ _ ha₁'
      (IsLocalRing.closedPoint k)
    have hrange : Set.range ((BigFppfOver.toScheme B S hS).map φ') ⊆
        (O : Set x.unop.1.unop.obj.left.obj) := by
      rintro _ ⟨t₁, rfl⟩
      have ht : t₁ = (BigFppfOver.toScheme B S hS).map i.unop.1.unop.hom t₀ :=
        Subsingleton.elim _ _
      rw [ht]
      have h3 := congrArg (fun m => (BigFppfOver.toScheme B S hS).map m) hcomp
      simp only [Functor.map_comp] at h3
      have h4 := congrArg (fun m => m t₀) h3
      exact h4 ▸ hjrange _
    obtain ⟨b₁, hb₁⟩ := exists_comp_restrictElementHom_eq c x O b hrange
    exact ⟨b₁, eq_of_comp_restrictElementHom_eq c x O (by rw [Category.assoc, hb₁]; exact hb)⟩

/-- **Versality is unchanged by restriction to an open subscheme.** For `ξ ∈ F(V)`, an open
`O ⊆ V` and a point `u` of `O`, the restriction `ξ|_O` is versal at `u` exactly when `ξ` is versal
at the image of `u` in `V`. Both sides are read as the lifting property over an affine chart of
`S`, where they agree by
`AlgebraicGeometry.Artin.ContractionSituation.liftsAtResiduePoint_restrictElement_iff`; the two
residue fields are identified by the open immersion, as in
`Deformation.Artin.isVersalAt_iff_restrict`. -/
theorem isVersalAt_restrictElement_iff (x : (contractionFunctor c).Elementsᵒᵖ)
    (O : x.unop.1.unop.obj.left.obj.Opens)
    (u : ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj
      (restrictElement c x O)).left) :
    Deformation.Artin.IsVersalAt
        ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj
          (restrictElement c x O))
        (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) u
        (restrictElement c x O) rfl ↔
      Deformation.Artin.IsVersalAt
        ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x)
        (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
        (((Over.post B.inclusion).map
          (BigFppfOver.openSubHom B S hS x.unop.1.unop.obj O)).left u) x rfl := by
  let qF := LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)
  let U : Over S := qF.obj x
  let U' : Over S := qF.obj (restrictElement c x O)
  let j : U'.left ⟶ U.left :=
    ((Over.post B.inclusion).map (BigFppfOver.openSubHom B S hS x.unop.1.unop.obj O)).left
  have : _root_.AlgebraicGeometry.IsOpenImmersion j :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion O.ι)
  let u' : U'.left := u
  have hjU : j ≫ U.hom = U'.hom :=
    Over.w ((Over.post B.inclusion).map (BigFppfOver.openSubHom B S hS x.unop.1.unop.obj O))
  -- an affine open `Spec Λ ⊆ S` through which the residue point of `j u'` factors
  let i := S.affineOpenCover.idx (Deformation.Artin.basePoint U (j u'))
  let Λ := (S.affineOpenCover.X i : Type u)
  let iΛ : Spec (.of Λ) ⟶ S := S.affineOpenCover.f i
  have hcov : Deformation.Artin.basePoint U (j u') ∈ Set.range iΛ.base :=
    S.affineOpenCover.covers _
  have hres : Spec.map (j.residueFieldMap u') ≫ U.left.fromSpecResidueField (j u') =
      U'.left.fromSpecResidueField u' ≫ j :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField j u'
  have hcomp : U'.left.fromSpecResidueField u' ≫ U'.hom =
      Spec.map (j.residueFieldMap u') ≫ (U.left.fromSpecResidueField (j u') ≫ U.hom) := by
    rw [← hjU, ← Category.assoc, ← hres, Category.assoc]
  have H : Set.range (U.left.fromSpecResidueField (j u') ≫ U.hom).base ⊆
      Set.range iΛ.base := by
    rintro _ ⟨s, rfl⟩
    have hs : s = IsLocalRing.closedPoint (U.left.residueField (j u')) :=
      Subsingleton.elim (α := Spec (U.left.residueField (j u'))) _ _
    rw [hs]
    exact hcov
  have H' : Set.range (U'.left.fromSpecResidueField u' ≫ U'.hom).base ⊆ Set.range iΛ.base := by
    rw [hcomp, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (Set.range_comp_subset_range _ _).trans H
  let algU : Algebra Λ (U.left.residueField (j u')) :=
    Deformation.Artin.chartResidueAlgebra iΛ U (j u') H
  let algU' : Algebra Λ (U'.left.residueField u') :=
    Deformation.Artin.chartResidueAlgebra iΛ U' u' H'
  have hcU := Deformation.Artin.algebraMap_chartResidueAlgebra iΛ U (j u') H
  have hcU' := Deformation.Artin.algebraMap_chartResidueAlgebra iΛ U' u' H'
  have hlin : ∀ l : Λ, (j.residueFieldMap u').hom
      (algebraMap Λ (U.left.residueField (j u') : Type u) l) =
      algebraMap Λ (U'.left.residueField u' : Type u) l := by
    have h : ((j.residueFieldMap u').hom.comp
        (algebraMap Λ (U.left.residueField (j u') : Type u))) =
        algebraMap Λ (U'.left.residueField u' : Type u) := by
      refine Deformation.Artin.ringHom_eq_of_specMap_comp_eq iΛ _ _ ?_
      have h₁ : CommRingCat.ofHom ((j.residueFieldMap u').hom.comp
          (algebraMap Λ (U.left.residueField (j u') : Type u))) =
          CommRingCat.ofHom (algebraMap Λ (U.left.residueField (j u') : Type u)) ≫
            j.residueFieldMap u' := rfl
      rw [h₁, Spec.map_comp, Category.assoc, hcU, ← Category.assoc, hres, Category.assoc, hjU,
        hcU']
    exact fun l => RingHom.congr_fun h l
  let e : (U.left.residueField (j u') : Type u) ≃ₐ[Λ] (U'.left.residueField u' : Type u) :=
    AlgEquiv.ofRingEquiv (f := (asIso (j.residueFieldMap u')).commRingCatIsoToRingEquiv) hlin
  have heq : U'.left.fromSpecResidueField u' ≫ j =
      Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) ≫
        U.left.fromSpecResidueField (j u') := hres.symm
  refine (Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_chart iΛ U' u' qF
    (restrictElement c x O) rfl hcU').trans ?_
  refine Iff.trans ?_ (Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_chart iΛ U (j u') qF
    x rfl hcU).symm
  refine (liftsAtResiduePoint_restrictElement_iff c (Λ := Λ) (k := U'.left.residueField u') iΛ x O
    (U'.left.fromSpecResidueField u')).trans ?_
  refine Iff.trans ?_ (Deformation.Artin.liftsAtResiduePoint_iff_changeResidueField e iΛ
    qF U x rfl (U.left.fromSpecResidueField (j u'))).symm
  exact Iff.of_eq (congrArg (Deformation.Artin.LiftsAtResiduePoint iΛ qF U x rfl) heq)

end AlgebraicGeometry.Artin.ContractionSituation

end
