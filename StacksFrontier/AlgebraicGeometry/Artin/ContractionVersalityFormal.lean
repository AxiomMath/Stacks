module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityStack
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.NilpotentLift

/-!
# Lifting along nilpotent thickenings through a formally smooth completion map

Let `F` be an fppf sheaf on the big fppf site of `S`, `T ⊆ |F|` a set of points and
`g : F_{/T} ⟶ W` a morphism from the completion of `F` along `T` (Stacks 0AMC) to a sheaf `W`.
If `g` is formally smooth (Stacks 049S), then every section of `F` with point-set image in `T`
over an affine object extends, along any closed immersion of affine objects with nilpotent
kernel, to a section with image in `T` lying over a prescribed section of `W`: the completion of a
sheaf is the subfunctor of sections with image in `T`
(`AlgebraicGeometry.Space.completionSheafIsoSubfunctor`), and formally smooth morphisms lift
along nilpotent thickenings
(`AlgebraicGeometry.Space.FormallySmooth.exists_isLift_of_isNilpotent`).

This is the form in which the smoothness of `x̂` given by Stacks 0GI9 is used in the second case of
the proof of Stacks 0GIA.

## Main results

* `AlgebraicGeometry.Space.exists_lift_of_formallySmooth_completion`: the lifting property.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0GIA](https://stacks.math.columbia.edu/tag/0GIA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Lifting through a formally smooth completion map.** Let `F` be an fppf sheaf,
`g : F_{/T} ⟶ W` formally smooth, `i : T₀ ⟶ T₁` a closed immersion of affine objects with
nilpotent kernel on global sections, `φ ∈ F(T₀)` with point-set image in `T`, and `w ∈ W(T₁)`
restricting to `g(φ)`. Then there is `φ' ∈ F(T₁)` with point-set image in `T`, restricting to
`φ`, with `g(φ') = w`. -/
theorem exists_lift_of_formallySmooth_completion {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) {T : Set (points B S hS F)}
    {W : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (g : completionSheaf B S hS F T ⟶ W) (hg : FormallySmooth g.hom)
    {T₀ T₁ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T₁)]
    (i : T₀ ⟶ T₁)
    (hi : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hnil : IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom))
    (φ : F.obj (op T₀)) (hφ : HasImageIn B S hS F T T₀ φ) (w : W.obj.obj (op T₁))
    (hw : W.obj.map i.op w = g.hom.app (op T₀) (FormalSpace.presheafSection B S hS φ hφ)) :
    ∃ (φ' : F.obj (op T₁)) (hφ' : HasImageIn B S hS F T T₁ φ'), F.map i.op φ' = φ ∧
      g.hom.app (op T₁) (FormalSpace.presheafSection B S hS φ' hφ') = w := by
  let e := completionSheafIsoSubfunctor B S hS hF T
  obtain ⟨z, hz₁, hz₂⟩ := FormallySmooth.exists_isLift_of_isNilpotent hg i hi hnil
    (FormalSpace.presheafSection B S hS φ hφ) w hw.symm
  have hze : FormalSpace.presheafSection B S hS (e.hom.app (op T₁) z).1.down
      (e.hom.app (op T₁) z).2 = z :=
    congrArg (fun ψ => ψ.app (op T₁) z) e.hom_inv_id
  have hφe : e.hom.app (op T₀) (FormalSpace.presheafSection B S hS φ hφ) = ⟨ULift.up φ, hφ⟩ :=
    congrArg (fun ψ => ψ.app (op T₀) ⟨ULift.up φ, hφ⟩) e.inv_hom_id
  refine ⟨(e.hom.app (op T₁) z).1.down, (e.hom.app (op T₁) z).2, ?_, ?_⟩
  · have h1 := NatTrans.naturality_apply e.hom i.op z
    rw [hz₁, hφe] at h1
    exact (congrArg (fun s => s.1.down) h1).symm
  · rw [hze]
    exact hz₂

end Space

/-! ### The thickenings of a lifting problem for versality -/

section TestMaps

/-- The morphism of spectra induced by a surjection of Artinian local rings, read through
equalities of schemes, has nilpotent kernel on global sections. -/
theorem isNilpotent_ker_appTop_of_eq_specMap {R' R : CommRingCat.{u}} [IsArtinianRing R']
    [IsLocalRing R'] [Nontrivial R] (f : R' ⟶ R)
    {X Y : Scheme.{u}} (e : X = Spec R) (e' : Y = Spec R') (m : X ⟶ Y)
    (hm : eqToHom e.symm ≫ m ≫ eqToHom e' = Spec.map f) :
    IsNilpotent (RingHom.ker m.appTop.hom) := by
  subst e e'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hm
  subst hm
  have hkerApp : RingHom.ker (Spec.map f).appTop.hom =
      (RingHom.ker f.hom).comap (Scheme.ΓSpecIso R').hom.hom := by
    calc
      _ = RingHom.ker ((Scheme.ΓSpecIso R).hom.hom.comp (Spec.map f).appTop.hom) :=
        (RingHom.ker_comp_of_injective _
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1).symm
      _ = RingHom.ker (f.hom.comp (Scheme.ΓSpecIso R').hom.hom) := by
        rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality]
      _ = _ := (RingHom.comap_ker _ _).symm
  have hle : RingHom.ker f.hom ≤ IsLocalRing.maximalIdeal R' := by
    intro r hr
    by_contra hmem
    have hu : IsUnit r := (IsLocalRing.mem_maximalIdeal r).not.mp hmem |> not_not.mp
    have := hu.map f.hom
    rw [RingHom.mem_ker.mp hr] at this
    exact not_isUnit_zero this
  obtain ⟨n, hn⟩ : IsNilpotent (IsLocalRing.maximalIdeal R') := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := R')
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
  refine ⟨n, eq_bot_iff.mpr ?_⟩
  rw [hkerApp]
  have hbot : RingHom.ker (Scheme.ΓSpecIso R').hom.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R').hom).1
  refine (Ideal.le_comap_pow _ n).trans ?_
  refine (Ideal.comap_mono (Ideal.pow_right_mono hle n)).trans ?_
  rw [hn, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot, hbot]

/-- The morphism of spectra induced by a surjection of rings, read through equalities of schemes,
is a closed immersion. -/
theorem isClosedImmersion_of_eq_specMap {R' R : CommRingCat.{u}} (f : R' ⟶ R)
    (hf : Function.Surjective f.hom) {X Y : Scheme.{u}} (e : X = Spec R) (e' : Y = Spec R')
    (m : X ⟶ Y) (hm : eqToHom e.symm ≫ m ≫ eqToHom e' = Spec.map f) :
    IsClosedImmersion m := by
  subst e e'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hm
  subst hm
  exact IsClosedImmersion.spec_of_surjective f hf

/-- The morphism of spectra induced by a surjection of Artinian local rings, read through
equalities of schemes, is a closed immersion with nilpotent kernel on global sections. -/
private theorem isClosedImmersion_and_isNilpotent_ker_of_eq_specMap {R' R : CommRingCat.{u}}
    [IsArtinianRing R'] [IsLocalRing R'] [Nontrivial R] (f : R' ⟶ R)
    (hf : Function.Surjective f.hom) {X Y : Scheme.{u}} (e : X = Spec R) (e' : Y = Spec R')
    (m : X ⟶ Y) (hm : eqToHom e.symm ≫ m ≫ eqToHom e' = Spec.map f) :
    IsClosedImmersion m ∧ IsNilpotent (RingHom.ker m.appTop.hom) :=
  ⟨isClosedImmersion_of_eq_specMap f hf e e' m hm,
    isNilpotent_ker_appTop_of_eq_specMap f e e' m hm⟩

end TestMaps

namespace FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Versality of `g : V_{/Z} ⟶ W` from lifting along nilpotent thickenings near the point.**
If every section of `V_{/Z}` over an affine object, landing in a set `O ∋ v`, extends along every
closed immersion of affine objects with nilpotent kernel over every prescribed section of `W`,
then `g` is versal at `v`: the lifting problems of Stacks 07XZ are such extensions, over spectra of
Artinian local rings. -/
theorem isVersalAtCompletion_of_lift {V : BigFppfOver B S hS}
    (Z : Set (Space.points B S hS (yoneda.obj V))) {W : FppfSheaf B S hS}
    (g : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
    (O : Set ((Over.post B.inclusion).obj V).left) (v : ((Over.post B.inclusion).obj V).left)
    (hvO : v ∈ O)
    (hlift : ∀ (T₀ T₁ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T₁)]
      (i : T₀ ⟶ T₁),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) →
      IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom) →
      ∀ (φ : T₀ ⟶ V) (hφ : Space.HasImageIn B S hS (yoneda.obj V) Z T₀ φ),
        Set.range ((BigFppfOver.toScheme B S hS).map φ) ⊆ O →
        ∀ w : W.obj.obj (op T₁),
          W.obj.map i.op w = g.hom.app (op T₀) (presheafSection B S hS (T := Z) φ hφ) →
          ∃ (φ' : T₁ ⟶ V) (hφ' : Space.HasImageIn B S hS (yoneda.obj V) Z T₁ φ'),
            i ≫ φ' = φ ∧ g.hom.app (op T₁) (presheafSection B S hS (T := Z) φ' hφ') = w) :
    IsVersalAtCompletion B S hS V Z W g v := by
  let : Algebra (S.presheaf.stalk (Deformation.Artin.basePoint ((Over.post B.inclusion).obj V) v))
      (((Over.post B.inclusion).obj V).left.residueField v) :=
    Deformation.Artin.residueFieldAlgebra ((Over.post B.inclusion).obj V) v
  intro A A' f hf T T' hT hT' i hi φ hφ hres w hw
  have e : (BigFppfOver.toScheme B S hS).obj T = Spec (.of A) := congrArg Over.left hT
  have e' : (BigFppfOver.toScheme B S hS).obj T' = Spec (.of A') := congrArg Over.left hT'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := by rw [e']; infer_instance
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj T) :=
    Artin.ContractionSituation.subsingleton_of_over_spec hT
  obtain ⟨hci, hnil⟩ := isClosedImmersion_and_isNilpotent_ker_of_eq_specMap (R' := .of A')
    (R := .of A) (CommRingCat.ofHom f.hom.toRingHom) hf e e'
    ((BigFppfOver.toScheme B S hS).map i) hi
  obtain ⟨t, ht⟩ := Artin.ContractionSituation.exists_map_eq_of_residue (T := T) (V := V) v
    (congrArg Over.left hT).symm _ φ hres
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map φ) ⊆ O := by
    rintro _ ⟨t₁, rfl⟩
    rw [Subsingleton.elim t₁ t, ht]
    exact hvO
  exact hlift T T' i hci hnil φ hφ hrange w hw

/-- **Lifting near an open from formal smoothness of the restriction to that open.** Let
`ι₀ : V₀ ⟶ V` be a morphism of the site whose underlying morphism of schemes is an open immersion.
If the restriction `V₀_{/Z₀} ⟶ V_{/Z} ⟶ W` of `g : V_{/Z} ⟶ W` is formally smooth, then sections
of `V_{/Z}` landing in the image of `V₀` extend along closed immersions of affine objects with
nilpotent kernel over every prescribed section of `W`. -/
theorem lift_of_formallySmooth_of_isOpenImmersion {V V₀ : BigFppfOver B S hS}
    (Z : Set (Space.points B S hS (yoneda.obj V))) {W : FppfSheaf B S hS}
    (g : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W) (ι₀ : V₀ ⟶ V)
    (hι₀ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι₀))
    (hFS : Space.FormallySmooth (Space.completionSheafMap B S hS (yoneda.map ι₀) Z ≫ g).hom)
    (T₀ T₁ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T₁)]
    (i : T₀ ⟶ T₁)
    (hi : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hnil : IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom))
    (φ : T₀ ⟶ V) (hφ : Space.HasImageIn B S hS (yoneda.obj V) Z T₀ φ)
    (hrange : Set.range ((BigFppfOver.toScheme B S hS).map φ) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map ι₀))
    (w : W.obj.obj (op T₁))
    (hw : W.obj.map i.op w = g.hom.app (op T₀) (presheafSection B S hS (T := Z) φ hφ)) :
    ∃ (φ' : T₁ ⟶ V) (hφ' : Space.HasImageIn B S hS (yoneda.obj V) Z T₁ φ'),
      i ≫ φ' = φ ∧ g.hom.app (op T₁) (presheafSection B S hS (T := Z) φ' hφ') = w := by
  obtain ⟨φ₀, hφ₀⟩ := BigFppfOver.exists_comp_eq_of_isOpenImmersion ι₀ hι₀ φ hrange
  have hφ₀' : Space.HasImageIn B S hS (yoneda.obj V₀)
      (Space.pointsMap B S hS _ (yoneda.map ι₀) ⁻¹' Z) T₀ φ₀ :=
    (hasImageIn_preimage_pointsMap_iff B S hS (yoneda.map ι₀) Z T₀ φ₀).2 (by
      change Space.HasImageIn B S hS (yoneda.obj V) Z T₀ (φ₀ ≫ ι₀)
      rw [hφ₀]; exact hφ)
  have hsec : ∀ (T : BigFppfOver B S hS) (ψ : T ⟶ V₀) (h₁)
      (h₂ : Space.HasImageIn B S hS (yoneda.obj V) Z T (ψ ≫ ι₀)),
      (Space.completionSheafMap B S hS (yoneda.map ι₀) Z).hom.app (op T)
        (presheafSection B S hS ψ h₁) = presheafSection B S hS (T := Z) (ψ ≫ ι₀) h₂ :=
    fun T ψ h₁ h₂ => completionSheafMap_presheafSection B S hS (yoneda.map ι₀) Z ψ h₁ h₂
  have hw' : W.obj.map i.op w =
      (Space.completionSheafMap B S hS (yoneda.map ι₀) Z ≫ g).hom.app (op T₀)
        (presheafSection B S hS φ₀ hφ₀') := by
    rw [hw]
    change _ = g.hom.app (op T₀) ((Space.completionSheafMap B S hS (yoneda.map ι₀) Z).hom.app
      (op T₀) (presheafSection B S hS φ₀ hφ₀'))
    rw [hsec T₀ φ₀ hφ₀' (by rw [hφ₀]; exact hφ)]
    exact congrArg _ (presheafSection_congr B S hS hφ₀.symm _ _)
  obtain ⟨ψ, hψ, hres, hval⟩ := Space.exists_lift_of_formallySmooth_completion
    (isAlgebraicSpace_yoneda B S hS _).isSheaf _ hFS i hi hnil φ₀ hφ₀' w hw'
  have hψ' : Space.HasImageIn B S hS (yoneda.obj V) Z T₁ (ψ ≫ ι₀) :=
    (hasImageIn_preimage_pointsMap_iff B S hS (yoneda.map ι₀) Z T₁ ψ).1 hψ
  refine ⟨ψ ≫ ι₀, hψ', ?_, ?_⟩
  · have hres' : i ≫ ψ = φ₀ := hres
    rw [← Category.assoc, hres', hφ₀]
  · rw [← hval]
    change _ = g.hom.app (op T₁) ((Space.completionSheafMap B S hS (yoneda.map ι₀) Z).hom.app
      (op T₁) (presheafSection B S hS ψ hψ))
    rw [hsec T₁ ψ hψ hψ']

end FormalSpace

namespace Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- **Versality of `ξ` at a point outside `Z` from lifting of `u'`.** Let
`ξ = (Z, u', x̂) ∈ F(V)` and `v ∉ Z`. If every section of `V ∖ Z` over an affine object all of
whose points go to `v` extends, along every closed immersion of affine objects with nilpotent
kernel, over every prescribed section of `U'` restricting to its image under `u'`, then `ξ` is
versal at `v`: a lifting problem for versality of `ξ` at `v` is such an extension, a triple on the
spectrum of an Artinian local ring whose closed point avoids `Z` being a point of `U'`. -/
theorem isVersalAt_of_lift_openPart (x : (contractionFunctor c).Elementsᵒᵖ)
    (v : ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x).left)
    (hv : (Space.pointsEquivScheme B S hS x.unop.1.unop.obj).symm v ∉
      (x.unop.2 : Triple c x.unop.1.unop.obj).Z)
    (hlift : ∀ (T₀ T₁ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T₁)]
      [Subsingleton ((BigFppfOver.toScheme B S hS).obj T₀)]
      [Subsingleton ((BigFppfOver.toScheme B S hS).obj T₁)]
      (_t₀ : (BigFppfOver.toScheme B S hS).obj T₀) (i : T₀ ⟶ T₁),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) →
      IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom) →
      ∀ (φ : T₀ ⟶ x.unop.1.unop.obj)
        (hφ : φ ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj x.unop.1.unop.obj)
          (x.unop.2 : Triple c x.unop.1.unop.obj).Zᶜ).obj (op T₀)),
        (∀ t, (BigFppfOver.toScheme B S hS).map φ t = v) →
        ∀ s : c.U'.toFunctor.obj (op T₁),
          c.U'.toFunctor.map i.op s =
            (x.unop.2 : Triple c x.unop.1.unop.obj).u.app (op T₀) ⟨φ, hφ⟩ →
          ∃ (φ' : T₁ ⟶ x.unop.1.unop.obj)
            (hφ' : φ' ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj x.unop.1.unop.obj)
              (x.unop.2 : Triple c x.unop.1.unop.obj).Zᶜ).obj (op T₁)),
            i ≫ φ' = φ ∧ (x.unop.2 : Triple c x.unop.1.unop.obj).u.app (op T₁) ⟨φ', hφ'⟩ = s) :
    Deformation.Artin.IsVersalAt
      ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x)
      (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) v x rfl := by
  let ξ : Triple c x.unop.1.unop.obj := x.unop.2
  let U := (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x
  let : Algebra (S.presheaf.stalk (Deformation.Artin.basePoint U v)) (U.left.residueField v) :=
    Deformation.Artin.residueFieldAlgebra U v
  intro A A' f hf y z hy hz i hi a ha
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj y.unop.1.unop.obj) :=
    subsingleton_of_over_spec hy
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj z.unop.1.unop.obj) :=
    subsingleton_of_over_spec hz
  let ι := i.unop.1.unop.hom
  let φ := a.unop.1.unop.hom
  have ha' := ha
  simp only [eqToHom_refl, Category.comp_id] at ha'
  obtain ⟨t, ht⟩ := exists_map_eq_of_residue (T := y.unop.1.unop.obj)
    (V := x.unop.1.unop.obj) v (congrArg Over.left hy).symm _ φ ha'
  have hφv : ∀ t', (BigFppfOver.toScheme B S hS).map φ t' = v := fun t' => by
    rw [Subsingleton.elim t' t, ht]
  have e : (BigFppfOver.toScheme B S hS).obj y.unop.1.unop.obj = Spec (.of A) :=
    congrArg Over.left hy
  have e' : (BigFppfOver.toScheme B S hS).obj z.unop.1.unop.obj = Spec (.of A') :=
    congrArg Over.left hz
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj z.unop.1.unop.obj) := by
    rw [e']; infer_instance
  obtain ⟨hci, hnil⟩ := isClosedImmersion_and_isNilpotent_ker_of_eq_specMap (R' := .of A')
    (R := .of A) (CommRingCat.ofHom f.hom.toRingHom) hf e e'
    ((BigFppfOver.toScheme B S hS).map ι) hi
  have hya : mapTriple c φ ξ = y.unop.2 := a.unop.2
  have hzi : mapTriple c ι z.unop.2 = y.unop.2 := i.unop.2
  have hmem : φ ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj x.unop.1.unop.obj)
      ξ.Zᶜ).obj (op y.unop.1.unop.obj) :=
    (Space.mem_openSubspaceOfPoints_iff_of_subsingleton (T := y.unop.1.unop.obj) φ t _).2
      (by rw [ht]; exact hv)
  have hyZ : (y.unop.2 : Triple c y.unop.1.unop.obj).Z = ∅ := by
    rw [← hya]; exact (mapTriple_Z_eq_empty_iff c φ ξ).2 hmem
  have hzZ : (z.unop.2 : Triple c z.unop.1.unop.obj).Z = ∅ := by
    rcases Triple.Z_eq_empty_or_eq_univ (z.unop.2 : Triple c z.unop.1.unop.obj) with h | h
    · exact h
    · exfalso
      have h0 := Triple.mapTriple_Z_eq_univ c ι _ h
      rw [hzi, hyZ] at h0
      exact (Set.mem_empty_iff_false ((Space.pointsEquivScheme B S hS _).symm t)).1
        (h0 ▸ Set.mem_univ _)
  let sz := (z.unop.2 : Triple c z.unop.1.unop.obj).uPoint hzZ
  have hcompat : c.U'.toFunctor.map ι.op sz = ξ.u.app (op y.unop.1.unop.obj) ⟨φ, hmem⟩ := by
    rw [← Triple.uPoint_mapTriple ι _ hzZ (Triple.mapTriple_Z_eq_empty c ι _ hzZ),
      Triple.uPoint_congr hzi _ hyZ,
      ← Triple.uPoint_congr hya ((mapTriple_Z_eq_empty_iff c φ ξ).2 hmem) hyZ,
      uPoint_mapTriple_eq c φ ξ hmem]
  obtain ⟨φ', hφ', hcomp, hval⟩ := hlift _ _ t ι hci hnil φ hmem hφv sz hcompat
  have hZ' := (mapTriple_Z_eq_empty_iff c φ' ξ).2 hφ'
  have hb : mapTriple c φ' ξ = z.unop.2 := by
    refine Triple.ext_of_Z_eq_empty hZ' hzZ ?_
    change ((mapTriple c φ' ξ).uPoint hZ').1 = sz.1
    rw [uPoint_mapTriple_eq c φ' ξ hφ' hZ', hval]
  refine ⟨Quiver.Hom.op ⟨(ObjectProperty.homMk φ' : z.unop.1.unop ⟶ x.unop.1.unop).op, hb⟩,
    ?_⟩
  apply Quiver.Hom.unop_inj
  apply Functor.Elements.hom_ext
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  exact hcomp

end Artin.ContractionSituation

end AlgebraicGeometry

end
