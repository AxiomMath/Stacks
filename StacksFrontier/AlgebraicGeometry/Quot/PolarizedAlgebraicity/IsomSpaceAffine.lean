module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomGroupSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubschemeLocus

/-!
# The isomorphism spaces of `𝒫olarized` are affine over the base

Let `x`, `y` be two objects of the stack `𝒫olarized` of polarized proper flat families of finite
presentation over an object `U` of the big fppf site of a terminal scheme. The isomorphism presheaf
`Isom(x, y)` on the big fppf site of `U` is represented by an object `R` of that site (Stacks 0D42,
`AlgebraicGeometry.hasRepresentableDiagonal_polarizedStackUnconditional`). This file proves that
the structure morphism `R ⟶ U` is an *affine* morphism of schemes, so that
`Isom(x, y) ⟶ U` is separated and quasi-compact. These are the two properties of the base changes
of the diagonal that Stacks 0DPT asks for, beyond local finite presentation.

The proof of Stacks 0D42 represents, over every affine open `V` of `U`, the functor
`T ↦ Isom(x, y)(T) × Hom(T, V)` on affine test objects by the spectrum `Spec H_V` of the
corepresenting algebra of the isomorphisms of polarized families over `V`
(`AlgebraicGeometry.exists_bijective_polarizedIsomPresheaf_specAlgebraObj`). The open subscheme
`R ×_U V` of `R` represents the same functor on all test objects. A morphism of the site inducing a
bijection on the points with values in every affine test object is an isomorphism, both
representable presheaves being fppf sheaves
(`AlgebraicGeometry.Space.isIso_of_bijective_app_of_isAffine`). So `R ×_U V ≅ Spec H_V` is affine,
for every affine open `V`, which is affineness of `R ⟶ U`.

These declarations are helpers of the proof of Stacks 0DPU and carry no `@[stacks]` attribute.

This is a different route from the source's for the separatedness and quasi-compactness clauses
of Stacks 0DPT. The source maps `Isom_𝒫(υ, χ)` to `Isom_U(Y, X)`, uses Stacks 0DPN, 0DPP, 0DLW and,
for quasi-compactness over a Noetherian base, Stacks 0DPR and Hilbert polynomials. The affineness
proved here gives both clauses directly, over every base.

## Main results

All in the namespace `AlgebraicGeometry.PolarizedAlgebraicity`.

* `isAffine_preimage_of_bijective`: an object `R` of the big fppf site of `S` whose points over
  the open `V` of `S` are represented on affine test objects by an affine object `X` has affine
  preimage of `V`.
* `exists_iso_yoneda_isAffineHom_polarizedIsomSpace`: `Isom(x, y)` is represented by an object of
  the site of `U` whose structure morphism to `U` is affine.
* `isSeparated_relocalizeToYoneda_polarizedIsomSpace` and
  `isQuasiCompact_relocalizeToYoneda_polarizedIsomSpace`: `Isom(x, y) ⟶ U`, read over the
  terminal scheme (Stacks 04SG), is separated and quasi-compact.

## References

* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
* [Stacks Project, Tag 0DPT](https://stacks.math.columbia.edu/tag/0DPT)
* [Stacks Project, Tag 01S5](https://stacks.math.columbia.edu/tag/01S5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.PolarizedAlgebraicity

open BigFppfOver

section Site

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism into the object of the site given by an open `V` of `S` is unique: the open
immersion of `V` is a monomorphism. -/
theorem hom_ext_opensObj {T : BigFppfOver B S hS} {V : S.Opens} (f g : T ⟶ opensObj B S hS V) :
    f = g := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  apply (cancel_mono V.ι).mp
  exact (congrArg InducedCategory.Hom.hom (Over.w f)).trans
    (congrArg InducedCategory.Hom.hom (Over.w g)).symm

/-- **The preimage of an open of the base is affine once it is represented by an affine object
on affine test objects.** Let `R` be an object of the big fppf site of `S` and `V` an open of
`S`. Suppose that an object `X` with affine underlying scheme, with morphisms `π : X ⟶ R` and
`q : X ⟶ V`, induces for every affine test object `T` a bijection from `T ⟶ X` onto the pairs of a
morphism `T ⟶ R` and a morphism `T ⟶ V`. Then the preimage of `V` in `R` is affine: it is
isomorphic to `X`. -/
theorem isAffine_preimage_of_bijective (R X : BigFppfOver B S hS) (V : S.Opens)
    (hX : IsAffine ((toScheme B S hS).obj X)) (π : X ⟶ R) (q : X ⟶ opensObj B S hS V)
    (hbij : ∀ T : BigFppfOver B S hS, IsAffine ((toScheme B S hS).obj T) →
      Function.Bijective (fun f : T ⟶ X => (f ≫ π, f ≫ q))) :
    IsAffine (R.hom.hom ⁻¹ᵁ V) := by
  let W := R.hom.hom ⁻¹ᵁ V
  let O := opensRestrictObj B S hS R W
  let ι : O ⟶ R := opensRestrictHom B S hS R W
  -- every object of the site with a morphism to `V` lands in `W` under any map to `R`
  have hXV : Set.range ⇑(π.left.hom) ⊆ Set.range ⇑W.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show R.hom.hom (π.left.hom z) ∈ V
    have hπ : π.left.hom ≫ R.hom.hom = X.hom.hom := congrArg InducedCategory.Hom.hom (Over.w π)
    have hq : q.left.hom ≫ V.ι = X.hom.hom := congrArg InducedCategory.Hom.hom (Over.w q)
    rw [← Scheme.Hom.comp_apply, hπ, ← hq, Scheme.Hom.comp_apply]
    exact (q.left.hom z).2
  let m₀ := IsOpenImmersion.lift W.ι π.left.hom hXV
  have hm₀ : m₀ ≫ W.ι = π.left.hom := IsOpenImmersion.lift_fac W.ι π.left.hom hXV
  let m : X ⟶ O := Over.homMk (ObjectProperty.homMk (X := X.left) (Y := O.left) m₀) (by
    apply ObjectProperty.hom_ext
    show m₀ ≫ (W.ι ≫ R.hom.hom) = X.hom.hom
    rw [← Category.assoc, hm₀]
    exact congrArg InducedCategory.Hom.hom (Over.w π))
  have hmι : m ≫ ι = π := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hm₀
  have hιmono : Mono ι := by
    refine ⟨fun a b hab => ?_⟩
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply (cancel_mono W.ι).mp
    exact congrArg (fun k => k.left.hom) hab
  have hiso : IsIso (yoneda.map m) := by
    refine Space.isIso_of_bijective_app_of_isAffine (isSheaf_yoneda_obj B S hS X)
      (isSheaf_yoneda_obj B S hS O) (yoneda.map m) fun T hT => ?_
    refine ⟨fun f f' hff' => (hbij T hT).1 ?_, fun g => ?_⟩
    · have h1 : f ≫ m = f' ≫ m := hff'
      refine Prod.ext ?_ (hom_ext_opensObj B S hS _ _)
      show f ≫ π = f' ≫ π
      rw [← hmι, ← Category.assoc, h1, Category.assoc]
    · have hT' : Set.range ⇑T.hom.hom ⊆ (V : Set S) := by
        rintro _ ⟨t, rfl⟩
        have hg : (g ≫ ι).left.hom ≫ R.hom.hom = T.hom.hom :=
          congrArg InducedCategory.Hom.hom (Over.w (g ≫ ι))
        rw [← hg, Scheme.Hom.comp_apply]
        exact (g.left.hom t).2
      obtain ⟨f, hf⟩ := (hbij T hT).2 (g ≫ ι, homOfRangeLe B S hS V hT')
      refine ⟨f, ?_⟩
      show f ≫ m = g
      apply hιmono.right_cancellation
      rw [Category.assoc, hmι]
      exact congrArg Prod.fst hf
  have : IsIso m := Yoneda.fullyFaithful.isIso_of_isIso_map m
  let em := (toScheme B S hS).mapIso (asIso m)
  exact @IsAffine.of_isIso _ _ em.inv em.isIso_inv hX

end Site

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (hT : IsTerminal (B.obj hS))

/-- **`Isom(x, y)` is represented by an object affine over `U`.** For two objects `x`, `y` of
`𝒫olarized` over `U`, the isomorphism presheaf `Isom(x, y)` on the big fppf site of `U` is
isomorphic to the presheaf represented by an object `R` of that site whose structure morphism to
`U` is affine: over every affine open `V` of `U`, the preimage of `V` in `R` is the spectrum of the
corepresenting algebra of the isomorphisms over `V` from the proof of Stacks 0D42. -/
theorem exists_iso_yoneda_isAffineHom_polarizedIsomSpace (U : BigFppfOver B S hS)
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U) :
    ∃ (R : BigFppfOver B U.left.obj U.left.property)
      (_ : Stack.isomSpace B S hS (polarizedStackUnconditional B hS hT) U x y ≅ yoneda.obj R),
      IsAffineHom R.hom.hom := by
  have hrep := isRepresentable_isomPresheaf_of_corepresented B hS hT U x y
    (isSheaf_polarizedIsomPresheaf B hS hT U x y) fun a b hab _ =>
      PolarizedFamily.exists_corepresentation_isoOverBase_of_sectionBijection
        Stacks.AlgebraicGeometry.ProjectiveDeformation.polarizedIsoSectionBijection a b hab
  let F := Stack.isomSpace B S hS (polarizedStackUnconditional B hS hT) U x y
  let R := F.reprX
  let e : yoneda.obj R ≅ F := F.reprW
  refine ⟨R, e.symm, ⟨fun V hV => ?_⟩⟩
  have hV' : IsAffine (B.inclusion.obj ((polarizedRestriction B hS hT U x
      (BigFppfOver.opensObj B U.left.obj U.left.property V)).1).base) :=
    isAffine_polarizedRestriction_base B hS hT U x _ hV
  obtain ⟨H, _, ι, hcard, hcorep⟩ :=
    PolarizedFamily.exists_corepresentation_isoOverBase_of_sectionBijection
      Stacks.AlgebraicGeometry.ProjectiveDeformation.polarizedIsoSectionBijection _ _
      (polarizedRestriction_base_eq_base B hS hT U x y
        (BigFppfOver.opensObj B U.left.obj U.left.property V))
  have hsize : (Spec (CommRingCat.of H)).size ≤ U.left.obj.size := by
    rw [Scheme.size_Spec]
    refine max_le U.left.obj.aleph0_le_size (hcard.trans (max_le U.left.obj.aleph0_le_size ?_))
    refine ((B.inclusion.obj _).mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩).trans ?_
    exact (Scheme.size_congr (eqToIso (congrArg B.inclusion.obj
      (polarizedRestriction_base B hS hT U x _)))).le.trans
        (Scheme.size_le_of_isOpenImmersion V.ι)
  obtain ⟨p, hp⟩ := exists_bijective_polarizedIsomPresheaf_specAlgebraObj B hS hT U x y
    _ H ι (hsize.trans_lt U.left.property) hcorep
  let X := BigFppfOver.specAlgebraObj B U.left.property
    (polarizedRestriction_base B hS hT U x (BigFppfOver.opensObj B U.left.obj U.left.property V))
    ι (hsize.trans_lt U.left.property)
  let π : X ⟶ R := Yoneda.fullyFaithful.preimage (p ≫ e.inv)
  have hπ : ∀ (T : BigFppfOver B U.left.obj U.left.property) (f : T ⟶ X),
      f ≫ π = e.inv.app (op T) (p.app (op T) f) := fun T f =>
    congrArg (fun k => k.app (op T) f) (Yoneda.fullyFaithful.map_preimage (p ≫ e.inv))
  have hXaff : IsAffine ((BigFppfOver.toScheme B U.left.obj U.left.property).obj X) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of H)))
  refine isAffine_preimage_of_bijective B U.left.obj U.left.property R X V hXaff π
    (BigFppfOver.specAlgebraHom B U.left.property _ ι (hsize.trans_lt U.left.property))
    fun T hTa => ?_
  have he : Function.Bijective (Prod.map (e.inv.app (op T))
      (id : (T ⟶ BigFppfOver.opensObj B U.left.obj U.left.property V) → _)) :=
    (((yoneda.obj R).mapIso (Iso.refl _)).symm ≪≫ e.app (op T)).symm.toEquiv.bijective.prodMap
      Function.bijective_id
  convert he.comp (hp T hTa) using 1
  exact funext fun f => Prod.ext (hπ T f) rfl

/-- A property of morphisms of presheaves that respects isomorphisms holds for `F ⟶ U` when `F` is
isomorphic to a representable presheaf `yoneda.obj R` whose structure map to `U` has it. -/
private theorem relocalizeToYoneda_of_iso_yoneda
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    (U : BigFppfOver B S hS) (F : (BigFppfOver B U.left.obj U.left.property)ᵒᵖ ⥤ Type u)
    (R : BigFppfOver B U.left.obj U.left.property) (e : F ≅ yoneda.obj R)
    (h : P (yoneda.map (Over.homMk R.hom rfl : (Over.map U.hom).obj R ⟶ Over.mk U.hom))) :
    P (OverShriek.relocalizeToYoneda U.hom F) := by
  rw [← Stack.relocalizeToYoneda_comp_map U.hom e.hom]
  refine (MorphismProperty.cancel_left_of_respectsIso P _ _).2 ?_
  rw [← Stack.relocalizeToYoneda_yoneda U.hom R]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).2 h

/-- **`Isom(x, y) ⟶ U` is separated.** For two objects `x`, `y` of `𝒫olarized` over `U`, the
structure morphism of the isomorphism space `Isom(x, y)`, read over the terminal scheme (Stacks
04SG), is separated: `Isom(x, y)` is represented by an object affine over `U`
(`exists_iso_yoneda_isAffineHom_polarizedIsomSpace`), and an affine morphism of
schemes is separated (Stacks 01S7). -/
theorem isSeparated_relocalizeToYoneda_polarizedIsomSpace (U : BigFppfOver B S hS)
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U) :
    Space.IsSeparated B S hS (OverShriek.relocalizeToYoneda U.hom
      (Stack.isomSpace B S hS (polarizedStackUnconditional B hS hT) U x y)) := by
  obtain ⟨R, e, hR⟩ := exists_iso_yoneda_isAffineHom_polarizedIsomSpace B hS hT U x y
  have := Space.isSeparated_respectsIso B S hS
  refine relocalizeToYoneda_of_iso_yoneda B hS (@Space.IsSeparated B S hS) U _ R e ?_
  exact (Space.isSeparated_yoneda_map_iff B S hS _).2 (inferInstanceAs (IsSeparated R.hom.hom))

/-- **`Isom(x, y) ⟶ U` is quasi-compact.** For two objects `x`, `y` of `𝒫olarized` over `U`, the
structure morphism of the isomorphism space `Isom(x, y)`, read over the terminal scheme (Stacks
04SG), is quasi-compact: `Isom(x, y)` is represented by an object affine over `U`
(`exists_iso_yoneda_isAffineHom_polarizedIsomSpace`), and an affine morphism of
schemes is quasi-compact (Stacks 01S7). -/
theorem isQuasiCompact_relocalizeToYoneda_polarizedIsomSpace (U : BigFppfOver B S hS)
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U) :
    Space.IsQuasiCompact B S hS (OverShriek.relocalizeToYoneda U.hom
      (Stack.isomSpace B S hS (polarizedStackUnconditional B hS hT) U x y)) := by
  obtain ⟨R, e, hR⟩ := exists_iso_yoneda_isAffineHom_polarizedIsomSpace B hS hT U x y
  have : MorphismProperty.RespectsIso (@Space.IsQuasiCompact B S hS) :=
    MorphismProperty.RespectsIso.of_respects_arrow_iso _ (fun f g e hf =>
      Space.isQuasiCompact_of_arrowIso B S hS f.hom g.hom e.hom.left e.hom.right
        e.hom.w hf)
  exact relocalizeToYoneda_of_iso_yoneda B hS (@Space.IsQuasiCompact B S hS) U _ R e
    (Space.isQuasiCompact_yoneda_map_of_isAffineHom B S hS _ hR)

end AlgebraicGeometry.PolarizedAlgebraicity

end
