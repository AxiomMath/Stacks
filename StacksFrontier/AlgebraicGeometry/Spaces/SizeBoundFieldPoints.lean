module

public import StacksFrontier.AlgebraicGeometry.Descent.FppfSingletonSheafEqualizer
public import StacksFrontier.AlgebraicGeometry.Size.FiniteTypeCount
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductUniformAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOverHom
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedGlobalFunctionsIntegral

/-!
# Axiom `[-1]` for algebraic spaces

Axiom `[-1]` of Artin's axioms (Stacks, Section 07XZ) is the set-theoretic condition that the
values of a functor on the spectra of fields of finite type over the base `S` have cardinality
bounded by the size of a single object of the big fppf site of `S`. This file proves that every
algebraic space over `S` satisfies it, for algebraic spaces with values in any universe
`Type (max w u)` (`AlgebraicGeometry.Space.IsAlgebraicSpaceULift`), so that it applies both to
the algebraic spaces of `Type u` of the library and to the reductions of formal algebraic spaces,
whose values lie in `Type (u + 1)`.

## The argument

Let `U ⟶ Y` be a scheme atlas of `Y`, surjective and étale. Let `T` be an object of the site
whose underlying scheme is the spectrum of a field `K`, locally of finite type over `S`, and let
`y ∈ Y(T)`. The base change `P = T ×_Y U` is a scheme, surjective and étale over `T`; choosing a
point of it, an affine open around it and a maximal ideal of its ring of sections gives the
spectrum `Spec L ⟶ P` of a field `L` with `Spec L ⟶ T` of finite type. Up to isomorphism over
`T` it is one of a fixed set of affine `T`-schemes of finite type indexed by a set `I` of
cardinality at most `ℵ₀ * 2 ^ max ℵ₀ #K`
(`AlgebraicGeometry.AffineFiniteTypeOver.exists_index_affineFiniteTypeOver`). The morphism
`Spec L ⟶ T` is flat, surjective and locally of finite presentation, so `Y(T) ⟶ Y(Spec L)` is
injective, and `y` restricted to `Spec L` is the image of a morphism `Spec L ⟶ U`. Hence `y` is
determined by an index `i ∈ I` and a morphism of schemes from the `i`-th model to `U`. Those
morphisms are counted by `AlgebraicGeometry.Scheme.SpecToEquivOfField`.

All cardinals that occur are at most `2 ^ μ` with `μ = max (size S) (size U)`, which lies below
the cutoff of the site because the cutoff is a strong limit.

## Main results

* `AlgebraicGeometry.Space.exists_cardinal_bound_fieldPoints`: the bound as a cardinal below the
  cutoff.
* `AlgebraicGeometry.Space.exists_sizeBound_fieldPoints`: axiom `[-1]` in the form of
  Stacks 07Y1, the bound being the size of an object of the site.

## References

* [Stacks Project, Section 07XZ](https://stacks.math.columbia.edu/tag/07XZ)
* [Stacks Project, Tag 07Y1](https://stacks.math.columbia.edu/tag/07Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe w u

namespace AlgebraicGeometry

/-- The product of two cardinals at most `2 ^ μ` is at most `2 ^ μ` for `μ` infinite. -/
private theorem mul_le_two_pow {a b μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (ha : a ≤ 2 ^ μ)
    (hb : b ≤ 2 ^ μ) : a * b ≤ 2 ^ μ :=
  (mul_le_mul' ha hb).trans (mul_eq_self (hμ.trans (cantor μ).le)).le

/-- A sigma type over an index type and with fibres all of cardinality at most `2 ^ μ`, for `μ`
infinite, has cardinality at most `2 ^ μ`. -/
private theorem mk_sigma_le_two_pow {ι : Type u} (f : ι → Type u) {μ : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hι : #ι ≤ 2 ^ μ) (hf : ∀ i, #(f i) ≤ 2 ^ μ) : #(Σ i, f i) ≤ 2 ^ μ := by
  rw [Cardinal.mk_sigma]
  exact (sum_le_mk_mul_iSup _).trans (mul_le_two_pow hμ hι (ciSup_le' hf))

/-- The morphisms of schemes from the spectrum of a field `L` to a scheme `X` number at most
`2 ^ μ` when `X` and `L` have size and cardinality at most the infinite cardinal `μ`. -/
theorem mk_hom_spec_field_le {L : Type u} [Field L] (X : Scheme.{u}) {μ : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hX : X.size ≤ μ) (hL : #L ≤ μ) :
    #(Spec (.of L) ⟶ X) ≤ 2 ^ μ := by
  rw [Cardinal.mk_congr (Scheme.SpecToEquivOfField L X)]
  refine mk_sigma_le_two_pow _ hμ
    (X.mk_le_two_pow_size.trans (power_le_power_left two_ne_zero hX)) fun x => ?_
  have hκ : #(X.residueField x) ≤ μ :=
    (mk_le_of_surjective (IsLocalRing.residue_surjective (R := X.presheaf.stalk x))).trans
      ((X.mk_stalk_le_size x).trans hX)
  calc #(X.residueField x ⟶ CommRingCat.of L)
      ≤ #(X.residueField x → L) :=
        mk_le_of_injective (f := fun φ => ⇑φ.hom) fun φ ψ h =>
          CommRingCat.hom_ext (RingHom.ext (congrFun h))
    _ = #L ^ #(X.residueField x) := (power_def _ _).symm
    _ ≤ μ ^ μ := (power_le_power_right hL).trans
        (power_le_power_left (aleph0_pos.trans_le hμ).ne' hκ)
    _ = 2 ^ μ := power_self_eq hμ

/-- A commutative ring has cardinality at most the size of its spectrum. -/
theorem mk_le_size_spec (R : Type u) [CommRing R] : #R ≤ (Spec (.of R)).size :=
  (mk_le_of_injective (f := fun r => (Scheme.ΓSpecIso (.of R)).inv r) fun a b hab => by
    simpa using congrArg (Scheme.ΓSpecIso (.of R)).hom hab).trans
    ((Spec (.of R)).mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩)

/-- The morphisms from schemes `V i` isomorphic to spectra of fields of cardinality at most the
infinite cardinal `μ`, indexed by a set of cardinality at most `2 ^ μ`, to a scheme of size at
most `μ` number at most `2 ^ μ`. -/
theorem mk_sigma_hom_le {I : Type u} (V : I → Scheme.{u}) (X : Scheme.{u}) {μ : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hX : X.size ≤ μ) (hI : #I ≤ 2 ^ μ)
    (hV : ∀ i, ∃ (L : Type u) (_ : Field L), #L ≤ μ ∧ Nonempty (V i ≅ Spec (.of L))) :
    #(Σ i, V i ⟶ X) ≤ 2 ^ μ := by
  refine mk_sigma_le_two_pow _ hμ hI fun i => ?_
  obtain ⟨L, _, hL, ⟨eL⟩⟩ := hV i
  rw [Cardinal.mk_congr (eL.homCongr (Iso.refl X))]
  exact mk_hom_spec_field_le X hμ hX hL

/-- A surjective morphism locally of finite type onto a nonempty scheme admits a point
`Spec L ⟶ P` with values in a field such that the composite to the target is locally of finite
type. -/
theorem exists_spec_field_hom_locallyOfFiniteType {P T : Scheme.{u}} (q : P ⟶ T) [Surjective q]
    [LocallyOfFiniteType q] [Nonempty T] :
    ∃ (L : Type u) (_ : Field L) (ι : Spec (.of L) ⟶ P), LocallyOfFiniteType (ι ≫ q) := by
  obtain ⟨p, -⟩ := q.surjective (Nonempty.some inferInstance)
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, -⟩ :=
    P.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  have : Nonempty V := ⟨⟨p, hpV⟩⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(P, V)
  let : Field (Γ(P, V) ⧸ m) := Ideal.Quotient.field m
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : _root_.AlgebraicGeometry.IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have : LocallyOfFiniteType hV.fromSpec := locallyOfFiniteType_of_isOpenImmersion _
  exact ⟨Γ(P, V) ⧸ m, inferInstance,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ hV.fromSpec, inferInstance⟩

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Restriction of a sheaf on the big fppf site along a surjective flat morphism locally of
finite presentation is injective. -/
theorem injective_map_op_of_isSheaf_of_flat {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) {V U : BigFppfOver B S hS}
    (π : V ⟶ U) (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map π))
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map π))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map π)) :
    Function.Injective (F.map π.op) := fun _ _ h =>
  (BigFppfOver.isSheafFor_singleton_of_isSheaf_of_flat B S hS F hF π hsurj hflat
    hlfp).isSeparatedFor.ext fun _ _ ⟨⟩ => h

/-- Given a scheme atlas `f` of `Y` and a set of models `V i` of the affine schemes of finite
type over the nonempty scheme of an object `U`, every section of `Y` over `U` restricts, along
one of the models isomorphic to the spectrum of a field, to the image of a morphism to the
atlas. -/
theorem exists_map_siteMapOver_eq_app {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {U₀ : BigFppfOver B S hS} {f : uliftYoneda.{w}.obj U₀ ⟶ Y}
    (hfs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f)
    (hfe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f)
    {U : BigFppfOver B S hS} [Nonempty ((BigFppfOver.toScheme B S hS).obj U)] {I : Type u}
    (V : I → AffineFiniteTypeOver ((BigFppfOver.toScheme B S hS).obj U))
    (hV : ∀ W : AffineFiniteTypeOver ((BigFppfOver.toScheme B S hS).obj U),
      ∃ i, ∃ e : (V i).obj ≅ W.obj, e.hom ≫ W.hom = (V i).hom)
    (hcont : ∀ i, B.Contains (V i).obj) {μ : Cardinal.{u}}
    (hμ : ((BigFppfOver.toScheme B S hS).obj U).size ≤ μ) (y : Y.obj (op U)) :
    ∃ (i : I) (h : (V i).obj ⟶ (BigFppfOver.toScheme B S hS).obj U₀)
      (hh : h ≫ B.inclusion.map U₀.hom = B.inclusion.map
        (BigFppfOver.siteObjectOver B S hS U (hcont i) (V i).hom).hom),
      (∃ (L : Type u) (_ : Field L), #L ≤ μ ∧ Nonempty ((V i).obj ≅ Spec (.of L))) ∧
      Y.map (BigFppfOver.siteMapOver B S hS U (hcont i) (V i).hom).op y =
        f.app _ (ULift.up (homOfSchemeHom B S hS
          (T := BigFppfOver.siteObjectOver B S hS U (hcont i) (V i).hom) (T' := U₀) h hh)) := by
  let g : uliftYoneda.{w}.obj U ⟶ Y := uliftYonedaEquiv.symm y
  let rep := hfs.rep
  let P := rep.pullback g
  let snd : P ⟶ U := rep.snd g
  let fst : P ⟶ U₀ := rep.fst' g
  have hsq : uliftYoneda.{w}.map fst ≫ f = uliftYoneda.{w}.map snd ≫ g := by
    rw [rep.map_fst']
    exact rep.w g
  have : Surjective ((BigFppfOver.toScheme B S hS).map snd) := hfs.property_snd g
  have : Etale ((BigFppfOver.toScheme B S hS).map snd) := hfe.property_snd g
  have hres : Y.map snd.op y = f.app _ (ULift.up fst) := by
    have h1 := uliftYonedaEquiv_naturality g snd.op
    rw [Equiv.apply_symm_apply] at h1
    rw [h1]
    show uliftYonedaEquiv.{w} (uliftYoneda.{w}.map snd ≫ g) = _
    rw [← hsq, uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
  obtain ⟨L, _, ιW, _⟩ :=
    exists_spec_field_hom_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map snd)
  let W : AffineFiniteTypeOver ((BigFppfOver.toScheme B S hS).obj U) :=
    ⟨Spec (.of L), ιW ≫ (BigFppfOver.toScheme B S hS).map snd, inferInstance, inferInstance⟩
  obtain ⟨i, e, he⟩ := hV W
  have := quasiCompact_of_subsingleton W.hom
  have hL : #L ≤ μ :=
    ((mk_le_size_spec L).trans (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact W.hom)).trans
      hμ
  let h : (V i).obj ⟶ _ := e.hom ≫ ιW ≫ (BigFppfOver.toScheme B S hS).map fst
  have hκ : (e.hom ≫ ιW) ≫ B.inclusion.map P.hom = B.inclusion.map
      (BigFppfOver.siteObjectOver B S hS U (hcont i) (V i).hom).hom := by
    rw [← toScheme_map_comp_inclusion_map_hom B S hS snd]
    show _ = (V i).hom ≫ B.inclusion.map U.hom
    rw [← he]
    simp [W]
  have hh : h ≫ B.inclusion.map U₀.hom = B.inclusion.map
      (BigFppfOver.siteObjectOver B S hS U (hcont i) (V i).hom).hom := by
    rw [← hκ]
    simp only [h, Category.assoc, toScheme_map_comp_inclusion_map_hom B S hS fst]
  let κ := homOfSchemeHom B S hS
    (T := BigFppfOver.siteObjectOver B S hS U (hcont i) (V i).hom) (T' := P) (e.hom ≫ ιW) hκ
  have hκmap : (BigFppfOver.toScheme B S hS).map κ = e.hom ≫ ιW :=
    toScheme_map_homOfSchemeHom B S hS _ hκ
  have hπ : BigFppfOver.siteMapOver B S hS U (hcont i) (V i).hom = κ ≫ snd :=
    (BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, hκmap]
      show (V i).hom = _
      rw [← he]
      exact (Category.assoc _ _ _).symm)
  have hfst : κ ≫ fst = homOfSchemeHom B S hS
      (T := BigFppfOver.siteObjectOver B S hS U (hcont i) (V i).hom) (T' := U₀) h hh :=
    (BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, hκmap]
      exact (Category.assoc _ _ _).trans (toScheme_map_homOfSchemeHom B S hS
        (T := BigFppfOver.siteObjectOver B S hS U (hcont i) (V i).hom) (T' := U₀) h hh).symm)
  refine ⟨i, h, hh, ⟨L, inferInstance, hL, ⟨e⟩⟩, ?_⟩
  rw [hπ, op_comp, Functor.map_comp_apply, hres, ← hfst]
  exact (NatTrans.naturality_apply f κ.op _).symm

/-- Given a scheme atlas `f` of the fppf sheaf `Y` whose source and `S` have size at most the
infinite cardinal `μ`, the values of `Y` on an object whose underlying scheme is the spectrum of a
field locally of finite type over `S` have cardinality at most `2 ^ μ`. -/
theorem mk_obj_le_two_pow_of_atlas {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {U₀ : BigFppfOver B S hS}
    {f : uliftYoneda.{w}.obj U₀ ⟶ Y}
    (hfs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f)
    (hfe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f)
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hSμ : S.size ≤ μ)
    (hU₀ : ((BigFppfOver.toScheme B S hS).obj U₀).size ≤ μ) (U : BigFppfOver B S hS)
    (K : Type u) [Field K] (eK : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of K))
    [LocallyOfFiniteType (B.inclusion.map U.hom)] :
    #(Y.obj (op U)) ≤ Cardinal.lift.{w} (2 ^ μ) := by
  set X₀ := (BigFppfOver.toScheme B S hS).obj U₀
  set T := (BigFppfOver.toScheme B S hS).obj U
  have : IsAffine T := IsAffine.of_isIso eK.hom
  have : Subsingleton T :=
    ⟨fun a b => (Scheme.homeoOfIso eK).injective (Subsingleton.elim _ _)⟩
  have : Nonempty T := ⟨eK.inv (Nonempty.some inferInstance)⟩
  have : IsIntegral T := isIntegral_of_isOpenImmersion eK.hom
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isOpenImmersion eK.hom
  have : QuasiCompact (B.inclusion.map U.hom) :=
    quasiCompact_of_subsingleton (X := T) (B.inclusion.map U.hom)
  have hTS : T.size ≤ μ :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact (B.inclusion.map U.hom)).trans hSμ
  obtain ⟨I, V, hI, hV⟩ := exists_index_affineFiniteTypeOver T
  have hcont : ∀ i, B.Contains (V i).obj := fun i =>
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact (V i).hom).trans_lt U.left.property
  let π : ∀ i, BigFppfOver.siteObjectOver B S hS U (hcont i) (V i).hom ⟶ U := fun i =>
    BigFppfOver.siteMapOver B S hS U (hcont i) (V i).hom
  let good : I → Prop := fun i =>
    ∃ (L : Type u) (_ : Field L), #L ≤ μ ∧ Nonempty ((V i).obj ≅ Spec (.of L))
  choose ι hom hhom hgood hres using exists_map_siteMapOver_eq_app hfs hfe V hV hcont hTS
  let ψ : Y.obj (op U) → ULift.{w} (Σ i : {i // good i}, ((V i.1).obj ⟶ X₀)) :=
    fun y => ULift.up ⟨⟨ι y, hgood y⟩, hom y⟩
  have hres₂ : ∀ y s, (ψ y).down = s → ∃ hh, Y.map (π s.1.1).op y =
      f.app _ (ULift.up (homOfSchemeHom B S hS
        (T := BigFppfOver.siteObjectOver B S hS U (hcont s.1.1) (V s.1.1).hom) (T' := U₀)
          s.2 hh)) := by
    rintro y s rfl
    exact ⟨hhom y, hres y⟩
  have hinj : Function.Injective ψ := by
    intro y y' hyy'
    obtain ⟨_, e₁⟩ := hres₂ y _ rfl
    obtain ⟨_, e₂⟩ := hres₂ y' _ (congrArg ULift.down hyy').symm
    obtain ⟨L, _, -, ⟨eL⟩⟩ := hgood y
    have : Nonempty ((BigFppfOver.toScheme B S hS).obj
        (BigFppfOver.siteObjectOver B S hS U (hcont (ι y)) (V (ι y)).hom)) :=
      ⟨(eL.inv (Nonempty.some inferInstance) : (V (ι y)).obj)⟩
    exact injective_map_op_of_isSheaf_of_flat hY (π (ι y))
      ⟨fun _ => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩ inferInstance
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr (V (ι y)).locallyOfFiniteType)
      (e₁.trans e₂.symm : Y.map (π (ι y)).op y = Y.map (π (ι y)).op y')
  have hIμ : #I ≤ 2 ^ μ :=
    hI.trans (mul_le_two_pow hμ (hμ.trans (cantor μ).le)
      (power_le_power_left two_ne_zero (max_le hμ
        ((T.mk_sections_le_size ⟨⊤, isAffineOpen_top T⟩).trans hTS))))
  calc #(Y.obj (op U)) ≤ #(ULift.{w} (Σ i : {i // good i}, ((V i.1).obj ⟶ X₀))) :=
        mk_le_of_injective hinj
    _ = Cardinal.lift.{w} #(Σ i : {i // good i}, ((V i.1).obj ⟶ X₀)) := mk_uLift _
    _ ≤ Cardinal.lift.{w} (2 ^ μ) := lift_le.mpr <| mk_sigma_hom_le
        (fun i : {i // good i} => (V i.1).obj) X₀ hμ hU₀ ((mk_subtype_le _).trans hIμ) fun i => i.2

/-- **Axiom `[-1]` for algebraic spaces, as a cardinal bound.** For an algebraic space `Y` over
`S` with values in `Type (max w u)` there is a cardinal `ν` with `size S ≤ ν < cutoff` bounding
the cardinalities of the values of `Y` on all objects of the site whose underlying scheme is the
spectrum of a field locally of finite type over `S`. -/
theorem exists_cardinal_bound_fieldPoints {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hY : IsAlgebraicSpaceULift.{w} B S hS Y) :
    ∃ ν : Cardinal.{u}, S.size ≤ ν ∧ ν < B.cutoff ∧
      ∀ (U : BigFppfOver B S hS) (K : Type u) [Field K],
        Nonempty ((BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of K)) →
        LocallyOfFiniteType (B.inclusion.map U.hom) →
        #(Y.obj (op U)) ≤ Cardinal.lift.{w} ν := by
  obtain ⟨U₀, f, hfs, hfe⟩ := hY.exists_atlas
  set μ : Cardinal.{u} := max S.size ((BigFppfOver.toScheme B S hS).obj U₀).size
  refine ⟨2 ^ μ, (le_max_left _ _).trans (cantor μ).le,
    B.cutoff_isStrongPrelimit (max_lt hS U₀.left.property), fun U K _ ⟨eK⟩ _ => ?_⟩
  exact mk_obj_le_two_pow_of_atlas hY.isSheaf hfs hfe (S.aleph0_le_size.trans (le_max_left _ _))
    (le_max_left _ _) (le_max_right _ _) U K eK

/-- An object of the big fppf site over `S` whose size is at least a given cardinal `ν` with
`size S ≤ ν < cutoff`, as soon as no object over `S` has an underlying scheme with a point when
`S` is empty. Used to turn a cardinal bound into the bound by the size of an object that axiom
`[-1]` asks for. -/
theorem exists_le_size_of_le_of_lt (ν : Cardinal.{u}) (hSν : S.size ≤ ν) (hν : ν < B.cutoff) :
    ∃ T₀ : BigFppfOver B S hS, ∀ U : BigFppfOver B S hS,
      Nonempty ((BigFppfOver.toScheme B S hS).obj U) →
        ν ≤ ((BigFppfOver.toScheme B S hS).obj T₀).size := by
  by_cases hne : Nonempty S
  · obtain ⟨T₀, hT₀⟩ := BigFppfOver.exists_size_ge B S hS hne ν hSν hν
    exact ⟨T₀, fun _ _ => hT₀⟩
  · exact ⟨Over.mk (𝟙 _), fun U ⟨x⟩ => (hne ⟨(B.inclusion.map U.hom) x⟩).elim⟩

/-- **Axiom `[-1]` for algebraic spaces** (Stacks, Section 07XZ, in the form of Stacks 07Y1).
For an algebraic space `Y` over `S` with values in `Type (max w u)` there is an object `T₀` of
the big fppf site of `S` such that `#Y(U) ≤ size T₀` for every object `U` whose underlying
scheme is the spectrum of a field and is locally of finite type over `S`. -/
theorem exists_sizeBound_fieldPoints {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hY : IsAlgebraicSpaceULift.{w} B S hS Y) :
    ∃ T₀ : BigFppfOver B S hS, ∀ (U : BigFppfOver B S hS) (K : Type u) [Field K],
      Nonempty ((BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of K)) →
      LocallyOfFiniteType (B.inclusion.map U.hom) →
      #(Y.obj (op U)) ≤ Cardinal.lift.{w} ((BigFppfOver.toScheme B S hS).obj T₀).size := by
  obtain ⟨ν, hSν, hν, hb⟩ := exists_cardinal_bound_fieldPoints hY
  obtain ⟨T₀, hT₀⟩ := exists_le_size_of_le_of_lt (hS := hS) ν hSν hν
  exact ⟨T₀, fun U K _ ⟨e⟩ hlft => (hb U K ⟨e⟩ hlft).trans
    (lift_le.mpr (hT₀ U ⟨e.inv (Nonempty.some inferInstance)⟩))⟩

end Space

end AlgebraicGeometry
