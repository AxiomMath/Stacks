module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionOverFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecQuotientInSite
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.RingTheory.Rig.HenselizationDescent

/-!
# Morphisms of completions of affine Noetherian schemes

Let `S` be a scheme contained in a big fppf site `B`. For a morphism `g : V ⟶ X` of objects of
the site and a set `T` of points of `X`, write `g_{/T} : V_{/g⁻¹T} ⟶ X_{/T}` for the completion
`AlgebraicGeometry.Space.completionOverFunctor`. For Noetherian affine `X`, `X'`, `Y`, a closed
`T ⊆ |X|`, a morphism `f : X' ⟶ X` locally of finite type and étale over `X ∖ T`, and
`h : Y ⟶ X`, every morphism `α : Y_{/T} ⟶ X'_{/T}` over `X_{/T}` is `a_{/T} ∘ b_{/T}⁻¹` for an
étale `b : Y' ⟶ Y` of affine schemes with `b_{/T}` an isomorphism and a morphism `a : Y' ⟶ X'`
over `X`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.completionEval`: a morphism of completions evaluated on the
  section given by a section of the source with point-set image in the completed set, and read in
  the target presheaf.
* `AlgebraicGeometry.FormalSpace.specAlgOver`: the spectrum of an algebra over the global sections
  of an affine object `Y` of the site, as an object of the site over `Y`.
* `AlgebraicGeometry.FormalSpace.stageMap` and `AlgebraicGeometry.FormalSpace.stageAlgHom`: the
  values of `α` on the infinitesimal neighbourhoods `Spec(C ⧸ (IC)ⁿ)` of the closed fibre of `Y`,
  assembled into an `A`-algebra map `B → C^∧` into the `IC`-adic completion.

## Main results

* `AlgebraicGeometry.FormalSpace.completionSheaf_hom_ext`: two morphisms of completions agree when
  they agree on the sections over affine objects of the site.
* `AlgebraicGeometry.FormalSpace.isIso_completionSheafMap_specAlgOverι`: the completion of an étale
  neighbourhood `Spec C' ⟶ Y` of the closed fibre is an isomorphism.
* `AlgebraicGeometry.FormalSpace.exists_etale_completion_factorization`: every morphism
  `α : Y_{/T} ⟶ X'_{/T}` over `X_{/T}` is `a_{/T} ∘ b_{/T}⁻¹` for an étale `b : Y' ⟶ Y` with
  `b_{/T}` an isomorphism and a morphism `a : Y' ⟶ X'` over `X`.

## References

* [Stacks Project, Tag 0AR3](https://stacks.math.columbia.edu/tag/0AR3)
* [Stacks Project, Tag 0AKJ](https://stacks.math.columbia.edu/tag/0AKJ)
* [Stacks Project, Tag 0GDB](https://stacks.math.columbia.edu/tag/0GDB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### Algebra maps out of an étale neighbourhood of a closed fibre -/

/-- Let `C → C'` be étale with `C ⧸ J ≅ C' ⧸ JC'`. Into a `C`-algebra `R` in which `J`
generates a nilpotent ideal there is exactly one `C`-algebra map `C' → R`. -/
theorem existsUnique_algHom_of_etale_of_bijective_quotientMap
    {C C' R : Type*} [CommRing C] [CommRing C'] [CommRing R]
    [Algebra C C'] [Algebra.Etale C C'] [Algebra C R] (J : Ideal C)
    (hbij : Function.Bijective
      (Ideal.quotientMap (J.map (algebraMap C C')) (algebraMap C C') Ideal.le_comap_map))
    (hJ : IsNilpotent (J.map (algebraMap C R))) :
    Nonempty (C' →ₐ[C] R) ∧ ∀ g₁ g₂ : C' →ₐ[C] R, g₁ = g₂ := by
  set JR := J.map (algebraMap C R)
  let e := RingEquiv.ofBijective _ hbij
  have he : ∀ c : C, e.symm (Ideal.Quotient.mk _ (algebraMap C C' c)) = Ideal.Quotient.mk J c := by
    intro c
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  refine ⟨⟨Algebra.FormallySmooth.lift JR hJ
    { toRingHom := (Ideal.quotientMap JR (algebraMap C R) Ideal.le_comap_map).comp
        (e.symm.toRingHom.comp (Ideal.Quotient.mk _))
      commutes' := fun c ↦ by
        show Ideal.quotientMap JR (algebraMap C R) Ideal.le_comap_map
          (e.symm (Ideal.Quotient.mk _ (algebraMap C C' c))) = _
        rw [he]
        rfl }⟩, fun g₁ g₂ ↦ ?_⟩
  refine Algebra.FormallyUnramified.ext JR hJ fun x ↦ ?_
  obtain ⟨c', hc'⟩ := hbij.2 (Ideal.Quotient.mk _ x)
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  have hx : x - algebraMap C C' c ∈ J.map (algebraMap C C') := by
    rw [← Ideal.Quotient.eq]
    exact hc'.symm
  have key : ∀ g : C' →ₐ[C] R,
      Ideal.Quotient.mk JR (g x) = Ideal.Quotient.mk JR (algebraMap C R c) := by
    intro g
    rw [Ideal.Quotient.eq, ← g.commutes, ← map_sub]
    have : Ideal.map (g : C' →+* R) (J.map (algebraMap C C')) = JR := by
      rw [Ideal.map_map]
      congr 1
      exact g.comp_algebraMap
    exact this ▸ Ideal.mem_map_of_mem (g : C' →+* R) hx
  rw [key g₁, key g₂]

/-! ### Sections with point-set image in a closed subset -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism `y : U ⟶ Y` over `h : Y ⟶ X` has point-set image in `|h|⁻¹ T` exactly when every
point of `U` lands, in the scheme underlying `X`, in the image of `T`. -/
theorem hasImageIn_yoneda_preimage_iff {X Y U : BigFppfOver B S hS} (h : Y ⟶ X)
    (T : Set (Space.points B S hS (yoneda.obj X))) (y : U ⟶ Y) :
    Space.HasImageIn B S hS (yoneda.obj Y)
        (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) U y ↔
      ∀ v : (BigFppfOver.toScheme B S hS).obj U,
        (BigFppfOver.toScheme B S hS).map (y ≫ h) v ∈ Space.pointsToScheme B S hS X '' T := by
  have hy : (yonedaEquiv.symm y : yoneda.obj U ⟶ yoneda.obj Y) = yoneda.map y := by
    ext V g
    simp [yonedaEquiv]
  rw [Space.hasImageIn_iff_range_subset, hy]
  constructor
  · intro H v
    obtain ⟨p, rfl⟩ := Space.surjective_pointsToScheme B S hS U v
    refine ⟨_, H ⟨p, rfl⟩, ?_⟩
    rw [Space.pointsToScheme_pointsMap, Space.pointsToScheme_pointsMap, Functor.map_comp]
    rfl
  · rintro H _ ⟨p, rfl⟩
    obtain ⟨t, ht, he⟩ := H (Space.pointsToScheme B S hS U p)
    show Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h)
      (Space.pointsMap B S hS (yoneda.obj U) (yoneda.map y) p) ∈ T
    convert ht using 1
    apply Space.injective_pointsToScheme B S hS X
    rw [he, Space.pointsToScheme_pointsMap, Space.pointsToScheme_pointsMap, Functor.map_comp]
    rfl

/-- If every point of an affine scheme `V` maps into the zero locus of an ideal `I` of global
functions of `Z`, then `I` generates a nilpotent ideal of functions on `V`, provided `I` is
finitely generated. -/
theorem isNilpotent_map_appTop_of_range_subset_zeroLocus {V Z : Scheme.{u}} [IsAffine V]
    (g : V ⟶ Z) (I : Ideal Γ(Z, ⊤)) (hI : I.FG)
    (hg : ∀ v, g v ∈ Z.zeroLocus (U := ⊤) (I : Set Γ(Z, ⊤))) :
    IsNilpotent (I.map g.appTop.hom) := by
  have huniv : V.zeroLocus (U := ⊤) (g.appTop.hom '' (I : Set Γ(Z, ⊤))) = Set.univ := by
    have := Scheme.preimage_zeroLocus g (U := ⊤) (I : Set Γ(Z, ⊤))
    change _ = V.zeroLocus (U := ⊤) (g.appTop.hom '' (I : Set Γ(Z, ⊤))) at this
    rw [← this]
    exact Set.eq_univ_of_forall hg
  have hspec : PrimeSpectrum.zeroLocus (g.appTop.hom '' (I : Set Γ(Z, ⊤))) = Set.univ := by
    rw [← V.isoSpec_image_zeroLocus, huniv, Set.image_univ]
    exact Set.range_eq_univ.2
      (AlgebraicGeometry.Scheme.Hom.homeomorph V.isoSpec.hom).bijective.surjective
  have hle : I.map g.appTop.hom ≤ (⊥ : Ideal Γ(V, ⊤)).radical := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun a ha ↦ (PrimeSpectrum.zeroLocus_eq_univ_iff _).1 hspec ⟨a, ha, rfl⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (hI.map _)
  exact ⟨n, le_bot_iff.1 hn⟩

/-- A ring map out of a commutative ring of `CommRingCat`, as a morphism to the bundled
codomain. -/
abbrev homOf {R : CommRingCat.{u}} {A₀ : Type u} [CommRing A₀] (f : R →+* A₀) :
    R ⟶ CommRingCat.of A₀ :=
  ConcreteCategory.ofHom (C := CommRingCat) f

/-- A ring map into a commutative ring of `CommRingCat`, as a morphism from the bundled
domain. -/
abbrev homTo {A₀ : Type u} [CommRing A₀] {R : CommRingCat.{u}} (f : A₀ →+* R) :
    CommRingCat.of A₀ ⟶ R :=
  ConcreteCategory.ofHom (C := CommRingCat) f

/-! ### Global sections and morphisms into affine schemes -/

/-- On global sections, `Spec.map φ ≫ Z.isoSpec.inv` is `φ` followed by the inverse of
`Γ(Spec R) ≅ R`. -/
theorem appTop_SpecMap_comp_isoSpec_inv {Z : Scheme.{u}} [IsAffine Z] {R : CommRingCat.{u}}
    (φ : Γ(Z, ⊤) ⟶ R) :
    (Spec.map φ ≫ Z.isoSpec.inv).appTop = φ ≫ (Scheme.ΓSpecIso R).inv := by
  have h1 : Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso Γ(Z, ⊤)).hom, Iso.inv_hom_id, ← Scheme.toSpecΓ_appTop,
      ← Scheme.Hom.comp_appTop]
    show (Z.isoSpec.hom ≫ Z.isoSpec.inv).appTop = _
    rw [Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rw [Scheme.Hom.comp_appTop, h1, ← cancel_mono (Scheme.ΓSpecIso R).hom, Category.assoc,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- On global sections, `V.toSpecΓ ≫ Spec.map ψ` is `ψ`, read through `Γ(Spec R) ≅ R`. -/
theorem ΓSpecIso_inv_appTop_toSpecΓ_SpecMap {V : Scheme.{u}} {R : CommRingCat.{u}}
    (ψ : R ⟶ Γ(V, ⊤)) :
    (Scheme.ΓSpecIso R).inv ≫ (V.toSpecΓ ≫ Spec.map ψ).appTop = ψ := by
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc,
    ← cancel_mono (Scheme.ΓSpecIso Γ(V, ⊤)).inv, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, ← cancel_epi (Scheme.ΓSpecIso R).hom, Iso.hom_inv_id_assoc]
  exact (Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality ψ)

/-- If a morphism of affine Noetherian schemes, locally of finite type, is étale at every point
lying over the complement of the zero locus of `I`, then on global sections it is étale away from
`V(I)`. -/
theorem isEtaleOutside_of_forall_etaleAt {X' X : Scheme.{u}} [IsAffine X'] [IsAffine X]
    [IsNoetherian X] (f : X' ⟶ X) [LocallyOfFiniteType f] (I : Ideal Γ(X, ⊤))
    (h : ∀ x, f x ∉ X.zeroLocus (U := ⊤) (I : Set Γ(X, ⊤)) → EtaleAt f x) :
    letI := f.appTop.hom.toAlgebra
    Rig.IsEtaleOutside I Γ(X', ⊤) := by
  let := f.appTop.hom.toAlgebra
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian f
  intro p hp
  set x := X'.isoSpec.inv p with hx
  have hprime : (isAffineOpen_top X').primeIdealOf ⟨x, trivial⟩ = p := by
    apply (AlgebraicGeometry.Scheme.Hom.homeomorph X'.isoSpec.inv).injective
    have h₁ := (isAffineOpen_top X').fromSpec_primeIdealOf ⟨x, trivial⟩
    rwa [IsAffineOpen.fromSpec_top] at h₁
  have hfx : f x ∉ X.zeroLocus (U := ⊤) (I : Set Γ(X, ⊤)) := by
    intro hmem
    apply hp
    have h₁ : x ∈ f ⁻¹' X.zeroLocus (U := ⊤) (I : Set Γ(X, ⊤)) := hmem
    rw [Scheme.preimage_zeroLocus] at h₁
    have h₂ : p ∈ X'.isoSpec.inv ⁻¹' X'.zeroLocus (U := ⊤)
        ((f.app ⊤).hom '' (I : Set Γ(X, ⊤))) := h₁
    rw [Scheme.isoSpec_inv_preimage_zeroLocus] at h₂
    exact fun a ha ↦ h₂ ⟨a, ha, rfl⟩
  have het : IsEtaleAt f x := (isEtaleAt_iff_etaleAt f x).2 (h x hfx)
  have key := (isEtaleLocalHom_iff_isEtaleAt_affine f x ⊤ (isAffineOpen_top X') trivial ⊤
    (isAffineOpen_top X) le_top).1 het
  have happ : f.appLE ⊤ ⊤ le_top = f.appTop := Scheme.Hom.appLE_eq_app f
  rwa [happ, hprime] at key

/-- A morphism into a scheme whose map on global sections makes every element of `I` nilpotent
lands in the zero locus of `I`. -/
theorem mem_zeroLocus_of_isNilpotent {W Z : Scheme.{u}} (g : W ⟶ Z) (I : Ideal Γ(Z, ⊤))
    (hg : ∀ a ∈ I, IsNilpotent (g.appTop.hom a)) (w : W) :
    g w ∈ Z.zeroLocus (U := ⊤) (I : Set Γ(Z, ⊤)) := by
  rw [Scheme.mem_zeroLocus_iff]
  intro a ha hw
  have : w ∈ g ⁻¹ᵁ Z.basicOpen a := hw
  rw [Scheme.preimage_basicOpen_top] at this
  have h0 : W.basicOpen (g.appTop.hom a) = ⊥ :=
    W.toLocallyRingedSpace.basicOpen_eq_bot_of_isNilpotent ⊤ _ (hg a ha)
  rwa [show W.basicOpen (g.appTop a) = W.basicOpen (g.appTop.hom a) from rfl, h0] at this

section ImageInClosed

variable {X Y : BigFppfOver B S hS} (h : Y ⟶ X) (T : Set (Space.points B S hS (yoneda.obj X)))
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj X, ⊤))
  (hI : Space.pointsToScheme B S hS X '' T =
    ((BigFppfOver.toScheme B S hS).obj X).zeroLocus (U := ⊤)
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)))

include hI in
/-- A morphism `y : V ⟶ Y` along which every element of `I` becomes nilpotent has point-set
image in `|h|⁻¹ T`, where `T` has image `V(I)` in `X`. -/
theorem hasImageIn_of_isNilpotent {V : BigFppfOver B S hS} (y : V ⟶ Y)
    (hy : ∀ a ∈ I, IsNilpotent (((BigFppfOver.toScheme B S hS).map (y ≫ h)).appTop.hom a)) :
    Space.HasImageIn B S hS (yoneda.obj Y)
      (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) V y := by
  rw [hasImageIn_yoneda_preimage_iff, hI]
  exact mem_zeroLocus_of_isNilpotent _ I hy

include hI in
/-- A morphism `y : V ⟶ Y` out of an affine `V` with point-set image in `|h|⁻¹ T` makes the
finitely generated ideal `I` nilpotent on `V`, where `T` has image `V(I)` in `X`. -/
theorem isNilpotent_of_hasImageIn {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (hIfg : I.FG) (y : V ⟶ Y)
    (hy : Space.HasImageIn B S hS (yoneda.obj Y)
      (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) V y) :
    IsNilpotent (I.map ((BigFppfOver.toScheme B S hS).map (y ≫ h)).appTop.hom) := by
  rw [hasImageIn_yoneda_preimage_iff, hI] at hy
  exact isNilpotent_map_appTop_of_range_subset_zeroLocus _ I hIfg hy

end ImageInClosed

/-- Following a ring map `φ : A₀ →+* B₀` by the inverse and then the forward map of
`Γ(Spec B₀) ≅ B₀` gives back `φ`. -/
theorem ofHom_comp_ΓSpecIso_inv_comp_hom {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀]
    (φ : A₀ →+* B₀) {Z : CommRingCat.{u}} (ψ : Z ⟶ CommRingCat.of A₀) :
    ((CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B₀)).inv) ≫
      (Scheme.ΓSpecIso (CommRingCat.of B₀)).hom).hom.comp ψ.hom = φ.comp ψ.hom := by
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-! ### Spectra over an affine object of the site -/

section SpecOver

/-- A morphism of the site out of a scheme with a morphism into the scheme of the target that
lies over `S`. -/
def siteHom {U W : BigFppfOver B S hS}
    (g : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj W)
    (hg : g ≫ W.hom.hom = U.hom.hom) : U ⟶ W :=
  Over.homMk (⟨g⟩ : U.left ⟶ W.left) (InducedCategory.hom_ext hg)

/-- The map on global sections of a composite of morphisms of the site is the composite of
their maps on global sections, in the opposite order. -/
theorem appTop_toScheme_map_comp {U V W : BigFppfOver B S hS} (g : U ⟶ V) (g' : V ⟶ W) :
    ((BigFppfOver.toScheme B S hS).map (g ≫ g')).appTop =
      ((BigFppfOver.toScheme B S hS).map g').appTop ≫
        ((BigFppfOver.toScheme B S hS).map g).appTop := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]

/-- A morphism of the site commutes with the structure morphisms to `S`. -/
theorem toScheme_map_comp_hom {U W : BigFppfOver B S hS} (g : U ⟶ W) :
    (BigFppfOver.toScheme B S hS).map g ≫ W.hom.hom = U.hom.hom :=
  congrArg (fun k ↦ k.hom) (Over.w g)

variable (Y : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]

/-- The spectrum of the global sections of an affine object of the site lies in the site. -/
theorem contains_spec_globalSections :
    B.Contains (Spec Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact
    ((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv) Y.left.property

/-- The spectrum of an algebra `R` over the global sections of an affine object `Y` of the site,
as an object of the site over `Y`. -/
def specAlgOver {R : CommRingCat.{u}} (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R)
    (hR : B.Contains (Spec R)) : BigFppfOver B S hS :=
  BigFppfOver.siteObjectOver B S hS Y hR
    (Spec.map φ ≫ ((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv)

/-- The structure morphism `Spec R ⟶ Y` of `specAlgOver`. -/
def specAlgOverι {R : CommRingCat.{u}} (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R)
    (hR : B.Contains (Spec R)) : specAlgOver B S hS Y φ hR ⟶ Y :=
  BigFppfOver.siteMapOver B S hS Y hR _

/-- The spectrum `specAlgOver φ hR` is affine. -/
instance {R : CommRingCat.{u}} (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R)
    (hR : B.Contains (Spec R)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (specAlgOver B S hS Y φ hR)) :=
  inferInstanceAs (IsAffine (Spec R))

/-- On global sections, the structure morphism `specAlgOverι φ hR : Spec R ⟶ Y` is `φ`
followed by the inverse of `Γ(Spec R) ≅ R`. -/
theorem appTop_specAlgOverι {R : CommRingCat.{u}}
    (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R)
    (hR : B.Contains (Spec R)) :
    ((BigFppfOver.toScheme B S hS).map (specAlgOverι B S hS Y φ hR)).appTop =
      φ ≫ (Scheme.ΓSpecIso R).inv :=
  appTop_SpecMap_comp_isoSpec_inv φ

/-- The kernel of `φ` is contained in the kernel of the map on global sections of
`specAlgOverι φ hR`. -/
theorem ker_le_ker_appTop_specAlgOverι {R : CommRingCat.{u}}
    (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R) (hR : B.Contains (Spec R)) :
    RingHom.ker φ.hom ≤
      RingHom.ker ((BigFppfOver.toScheme B S hS).map (specAlgOverι B S hS Y φ hR)).appTop.hom := by
  intro c hc
  rw [RingHom.mem_ker, appTop_specAlgOverι]
  show (Scheme.ΓSpecIso R).inv.hom (φ.hom c) = 0
  rw [(RingHom.mem_ker).1 hc, map_zero]

/-- A morphism `y : V ⟶ Y` whose map on global sections factors through `φ` lifts to
`specAlgOver φ`. -/
def specAlgOverLift {R : CommRingCat.{u}} (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R)
    (hR : B.Contains (Spec R)) {V : BigFppfOver B S hS} (y : V ⟶ Y)
    (ψ : R ⟶ Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hψ : φ ≫ ψ = ((BigFppfOver.toScheme B S hS).map y).appTop) :
    V ⟶ specAlgOver B S hS Y φ hR :=
  siteHom B S hS (W := specAlgOver B S hS Y φ hR)
    (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ ≫ Spec.map ψ)
    ((Category.assoc (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ ≫ Spec.map ψ)
      (Spec.map φ ≫ ((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv) Y.hom.hom).symm.trans
      ((congrArg (· ≫ Y.hom.hom) (ext_of_isAffine (by
        rw [Scheme.Hom.comp_appTop, appTop_SpecMap_comp_isoSpec_inv, Category.assoc,
          ΓSpecIso_inv_appTop_toSpecΓ_SpecMap, hψ]) :
        (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ ≫ Spec.map ψ) ≫
          (Spec.map φ ≫ ((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv) =
          (BigFppfOver.toScheme B S hS).map y)).trans (toScheme_map_comp_hom B S hS y)))

/-- The lift `specAlgOverLift φ hR y ψ hψ` of `y` followed by `specAlgOverι φ hR` is `y`. -/
theorem specAlgOverLift_comp_specAlgOverι {R : CommRingCat.{u}}
    (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R)
    (hR : B.Contains (Spec R)) {V : BigFppfOver B S hS} (y : V ⟶ Y)
    (ψ : R ⟶ Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hψ : φ ≫ ψ = ((BigFppfOver.toScheme B S hS).map y).appTop) :
    specAlgOverLift B S hS Y φ hR y ψ hψ ≫ specAlgOverι B S hS Y φ hR = y := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  apply ext_of_isAffine
  show ((((BigFppfOver.toScheme B S hS).obj V).toSpecΓ ≫ Spec.map ψ) ≫
    (Spec.map φ ≫ ((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv)).appTop = _
  rw [Scheme.Hom.comp_appTop, appTop_SpecMap_comp_isoSpec_inv, Category.assoc,
    ΓSpecIso_inv_appTop_toSpecΓ_SpecMap, hψ]

/-- On global sections, the lift `specAlgOverLift φ hR y ψ hψ` is `ψ`, read through
`Γ(Spec R) ≅ R`. -/
theorem ΓSpecIso_inv_appTop_specAlgOverLift {R : CommRingCat.{u}}
    (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R)
    (hR : B.Contains (Spec R)) {V : BigFppfOver B S hS} (y : V ⟶ Y)
    (ψ : R ⟶ Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hψ : φ ≫ ψ = ((BigFppfOver.toScheme B S hS).map y).appTop) :
    (Scheme.ΓSpecIso R).inv ≫
      ((BigFppfOver.toScheme B S hS).map (specAlgOverLift B S hS Y φ hR y ψ hψ)).appTop = ψ :=
  ΓSpecIso_inv_appTop_toSpecΓ_SpecMap ψ

/-- Two morphisms into `specAlgOver φ` agree when they induce the same map on global sections. -/
theorem specAlgOver_hom_ext {R : CommRingCat.{u}}
    (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R)
    (hR : B.Contains (Spec R)) {V : BigFppfOver B S hS} {x₁ x₂ : V ⟶ specAlgOver B S hS Y φ hR}
    (h : (Scheme.ΓSpecIso R).inv ≫ ((BigFppfOver.toScheme B S hS).map x₁).appTop =
      (Scheme.ΓSpecIso R).inv ≫ ((BigFppfOver.toScheme B S hS).map x₂).appTop) :
    x₁ = x₂ :=
  (BigFppfOver.toScheme B S hS).map_injective
    (ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso R).inv).1 h))

/-- On global sections, `x ≫ specAlgOverι φ hR` is `φ` followed by the map of `x`, read
through `Γ(Spec R) ≅ R`. -/
theorem appTop_comp_specAlgOverι {R : CommRingCat.{u}}
    (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R)
    (hR : B.Contains (Spec R)) {V : BigFppfOver B S hS} (x : V ⟶ specAlgOver B S hS Y φ hR) :
    φ ≫ (Scheme.ΓSpecIso R).inv ≫ ((BigFppfOver.toScheme B S hS).map x).appTop =
      ((BigFppfOver.toScheme B S hS).map (x ≫ specAlgOverι B S hS Y φ hR)).appTop := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop, appTop_specAlgOverι]
  rfl

/-- The map on global sections of a morphism `g : specAlgOver φ ⟶ Z`, read in `R` through
`Γ(Spec R) ≅ R`. -/
abbrev specAlgOverRingOut {R : CommRingCat.{u}}
    (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R) (hR : B.Contains (Spec R))
    {Z : BigFppfOver B S hS} (g : specAlgOver B S hS Y φ hR ⟶ Z) :
    Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) →+* R :=
  (((BigFppfOver.toScheme B S hS).map g).appTop ≫ (Scheme.ΓSpecIso R).hom).hom

/-- If `g ≫ f = specAlgOverι φ hR ≫ h`, then `specAlgOverRingOut g` precomposed with the map
of `f` on global sections is `φ` precomposed with the map of `h`. -/
theorem specAlgOverRingOut_comp_of_comp_eq {R : CommRingCat.{u}}
    (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R) (hR : B.Contains (Spec R))
    {Z X : BigFppfOver B S hS} (g : specAlgOver B S hS Y φ hR ⟶ Z) (f : Z ⟶ X) (h : Y ⟶ X)
    (hg : g ≫ f = specAlgOverι B S hS Y φ hR ≫ h) :
    (specAlgOverRingOut B S hS Y φ hR g).comp ((BigFppfOver.toScheme B S hS).map f).appTop.hom =
      φ.hom.comp ((BigFppfOver.toScheme B S hS).map h).appTop.hom := by
  have e := congrArg (fun k ↦ ((BigFppfOver.toScheme B S hS).map k).appTop) hg
  simp only [appTop_toScheme_map_comp, appTop_specAlgOverι] at e
  ext a
  have ea := congrArg (fun k ↦ (Scheme.ΓSpecIso R).hom.hom (k.hom a)) e
  exact ea.trans ((Scheme.ΓSpecIso R).inv_hom_id_apply _)

/-- The map on global sections of `specAlgOverLift φ' hR' y ψ hψ ≫ g`, read in `R`, is
`specAlgOverRingOut g`, read in `R'`, followed by `ψ`. -/
theorem specAlgOverRingOut_specAlgOverLift_comp {R R' : CommRingCat.{u}}
    (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R) (hR : B.Contains (Spec R))
    (φ' : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R') (hR' : B.Contains (Spec R'))
    (y : specAlgOver B S hS Y φ hR ⟶ Y)
    (ψ : R' ⟶ Γ((BigFppfOver.toScheme B S hS).obj (specAlgOver B S hS Y φ hR), ⊤))
    (hψ : φ' ≫ ψ = ((BigFppfOver.toScheme B S hS).map y).appTop)
    {Z : BigFppfOver B S hS} (g : specAlgOver B S hS Y φ' hR' ⟶ Z) :
    specAlgOverRingOut B S hS Y φ hR (specAlgOverLift B S hS Y φ' hR' y ψ hψ ≫ g) =
      ((ψ ≫ (Scheme.ΓSpecIso R).hom).hom).comp (specAlgOverRingOut B S hS Y φ' hR' g) := by
  have e := ΓSpecIso_inv_appTop_specAlgOverLift B S hS Y φ' hR' y ψ hψ
  ext a
  show (Scheme.ΓSpecIso R).hom.hom (((BigFppfOver.toScheme B S hS).map
      (specAlgOverLift B S hS Y φ' hR' y ψ hψ)).appTop.hom
      (((BigFppfOver.toScheme B S hS).map g).appTop.hom a)) =
    (Scheme.ΓSpecIso R).hom.hom (ψ.hom ((Scheme.ΓSpecIso R').hom.hom
      (((BigFppfOver.toScheme B S hS).map g).appTop.hom a)))
  congr 1
  set z := ((BigFppfOver.toScheme B S hS).map g).appTop.hom a
  have h1 := congrArg (fun k ↦ k.hom ((Scheme.ΓSpecIso R').hom.hom z)) e
  refine Eq.trans ?_ h1
  show _ = ((BigFppfOver.toScheme B S hS).map (specAlgOverLift B S hS Y φ' hR' y ψ hψ)).appTop.hom
    ((Scheme.ΓSpecIso R').inv.hom ((Scheme.ΓSpecIso R').hom.hom z))
  have h2 : (Scheme.ΓSpecIso R').inv.hom ((Scheme.ΓSpecIso R').hom.hom z) = z :=
    (Scheme.ΓSpecIso R').hom_inv_id_apply z
  exact congrArg _ h2.symm

/-- The map on global sections of `specAlgOverLift φ hR y ψ hψ ≫ g` is
`specAlgOverRingOut g` followed by `ψ`. -/
theorem appTop_specAlgOverLift_comp {R : CommRingCat.{u}}
    (φ : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⟶ R) (hR : B.Contains (Spec R))
    {V : BigFppfOver B S hS} (y : V ⟶ Y) (ψ : R ⟶ Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hψ : φ ≫ ψ = ((BigFppfOver.toScheme B S hS).map y).appTop)
    {Z : BigFppfOver B S hS} (g : specAlgOver B S hS Y φ hR ⟶ Z) :
    ((BigFppfOver.toScheme B S hS).map (specAlgOverLift B S hS Y φ hR y ψ hψ ≫ g)).appTop.hom =
      ψ.hom.comp (specAlgOverRingOut B S hS Y φ hR g) := by
  have e := ΓSpecIso_inv_appTop_specAlgOverLift B S hS Y φ hR y ψ hψ
  ext a
  show ((BigFppfOver.toScheme B S hS).map (specAlgOverLift B S hS Y φ hR y ψ hψ)).appTop.hom
      (((BigFppfOver.toScheme B S hS).map g).appTop.hom a) =
    ψ.hom ((Scheme.ΓSpecIso R).hom.hom (((BigFppfOver.toScheme B S hS).map g).appTop.hom a))
  set z := ((BigFppfOver.toScheme B S hS).map g).appTop.hom a
  have h1 := congrArg (fun k ↦ k.hom ((Scheme.ΓSpecIso R).hom.hom z)) e
  refine Eq.trans ?_ h1
  show _ = ((BigFppfOver.toScheme B S hS).map (specAlgOverLift B S hS Y φ hR y ψ hψ)).appTop.hom
    ((Scheme.ΓSpecIso R).inv.hom ((Scheme.ΓSpecIso R).hom.hom z))
  have h2 : (Scheme.ΓSpecIso R).inv.hom ((Scheme.ΓSpecIso R).hom.hom z) = z :=
    (Scheme.ΓSpecIso R).hom_inv_id_apply z
  exact congrArg _ h2.symm

/-- A ring map `g : Γ(X') → C'` compatible with `f` and `h` on global sections is the map on
global sections of a morphism `a : specAlgOver ⟶ X'` over `X`. -/
theorem exists_hom_specAlgOver_of_algHom {X X' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X')]
    (f : X' ⟶ X) (h : Y ⟶ X) {Cp : Type u} [CommRing Cp]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp] (hY' : B.Contains (Spec (.of Cp)))
    (g : Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) →+* Cp)
    (hg : g.comp ((BigFppfOver.toScheme B S hS).map f).appTop.hom =
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp).comp
        ((BigFppfOver.toScheme B S hS).map h).appTop.hom) :
    ∃ a : specAlgOver B S hS Y (homOf
        (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY' ⟶ X',
      a ≫ f = specAlgOverι B S hS Y _ hY' ≫ h ∧
        ((BigFppfOver.toScheme B S hS).map a).appTop = homOf g ≫
          (Scheme.ΓSpecIso (.of Cp)).inv := by
  let a₀ : Spec (.of Cp) ⟶ (BigFppfOver.toScheme B S hS).obj X' :=
    Spec.map (homOf g) ≫ ((BigFppfOver.toScheme B S hS).obj X').isoSpec.inv
  have ha₀ : a₀.appTop = homOf g ≫ (Scheme.ΓSpecIso (.of Cp)).inv :=
    appTop_SpecMap_comp_isoSpec_inv _
  have hab₀ : a₀ ≫ (BigFppfOver.toScheme B S hS).map f =
      (BigFppfOver.toScheme B S hS).map (specAlgOverι B S hS Y (homOf
        (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY') ≫
        (BigFppfOver.toScheme B S hS).map h := by
    apply ext_of_isAffine
    have e1 : (a₀ ≫ (BigFppfOver.toScheme B S hS).map f).appTop =
        ((BigFppfOver.toScheme B S hS).map f).appTop ≫ a₀.appTop := Scheme.Hom.comp_appTop _ _
    rw [e1, ha₀, Scheme.Hom.comp_appTop, appTop_specAlgOverι, ← Category.assoc]
    refine (congrArg (· ≫ (Scheme.ΓSpecIso (.of Cp)).inv) (CommRingCat.hom_ext hg)).trans ?_
    rfl
  refine ⟨siteHom B S hS (U := specAlgOver B S hS Y _ hY') a₀ ?_, ?_, ha₀⟩
  · rw [← toScheme_map_comp_hom B S hS f]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.hom.hom) hab₀).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (toScheme_map_comp_hom B S hS h)).trans
        (toScheme_map_comp_hom B S hS (specAlgOverι B S hS Y _ hY')))))
  · exact (BigFppfOver.toScheme B S hS).map_injective
      (by rw [Functor.map_comp, Functor.map_comp]; exact hab₀)

/-- The spectrum of an étale algebra over the global sections of an affine object of the site
lies in the site. -/
theorem contains_spec_of_etale {Cp : Type u} [CommRing Cp]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp]
    [Algebra.Etale Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp] :
    B.Contains (Spec (.of Cp)) := by
  have : Etale (Spec.map (homOf
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  exact BigFppfSite.contains_of_locallyOfFinitePresentation B
    (Spec.map (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)))
    (contains_spec_globalSections B S hS Y)

/-- For an étale algebra `C'` over the global sections of `Y`, the structure morphism
`Spec C' ⟶ Y` is étale. -/
theorem etale_specAlgOverι {Cp : Type u} [CommRing Cp]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp]
    [Algebra.Etale Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp]
    (hY' : B.Contains (Spec (.of Cp))) :
    Etale ((BigFppfOver.toScheme B S hS).map (specAlgOverι B S hS Y
      (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY')) := by
  have : Etale (Spec.map (homOf
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  show Etale (Spec.map _ ≫ ((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv)
  infer_instance

end SpecOver

section Stages

variable {X Y : BigFppfOver B S hS} (h : Y ⟶ X) (T : Set (Space.points B S hS (yoneda.obj X)))
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj X, ⊤))
  (hI : Space.pointsToScheme B S hS X '' T =
    ((BigFppfOver.toScheme B S hS).obj X).zeroLocus (U := ⊤)
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)))

/-- If the `n`-th power of the ideal generated by `I` on `Y` lies in the kernel of the map of
`z` on global sections, then every element of `I` becomes nilpotent along `z ≫ h`. -/
theorem isNilpotent_appTop_comp_of_le_ker {V : BigFppfOver B S hS} (z : V ⟶ Y) (n : ℕ)
    (hz : (I.map ((BigFppfOver.toScheme B S hS).map h).appTop.hom) ^ n ≤
      RingHom.ker ((BigFppfOver.toScheme B S hS).map z).appTop.hom) :
    ∀ a ∈ I, IsNilpotent (((BigFppfOver.toScheme B S hS).map (z ≫ h)).appTop.hom a) := by
  intro a ha
  refine ⟨n, ?_⟩
  rw [appTop_toScheme_map_comp, CommRingCat.hom_comp, RingHom.comp_apply, ← map_pow]
  exact hz (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ ha) n)

include hI in
/-- The `n`-th infinitesimal neighbourhood `Spec(C ⧸ (IC)ⁿ)` of the closed fibre of an affine
`Y` over `X` has point-set image over `T`. -/
theorem hasImageIn_specAlgOverι_quotient [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)] (n : ℕ)
    (hR : B.Contains (Spec (.of (Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⧸
      (I.map ((BigFppfOver.toScheme B S hS).map h).appTop.hom) ^ n)))) :
    Space.HasImageIn B S hS (yoneda.obj Y)
      (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) _
      (specAlgOverι B S hS Y (homOf (Ideal.Quotient.mk
        ((I.map ((BigFppfOver.toScheme B S hS).map h).appTop.hom) ^ n))) hR) := by
  refine hasImageIn_of_isNilpotent B S hS h T I hI _
    (isNilpotent_appTop_comp_of_le_ker B S hS h I _ n ?_)
  refine le_trans ?_ (ker_le_ker_appTop_specAlgOverι B S hS Y _ hR)
  rw [CommRingCat.hom_ofHom, Ideal.mk_ker]


end Stages

/-! ### Morphisms into an étale neighbourhood of a closed fibre -/

section EtaleNeighbourhood

variable (Y : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
  {Cp : Type u} [CommRing Cp] [Algebra Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp]
  [Algebra.Etale Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp]
  (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤))
  (hbij : Function.Bijective
    (Ideal.quotientMap (J.map (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp))
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp) Ideal.le_comap_map))
  (hY' : B.Contains (Spec (.of Cp)))

/-- The ring map `C' → Γ(V)` of a morphism `V ⟶ Spec C'`. -/
abbrev specAlgOverRingHom {V : BigFppfOver B S hS}
    (x : V ⟶ specAlgOver B S hS Y
      (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY') :
    Cp →+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  ((Scheme.ΓSpecIso (.of Cp)).inv ≫ ((BigFppfOver.toScheme B S hS).map x).appTop).hom

omit [Algebra.Etale Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp] in
/-- The ring map `C' → Γ(V)` of `x : V ⟶ Spec C'`, restricted to the global sections of `Y`,
is the map on global sections of `x ≫ specAlgOverι`. -/
theorem specAlgOverRingHom_comp_algebraMap {V : BigFppfOver B S hS}
    (x : V ⟶ specAlgOver B S hS Y
      (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY') :
    (specAlgOverRingHom B S hS Y hY' x).comp
        (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp) =
      ((BigFppfOver.toScheme B S hS).map
        (x ≫ specAlgOverι B S hS Y
          (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY')).appTop.hom := by
  rw [← appTop_comp_specAlgOverι]
  rfl

include hbij in
/-- On a `V` in which `J` generates a nilpotent ideal of global functions, the `C`-algebra map
`C' → Γ(V)` of a morphism `V ⟶ Spec C'` is the only one. -/
theorem specAlgOverRingHom_eq {V : BigFppfOver B S hS}
    (x : V ⟶ specAlgOver B S hS Y
      (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY')
    (hnil : IsNilpotent (J.map ((BigFppfOver.toScheme B S hS).map
      (x ≫ specAlgOverι B S hS Y
        (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY')).appTop.hom))
    (θ : Cp →+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hθ : θ.comp (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp) =
      ((BigFppfOver.toScheme B S hS).map (x ≫ specAlgOverι B S hS Y
        (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY')).appTop.hom) :
    specAlgOverRingHom B S hS Y hY' x = θ := by
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map (x ≫ specAlgOverι B S hS Y
      (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY')).appTop.hom.toAlgebra
  obtain ⟨-, huniq⟩ := existsUnique_algHom_of_etale_of_bijective_quotientMap J hbij hnil
  have := huniq ⟨specAlgOverRingHom B S hS Y hY' x, fun c ↦
      RingHom.congr_fun (specAlgOverRingHom_comp_algebraMap B S hS Y hY' x) c⟩
    ⟨θ, fun c ↦ RingHom.congr_fun hθ c⟩
  exact congrArg AlgHom.toRingHom this

include hbij in
/-- A morphism `y : V ⟶ Y` along which `J` becomes nilpotent lifts to `Spec C'`. -/
theorem exists_lift_specAlgOver {V : BigFppfOver B S hS} (y : V ⟶ Y)
    (hnil : IsNilpotent (J.map ((BigFppfOver.toScheme B S hS).map y).appTop.hom)) :
    ∃ x : V ⟶ specAlgOver B S hS Y
        (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY',
      x ≫ specAlgOverι B S hS Y
        (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY' = y := by
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map y).appTop.hom.toAlgebra
  obtain ⟨⟨g⟩, -⟩ := existsUnique_algHom_of_etale_of_bijective_quotientMap J hbij hnil
  refine ⟨specAlgOverLift B S hS Y _ hY' y (homTo g.toRingHom) ?_, ?_⟩
  · ext c
    exact g.commutes c
  · exact specAlgOverLift_comp_specAlgOverι B S hS Y _ hY' y _ _

include hbij in
/-- Lifts of `y : V ⟶ Y` to `Spec C'` are unique when `J` becomes nilpotent along `y`. -/
theorem lift_specAlgOver_unique {V : BigFppfOver B S hS} (y : V ⟶ Y)
    (hnil : IsNilpotent (J.map ((BigFppfOver.toScheme B S hS).map y).appTop.hom))
    {x₁ x₂ : V ⟶ specAlgOver B S hS Y
      (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY'}
    (h₁ : x₁ ≫ specAlgOverι B S hS Y
      (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY' = y)
    (h₂ : x₂ ≫ specAlgOverι B S hS Y
      (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY' = y) :
    x₁ = x₂ := by
  apply specAlgOver_hom_ext
  have e := specAlgOverRingHom_eq B S hS Y J hbij hY' x₁ (h₁ ▸ hnil)
    (specAlgOverRingHom B S hS Y hY' x₂) (by rw [specAlgOverRingHom_comp_algebraMap, h₁, h₂])
  exact CommRingCat.hom_ext e

end EtaleNeighbourhood

/-! ### Reading sections of completions -/

/-- The universe lift of a representable presheaf on the big fppf site is an fppf sheaf. -/
theorem isSheaf_yoneda_comp_uliftFunctor (Z : BigFppfOver B S hS) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj Z ⋙ uliftFunctor.{u + 1}) := by
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type]
  exact BigFppfOver.isSheaf_yoneda_obj B S hS Z

section Read

variable {G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (G ⋙ uliftFunctor.{u + 1}))
  (hG' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (G' ⋙ uliftFunctor.{u + 1}))

/-- A section of the sheafified universe lift of a presheaf `G` whose universe lift is already a
sheaf, read as a section of `G`. -/
def ambientRead {U : BigFppfOver B S hS}
    (z : (Space.sheafifiedULift B S hS G).obj.obj (op U)) : G.obj (op U) :=
  (((BigFppfOver.topology B S hS).isoSheafify hG).inv.app (op U) z).down

/-- Reading the image of a section `g` of `G` in the sheafified universe lift gives back `g`. -/
theorem ambientRead_toSheafify {U : BigFppfOver B S hS} (g : G.obj (op U)) :
    ambientRead B S hS hG (((BigFppfOver.topology B S hS).toSheafify
      (G ⋙ uliftFunctor.{u + 1})).app (op U) (ULift.up g)) = g :=
  congrArg (fun φ ↦ (φ.app (op U) (ULift.up g)).down)
    ((BigFppfOver.topology B S hS).isoSheafify hG).hom_inv_id

/-- Reading sections of the sheafified universe lift of `G` as sections of `G` is injective. -/
theorem ambientRead_injective {U : BigFppfOver B S hS} :
    Function.Injective (ambientRead B S hS hG (U := U)) := by
  intro z₁ z₂ hz
  let e := (BigFppfOver.topology B S hS).isoSheafify hG
  have h₁ : e.hom.app (op U) (e.inv.app (op U) z₁) = z₁ :=
    congrArg (fun φ ↦ φ.app (op U) z₁) e.inv_hom_id
  have h₂ : e.hom.app (op U) (e.inv.app (op U) z₂) = z₂ :=
    congrArg (fun φ ↦ φ.app (op U) z₂) e.inv_hom_id
  rw [← h₁, ← h₂]
  congr 1
  exact ULift.ext hz

/-- Reading sections of the sheafified universe lift of `G` commutes with restriction. -/
theorem ambientRead_map {U V : BigFppfOver B S hS} (φ : V ⟶ U)
    (z : (Space.sheafifiedULift B S hS G).obj.obj (op U)) :
    ambientRead B S hS hG ((Space.sheafifiedULift B S hS G).obj.map φ.op z) =
      G.map φ.op (ambientRead B S hS hG z) :=
  congrArg ULift.down (NatTrans.naturality_apply
    ((BigFppfOver.topology B S hS).isoSheafify hG).inv φ.op z)

/-- Reading sections of the sheafified universe lift is natural in morphisms of presheaves. -/
theorem ambientRead_sheafifiedULiftMap (a : G ⟶ G') {U : BigFppfOver B S hS}
    (z : (Space.sheafifiedULift B S hS G).obj.obj (op U)) :
    ambientRead B S hS hG' ((Space.sheafifiedULiftMap B S hS a).hom.app (op U) z) =
      a.app (op U) (ambientRead B S hS hG z) := by
  let e := (BigFppfOver.topology B S hS).isoSheafify hG
  obtain ⟨w, rfl⟩ : ∃ w, e.hom.app (op U) w = z :=
    ⟨e.inv.app (op U) z, congrArg (fun φ ↦ φ.app (op U) z) e.inv_hom_id⟩
  obtain ⟨g⟩ := w
  show ambientRead B S hS hG' (((BigFppfOver.topology B S hS).toSheafify
      (G ⋙ uliftFunctor.{u + 1}) ≫
    (BigFppfOver.topology B S hS).sheafifyMap
      (Functor.whiskerRight a uliftFunctor.{u + 1})).app (op U) (ULift.up g)) =
    a.app (op U) (ambientRead B S hS hG (((BigFppfOver.topology B S hS).toSheafify
      (G ⋙ uliftFunctor.{u + 1})).app (op U) (ULift.up g)))
  rw [← GrothendieckTopology.toSheafify_naturality, ambientRead_toSheafify]
  exact ambientRead_toSheafify B S hS hG' (a.app (op U) g)

end Read

/-- A section has point-set image in the inverse image of `T` under a morphism of presheaves
exactly when its image has point-set image in `T`. -/
theorem hasImageIn_preimage_pointsMap_iff {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : F ⟶ G)
    (T : Set (Space.points B S hS G)) (U : BigFppfOver B S hS) (x : F.obj (op U)) :
    Space.HasImageIn B S hS F (Space.pointsMap B S hS F φ ⁻¹' T) U x ↔
      Space.HasImageIn B S hS G T U (φ.app (op U) x) := by
  refine forall_congr' fun p ↦ ?_
  show Space.pointsMap B S hS F φ _ ∈ T ↔ _
  rw [Space.pointsMap_class]
  show (⟨p.carrier, p.contained, p.toBase, φ.app _ (F.map p.value.op x)⟩ :
    Space.FieldValuedPoint B S hS G).class B S hS G ∈ T ↔ _
  rw [NatTrans.naturality_apply φ p.value.op x]

/-- A section over `T` of an object `M` over `X` stays over `T` after a morphism over `X`. -/
theorem hasImageIn_over_left_app {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) {M N : Over X} (g : M ⟶ N) {U : BigFppfOver B S hS}
    (x : M.left.obj (op U))
    (hx : Space.HasImageIn B S hS M.left (Space.pointsMap B S hS M.left M.hom ⁻¹' T) U x) :
    Space.HasImageIn B S hS N.left (Space.pointsMap B S hS N.left N.hom ⁻¹' T) U
      (g.left.app (op U) x) :=
  (hasImageIn_preimage_pointsMap_iff B S hS g.left _ U x).1
    (Space.preimage_pointsMap_over B S hS T g ▸ hx)

section PresheafSections

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The section of the completion of a presheaf `F` along `T` given by a section of `F` with
point-set image in `T`. -/
def presheafSection {T : Set (Space.points B S hS F)} {U : BigFppfOver B S hS} (x : F.obj (op U))
    (hx : Space.HasImageIn B S hS F T U x) :
    (Space.completionSheaf B S hS F T).obj.obj (op U) :=
  ((BigFppfOver.topology B S hS).toSheafify
    (Space.completionSubfunctor B S hS F T).toFunctor).app (op U) ⟨ULift.up x, hx⟩

/-- The completion of a morphism `φ : F ⟶ G` sends the section given by `x` to the section
given by `φ x`. -/
theorem completionSheafMap_presheafSection (φ : F ⟶ G) (T : Set (Space.points B S hS G))
    {U : BigFppfOver B S hS} (x : F.obj (op U))
    (hx : Space.HasImageIn B S hS F (Space.pointsMap B S hS F φ ⁻¹' T) U x)
    (hx' : Space.HasImageIn B S hS G T U (φ.app (op U) x)) :
    (Space.completionSheafMap B S hS φ T).hom.app (op U) (presheafSection B S hS x hx) =
      presheafSection B S hS (φ.app (op U) x) hx' :=
  (NatTrans.congr_app ((BigFppfOver.topology B S hS).toSheafify_naturality
    (Space.completionMap B S hS φ T)) (op U) ▸ rfl :
      ((BigFppfOver.topology B S hS).toSheafify _ ≫
        (BigFppfOver.topology B S hS).sheafifyMap
          (Space.completionMap B S hS φ T)).app (op U) ⟨ULift.up x, hx⟩ = _)

/-- The inclusion of the completion of `F` into the sheafified universe lift of `F` sends the
section given by `x` to the image of `x`. -/
theorem inclusion_presheafSection {T : Set (Space.points B S hS F)} {U : BigFppfOver B S hS}
    (x : F.obj (op U)) (hx : Space.HasImageIn B S hS F T U x) :
    (Space.completionSheafInclusion B S hS F T).hom.app (op U) (presheafSection B S hS x hx) =
      ((BigFppfOver.topology B S hS).toSheafify (F ⋙ uliftFunctor.{u + 1})).app (op U)
        (ULift.up x) :=
  (NatTrans.congr_app ((BigFppfOver.topology B S hS).toSheafify_naturality
    (Space.completionSubfunctor B S hS F T).ι) (op U) ▸ rfl :
      ((BigFppfOver.topology B S hS).toSheafify _ ≫
        (BigFppfOver.topology B S hS).sheafifyMap
          (Space.completionSubfunctor B S hS F T).ι).app (op U) ⟨ULift.up x, hx⟩ = _)

/-- The sheafified universe lift of a morphism `φ : F ⟶ G` sends the image of a section `x`
of `F` to the image of `φ x`. -/
theorem sheafifiedULiftMap_toSheafify (φ : F ⟶ G) {U : BigFppfOver B S hS} (x : F.obj (op U)) :
    (Space.sheafifiedULiftMap B S hS φ).hom.app (op U)
      (((BigFppfOver.topology B S hS).toSheafify (F ⋙ uliftFunctor.{u + 1})).app (op U)
        (ULift.up x)) =
      ((BigFppfOver.topology B S hS).toSheafify (G ⋙ uliftFunctor.{u + 1})).app (op U)
        (ULift.up (φ.app (op U) x)) :=
  (NatTrans.congr_app ((BigFppfOver.topology B S hS).toSheafify_naturality
    (Functor.whiskerRight φ uliftFunctor.{u + 1})) (op U) ▸ rfl :
      ((BigFppfOver.topology B S hS).toSheafify _ ≫
        (BigFppfOver.topology B S hS).sheafifyMap
          (Functor.whiskerRight φ uliftFunctor.{u + 1})).app (op U) (ULift.up x) = _)

/-- The inclusion of the completion of `F` into the sheafified universe lift of `F` is injective
on sections. -/
theorem injective_completionSheafInclusion_app (T : Set (Space.points B S hS F))
    (U : BigFppfOver B S hS) :
    Function.Injective ((Space.completionSheafInclusion B S hS F T).hom.app (op U)) := by
  have := Space.mono_completionSheafInclusion B S hS F T
  have hm : Mono (Space.completionSheafInclusion B S hS F T).hom :=
    inferInstanceAs (Mono ((sheafToPresheaf _ _).map (Space.completionSheafInclusion B S hS F T)))
  rw [← CategoryTheory.mono_iff_injective]
  infer_instance

/-- The completion of a morphism over `X` sends the section given by `x` to the section given by
the image of `x`. -/
theorem completionOverMap_presheafSection {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) {M N : Over X} (g : M ⟶ N) {U : BigFppfOver B S hS}
    (x : M.left.obj (op U))
    (hx : Space.HasImageIn B S hS M.left (Space.pointsMap B S hS M.left M.hom ⁻¹' T) U x)
    (hx' : Space.HasImageIn B S hS N.left (Space.pointsMap B S hS N.left N.hom ⁻¹' T) U
      (g.left.app (op U) x)) :
    (Space.completionOverMap B S hS T g).hom.app (op U) (presheafSection B S hS x hx) =
      presheafSection B S hS (g.left.app (op U) x) hx' := by
  apply injective_completionSheafInclusion_app B S hS _ U
  have h := congrArg (fun Φ ↦ Φ.hom.app (op U) (presheafSection B S hS x hx))
    (Space.completionOverMap_comp_inclusion B S hS T g)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply] at h
  rw [h, inclusion_presheafSection, inclusion_presheafSection, sheafifiedULiftMap_toSheafify]

end PresheafSections

section Evaluation

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {TF : Set (Space.points B S hS F)}
  {TG : Set (Space.points B S hS G)}
  (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (G ⋙ uliftFunctor.{u + 1}))

/-- The section of the completion given by `x` restricts to the section given by the
restriction of `x`. -/
theorem presheafSection_map {U V : BigFppfOver B S hS} (φ : V ⟶ U) (x : F.obj (op U))
    (hx : Space.HasImageIn B S hS F TF U x)
    (hx' : Space.HasImageIn B S hS F TF V (F.map φ.op x)) :
    (Space.completionSheaf B S hS F TF).obj.map φ.op (presheafSection B S hS x hx) =
      presheafSection B S hS (F.map φ.op x) hx' :=
  (NatTrans.naturality_apply ((BigFppfOver.topology B S hS).toSheafify
    (Space.completionSubfunctor B S hS F TF).toFunctor) φ.op ⟨ULift.up x, hx⟩).symm

/-- A morphism of completions, evaluated on the section given by a section `x` of `F` with
point-set image in `TF`, and read as a section of `G`. -/
def completionEval (Φ : Space.completionSheaf B S hS F TF ⟶ Space.completionSheaf B S hS G TG)
    {U : BigFppfOver B S hS} (x : F.obj (op U)) (hx : Space.HasImageIn B S hS F TF U x) :
    G.obj (op U) :=
  ambientRead B S hS hG ((Space.completionSheafInclusion B S hS G TG).hom.app (op U)
    (Φ.hom.app (op U) (presheafSection B S hS x hx)))

/-- Evaluating a morphism of completions commutes with restriction. -/
theorem completionEval_map
    (Φ : Space.completionSheaf B S hS F TF ⟶ Space.completionSheaf B S hS G TG)
    {U V : BigFppfOver B S hS} (φ : V ⟶ U) (x : F.obj (op U))
    (hx : Space.HasImageIn B S hS F TF U x)
    (hx' : Space.HasImageIn B S hS F TF V (F.map φ.op x)) :
    completionEval B S hS hG Φ (F.map φ.op x) hx' =
      G.map φ.op (completionEval B S hS hG Φ x hx) := by
  unfold completionEval
  rw [← presheafSection_map B S hS φ x hx hx', NatTrans.naturality_apply Φ.hom,
    NatTrans.naturality_apply (Space.completionSheafInclusion B S hS G TG).hom]
  exact ambientRead_map B S hS hG φ _

/-- Two morphisms of completions into the completion of a presheaf whose universe lift is a sheaf
agree as soon as they agree on the sections over affine objects of the site. -/
theorem completionSheaf_hom_ext
    {Φ₁ Φ₂ : Space.completionSheaf B S hS F TF ⟶ Space.completionSheaf B S hS G TG}
    (H : ∀ (V : BigAffineFppf B S hS) (x : F.obj (op ((BigAffineFppf.inclusion B S hS).obj V)))
      (hx : Space.HasImageIn B S hS F TF _ x),
      completionEval B S hS hG Φ₁ x hx = completionEval B S hS hG Φ₂ x hx) :
    Φ₁ = Φ₂ := by
  have := Space.mono_completionSheafInclusion B S hS G TG
  rw [← cancel_mono (Space.completionSheafInclusion B S hS G TG)]
  apply Sheaf.hom_ext
  apply (BigFppfOver.topology B S hS).sheafify_hom_ext _ _
    (Space.sheafifiedULift B S hS G).property
  ext U x
  obtain ⟨⟨x⟩, hx⟩ := x
  have : (BigAffineFppf.inclusion B S hS).IsCoverDense (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  refine Functor.IsCoverDense.ext (BigAffineFppf.inclusion B S hS)
    (Space.sheafifiedULift B S hS G) U.unop fun V φ ↦ ?_
  apply ambientRead_injective B S hS hG
  have hx' : Space.HasImageIn B S hS F TF _ (F.map φ.op x) :=
    ((Space.completionSubfunctor B S hS F TF).map φ.op hx :)
  have key : ∀ Φ : Space.completionSheaf B S hS F TF ⟶ Space.completionSheaf B S hS G TG,
      ambientRead B S hS hG ((Space.sheafifiedULift B S hS G).obj.map φ.op
        ((Space.completionSheafInclusion B S hS G TG).hom.app U
          (Φ.hom.app U (presheafSection B S hS x hx)))) =
        completionEval B S hS hG Φ (F.map φ.op x) hx' := by
    intro Φ
    rw [ambientRead_map, completionEval_map B S hS hG Φ φ x hx hx']
    rfl
  show ambientRead B S hS hG ((Space.sheafifiedULift B S hS G).obj.map φ.op
        ((Space.completionSheafInclusion B S hS G TG).hom.app U
          (Φ₁.hom.app U (presheafSection B S hS x hx)))) =
    ambientRead B S hS hG ((Space.sheafifiedULift B S hS G).obj.map φ.op
        ((Space.completionSheafInclusion B S hS G TG).hom.app U
          (Φ₂.hom.app U (presheafSection B S hS x hx))))
  rw [key Φ₁, key Φ₂]
  exact H V (F.map φ.op x) hx'

/-- The completion of a morphism `g : M ⟶ N` over `X`, evaluated on a section `x` of `M`, is
`g x`. -/
theorem completionEval_completionOverMap {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) {M N : Over X} (g : M ⟶ N)
    (hN : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (N.left ⋙ uliftFunctor.{u + 1}))
    {U : BigFppfOver B S hS} (x : M.left.obj (op U))
    (hx : Space.HasImageIn B S hS M.left (Space.pointsMap B S hS M.left M.hom ⁻¹' T) U x) :
    completionEval B S hS hN (Space.completionOverMap B S hS T g) x hx = g.left.app (op U) x := by
  have hx' : Space.HasImageIn B S hS N.left (Space.pointsMap B S hS N.left N.hom ⁻¹' T) U
      (g.left.app (op U) x) := by
    have e := Space.preimage_pointsMap_over B S hS T g
    exact (hasImageIn_preimage_pointsMap_iff B S hS g.left _ U x).1 (e ▸ hx)
  unfold completionEval
  rw [completionOverMap_presheafSection B S hS T g x hx hx', inclusion_presheafSection]
  exact ambientRead_toSheafify B S hS hN _

/-- Evaluating the composite of the completion of `g : M ⟶ N` and `Φ` on a section `x` of `M`
is evaluating `Φ` on `g x`. -/
theorem completionEval_completionOverMap_comp {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) {M N : Over X} (g : M ⟶ N)
    (Φ : Space.completionSheaf B S hS N.left (Space.pointsMap B S hS N.left N.hom ⁻¹' T) ⟶
      Space.completionSheaf B S hS G TG)
    {U : BigFppfOver B S hS} (x : M.left.obj (op U))
    (hx : Space.HasImageIn B S hS M.left (Space.pointsMap B S hS M.left M.hom ⁻¹' T) U x)
    (hx' : Space.HasImageIn B S hS N.left (Space.pointsMap B S hS N.left N.hom ⁻¹' T) U
      (g.left.app (op U) x)) :
    completionEval B S hS hG (Space.completionOverMap B S hS T g ≫ Φ) x hx =
      completionEval B S hS hG Φ (g.left.app (op U) x) hx' := by
  unfold completionEval
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply]
  rw [completionOverMap_presheafSection B S hS T g x hx hx']

/-- A morphism `α : M_{/T} ⟶ N_{/T}` over `X_{/T}` sends a section of `M` to a section of `N`
with the same image in `X`. -/
theorem hom_app_completionEval {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) {M N : Over X}
    (α : (Space.completionOverFunctor B S hS T).obj M ⟶
      (Space.completionOverFunctor B S hS T).obj N)
    (hN : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (N.left ⋙ uliftFunctor.{u + 1}))
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    {U : BigFppfOver B S hS} (x : M.left.obj (op U))
    (hx : Space.HasImageIn B S hS M.left (Space.pointsMap B S hS M.left M.hom ⁻¹' T) U x) :
    N.hom.app (op U) (completionEval B S hS hN α.left x hx) = M.hom.app (op U) x := by
  let αL : Space.completionSheaf B S hS M.left (Space.pointsMap B S hS M.left M.hom ⁻¹' T) ⟶
      Space.completionSheaf B S hS N.left (Space.pointsMap B S hS N.left N.hom ⁻¹' T) := α.left
  have hw : αL ≫ Space.completionSheafMap B S hS N.hom T =
      Space.completionSheafMap B S hS M.hom T := Over.w α
  have hsq := (Space.isPullback_completionSheafMap B S hS N.hom T).w
  have h1 : ∀ z, (Space.sheafifiedULiftMap B S hS N.hom).hom.app (op U)
      ((Space.completionSheafInclusion B S hS N.left
        (Space.pointsMap B S hS N.left N.hom ⁻¹' T)).hom.app (op U) z) =
      (Space.completionSheafInclusion B S hS X T).hom.app (op U)
        ((Space.completionSheafMap B S hS N.hom T).hom.app (op U) z) :=
    fun z ↦ congrArg (fun Φ ↦ Φ.hom.app (op U) z) hsq
  have h2 : (Space.completionSheafMap B S hS N.hom T).hom.app (op U)
      (αL.hom.app (op U) (presheafSection B S hS x hx)) =
      (Space.completionSheafMap B S hS M.hom T).hom.app (op U) (presheafSection B S hS x hx) :=
    congrArg (fun Φ ↦ Φ.hom.app (op U) (presheafSection B S hS x hx)) hw
  show N.hom.app (op U) (ambientRead B S hS hN
    ((Space.completionSheafInclusion B S hS N.left
        (Space.pointsMap B S hS N.left N.hom ⁻¹' T)).hom.app (op U)
      (αL.hom.app (op U) (presheafSection B S hS x hx)))) = M.hom.app (op U) x
  rw [← ambientRead_sheafifiedULiftMap B S hS hN hX, h1, h2,
    completionSheafMap_presheafSection B S hS M.hom T x hx
      ((hasImageIn_preimage_pointsMap_iff B S hS M.hom T U x).1 hx), inclusion_presheafSection]
  exact ambientRead_toSheafify B S hS hX _

/-- Evaluating a morphism of completions on equal sections gives equal values. -/
theorem completionEval_congr
    (Φ : Space.completionSheaf B S hS F TF ⟶ Space.completionSheaf B S hS G TG)
    {U : BigFppfOver B S hS} {x x' : F.obj (op U)} (e : x = x')
    (hx : Space.HasImageIn B S hS F TF U x) (hx' : Space.HasImageIn B S hS F TF U x') :
    completionEval B S hS hG Φ x hx = completionEval B S hS hG Φ x' hx' := by
  subst e
  rfl

end Evaluation

/-! ### Isomorphisms of completions -/

/-- The completion of a morphism of presheaves is an isomorphism as soon as the induced morphism
of completion subfunctors is locally injective and locally surjective. -/
theorem isIso_completionSheafMap_of_isLocallyBijective {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (φ : F ⟶ G) (T : Set (Space.points B S hS G))
    [Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) (Space.completionMap B S hS φ T)]
    [Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Space.completionMap B S hS φ T)] :
    IsIso (Space.completionSheafMap B S hS φ T) := by
  let K := BigFppfOver.topology B S hS
  have hfac : K.toSheafify _ ≫ K.sheafifyMap (Space.completionMap B S hS φ T) =
      Space.completionMap B S hS φ T ≫ K.toSheafify _ :=
    (K.toSheafify_naturality _).symm
  have : Presheaf.IsLocallyInjective K
      (K.toSheafify _ ≫ K.sheafifyMap (Space.completionMap B S hS φ T)) := by
    rw [hfac]; infer_instance
  have : Presheaf.IsLocallySurjective K
      (K.toSheafify _ ≫ K.sheafifyMap (Space.completionMap B S hS φ T)) := by
    rw [hfac]; infer_instance
  have h₁ : Presheaf.IsLocallyInjective K (K.sheafifyMap (Space.completionMap B S hS φ T)) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective K
      (K.toSheafify _) _
  have h₂ : Presheaf.IsLocallySurjective K (K.sheafifyMap (Space.completionMap B S hS φ T)) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective K (K.toSheafify _) _
  exact (Sheaf.isLocallyBijective_iff_isIso (Space.completionSheafMap B S hS φ T)).1 ⟨h₁, h₂⟩

section EtaleNeighbourhoodCompletion

variable {X Y : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)] (h : Y ⟶ X)
  (T : Set (Space.points B S hS (yoneda.obj X)))
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)) (hIfg : I.FG)
  (hI : Space.pointsToScheme B S hS X '' T =
    ((BigFppfOver.toScheme B S hS).obj X).zeroLocus (U := ⊤)
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)))
  {Cp : Type u} [CommRing Cp] [Algebra Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp]
  [Algebra.Etale Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp]
  (hbij : Function.Bijective
    (Ideal.quotientMap ((I.map ((BigFppfOver.toScheme B S hS).map h).appTop.hom).map
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp))
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp) Ideal.le_comap_map))
  (hY' : B.Contains (Spec (.of Cp)))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)] in
/-- Extending `I` to `Y` along `h` and then to `V` along `z` is extending it along `z ≫ h`. -/
theorem map_map_appTop {V : BigFppfOver B S hS} (z : V ⟶ Y) :
    (I.map ((BigFppfOver.toScheme B S hS).map h).appTop.hom).map
        ((BigFppfOver.toScheme B S hS).map z).appTop.hom =
      I.map ((BigFppfOver.toScheme B S hS).map (z ≫ h)).appTop.hom := by
  rw [Ideal.map_map, Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)] in
include hIfg hI in
/-- A morphism `z : V ⟶ Y` out of an affine `V` with point-set image in `|h|⁻¹ T` makes the
ideal generated by `I` on `Y` nilpotent on `V`. -/
theorem isNilpotent_map_of_hasImageIn {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (z : V ⟶ Y)
    (hz : Space.HasImageIn B S hS (yoneda.obj Y)
      (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) V z) :
    IsNilpotent ((I.map ((BigFppfOver.toScheme B S hS).map h).appTop.hom).map
        ((BigFppfOver.toScheme B S hS).map z).appTop.hom) := by
  rw [map_map_appTop]
  exact isNilpotent_of_hasImageIn B S hS h T I hI hIfg z hz

include hIfg hI hbij in
/-- The morphism of completion subfunctors induced by an étale neighbourhood `Spec C' ⟶ Y`
of the closed fibre over `T` is locally injective. -/
theorem isLocallyInjective_completionMap_specAlgOverι :
    Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (Space.completionMap B S hS (yoneda.map (specAlgOverι B S hS Y
        (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY'))
        (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T)) where
  equalizerSieve_mem {U} x₁ x₂ hx := by
    have : (BigAffineFppf.inclusion B S hS).IsCoverDense (BigFppfOver.topology B S hS) :=
      Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
        (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
    obtain ⟨⟨x₁⟩, hx₁⟩ := x₁
    obtain ⟨⟨x₂⟩, hx₂⟩ := x₂
    set b := specAlgOverι B S hS Y
      (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY'
    have he : x₁ ≫ b = x₂ ≫ b := congrArg (fun z ↦ z.1.down) hx
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      ((BigAffineFppf.inclusion B S hS).is_cover_of_isCoverDense
        (BigFppfOver.topology B S hS) U.unop)
    rintro W f ⟨V, f₁, f₂, rfl⟩
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj V)) :=
      V.property
    apply Subtype.ext
    apply ULift.ext
    show (f₁ ≫ f₂) ≫ x₁ = (f₁ ≫ f₂) ≫ x₂
    rw [Category.assoc, Category.assoc]
    congr 1
    have hz : Space.HasImageIn B S hS (yoneda.obj Y)
        (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) _ (f₂ ≫ x₁ ≫ b) :=
      ((Space.completionSubfunctor B S hS (yoneda.obj Y) _).map f₂.op
        ((hasImageIn_preimage_pointsMap_iff B S hS (yoneda.map b) _ _ x₁).1 hx₁) :)
    exact lift_specAlgOver_unique B S hS Y _ hbij hY' (f₂ ≫ x₁ ≫ b)
      (isNilpotent_map_of_hasImageIn B S hS h T I hIfg hI _ hz)
      (Category.assoc _ _ _) (by rw [Category.assoc, he])

include hIfg hI hbij in
/-- The morphism of completion subfunctors induced by an étale neighbourhood `Spec C' ⟶ Y`
of the closed fibre over `T` is locally surjective. -/
theorem isLocallySurjective_completionMap_specAlgOverι :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Space.completionMap B S hS (yoneda.map (specAlgOverι B S hS Y
        (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY'))
        (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T)) where
  imageSieve_mem {U} y := by
    have : (BigAffineFppf.inclusion B S hS).IsCoverDense (BigFppfOver.topology B S hS) :=
      Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
        (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
    obtain ⟨⟨y⟩, hy⟩ := y
    set b := specAlgOverι B S hS Y
      (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY'
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      ((BigAffineFppf.inclusion B S hS).is_cover_of_isCoverDense
        (BigFppfOver.topology B S hS) U)
    rintro W f ⟨V, f₁, f₂, rfl⟩
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj V)) :=
      V.property
    apply Sieve.downward_closed
    have hz : Space.HasImageIn B S hS (yoneda.obj Y)
        (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) _ (f₂ ≫ y) :=
      ((Space.completionSubfunctor B S hS (yoneda.obj Y) _).map f₂.op hy :)
    obtain ⟨x, hx⟩ := exists_lift_specAlgOver B S hS Y _ hbij hY' (f₂ ≫ y)
      (isNilpotent_map_of_hasImageIn B S hS h T I hIfg hI _ hz)
    have hx' : Space.HasImageIn B S hS (yoneda.obj Y)
        (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) _
        ((yoneda.map b).app _ x) := by
      rw [show (yoneda.map b).app _ x = f₂ ≫ y from hx]
      exact hz
    exact ⟨⟨ULift.up x, (hasImageIn_preimage_pointsMap_iff B S hS (yoneda.map b) _ _ x).2 hx'⟩,
      Subtype.ext (ULift.ext hx)⟩

include hIfg hI hbij in
/-- The completion of an étale neighbourhood `Spec C' ⟶ Y` of the closed fibre over `T` is an
isomorphism. -/
theorem isIso_completionSheafMap_specAlgOverι :
    IsIso (Space.completionSheafMap B S hS (yoneda.map (specAlgOverι B S hS Y
        (homOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY'))
        (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T)) := by
  have := isLocallyInjective_completionMap_specAlgOverι B S hS h T I hIfg hI hbij hY'
  have := isLocallySurjective_completionMap_specAlgOverι B S hS h T I hIfg hI hbij hY'
  exact isIso_completionSheafMap_of_isLocallyBijective B S hS _ _

end EtaleNeighbourhoodCompletion

section StageMaps

variable {X X' Y : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
  (T : Set (Space.points B S hS (yoneda.obj X)))
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj X, ⊤))
  (hI : Space.pointsToScheme B S hS X '' T =
    ((BigFppfOver.toScheme B S hS).obj X).zeroLocus (U := ⊤)
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)))
  (f : X' ⟶ X) (h : Y ⟶ X)
  (α : (Space.completionOverFunctor B S hS T).obj (Over.mk (yoneda.map h)) ⟶
    (Space.completionOverFunctor B S hS T).obj (Over.mk (yoneda.map f)))

/-- The `n`-th power of the ideal `IC` cutting out the closed fibre of `h : Y ⟶ X` over `V(I)`. -/
abbrev fibreIdealPow (n : ℕ) : Ideal Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
  (I.map ((BigFppfOver.toScheme B S hS).map h).appTop.hom) ^ n

/-- The spectrum of `C ⧸ (IC)ⁿ` lies in the site. -/
theorem contains_spec_fibreQuotient (n : ℕ) :
    B.Contains (Spec (.of (Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⧸
      fibreIdealPow B S hS I h n))) :=
  B.contains_specQuotient (contains_spec_globalSections B S hS Y) _

/-- The `n`-th infinitesimal neighbourhood `Spec(C ⧸ (IC)ⁿ)` of the closed fibre of `Y`. -/
abbrev fibreStage (n : ℕ) : BigFppfOver B S hS :=
  specAlgOver B S hS Y (homOf (Ideal.Quotient.mk (fibreIdealPow B S hS I h n)))
    (contains_spec_fibreQuotient B S hS I h n)

/-- The inclusion of the `n`-th infinitesimal neighbourhood of the closed fibre into `Y`. -/
abbrev fibreStageι (n : ℕ) : fibreStage B S hS I h n ⟶ Y :=
  specAlgOverι B S hS Y _ (contains_spec_fibreQuotient B S hS I h n)

include hI in
/-- The inclusion of the `n`-th infinitesimal neighbourhood of the closed fibre into `Y` has
point-set image over `T`. -/
theorem hasImageIn_fibreStageι (n : ℕ) :
    Space.HasImageIn B S hS (yoneda.obj Y)
      (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) _
      (fibreStageι B S hS I h n) :=
  hasImageIn_specAlgOverι_quotient B S hS h T I hI n _

/-- The value of `α` on the `n`-th infinitesimal neighbourhood of the closed fibre. -/
def stageMap (n : ℕ) : fibreStage B S hS I h n ⟶ X' :=
  completionEval B S hS (G := (Over.mk (yoneda.map f)).left)
    (isSheaf_yoneda_comp_uliftFunctor B S hS X') α.left _ (hasImageIn_fibreStageι B S hS T I hI h n)

/-- The value `stageMap α n` of `α` on the `n`-th infinitesimal neighbourhood lies over `X`. -/
theorem stageMap_comp (n : ℕ) : stageMap B S hS T I hI f h α n ≫ f = fibreStageι B S hS I h n ≫ h :=
  hom_app_completionEval B S hS T α (isSheaf_yoneda_comp_uliftFunctor B S hS X')
    (isSheaf_yoneda_comp_uliftFunctor B S hS X) _ _

/-- On a morphism `z : V ⟶ Y` over `T` which factors as `w` through the `n`-th infinitesimal
neighbourhood of the closed fibre, the value of `α` is `w ≫ stageMap α n`. -/
theorem completionEval_eq_comp_stageMap {V : BigFppfOver B S hS} (z : V ⟶ Y)
    (hz : Space.HasImageIn B S hS (yoneda.obj Y)
      (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) V z) (n : ℕ)
    (w : V ⟶ fibreStage B S hS I h n) (hw : w ≫ fibreStageι B S hS I h n = z) :
    completionEval B S hS (G := (Over.mk (yoneda.map f)).left)
      (isSheaf_yoneda_comp_uliftFunctor B S hS X') α.left z hz =
      w ≫ stageMap B S hS T I hI f h α n := by
  have hz' : Space.HasImageIn B S hS (yoneda.obj Y)
      (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) V
      (w ≫ fibreStageι B S hS I h n) := hw.symm ▸ hz
  exact (completionEval_congr B S hS _ α.left hw.symm _ hz').trans
    (completionEval_map B S hS _ α.left w _ _ hz')

/-- The ring map `Γ(X') → C ⧸ (IC)ⁿ` of `stageMap α n`, precomposed with the map of `f` on
global sections, is the quotient map precomposed with the map of `h`. -/
theorem specAlgOverRingOut_stageMap_comp (n : ℕ) :
    (specAlgOverRingOut B S hS Y _ _ (stageMap B S hS T I hI f h α n)).comp
        ((BigFppfOver.toScheme B S hS).map f).appTop.hom =
      (Ideal.Quotient.mk (fibreIdealPow B S hS I h n)).comp
        ((BigFppfOver.toScheme B S hS).map h).appTop.hom :=
  specAlgOverRingOut_comp_of_comp_eq B S hS Y _ _ _ f h (stageMap_comp B S hS T I hI f h α n)

/-- For `m ≤ n`, the ring map of `stageMap α n` followed by `C ⧸ (IC)ⁿ → C ⧸ (IC)ᵐ` is the
ring map of `stageMap α m`. -/
theorem factor_comp_specAlgOverRingOut_stageMap {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)).comp
        (specAlgOverRingOut B S hS Y _ _ (stageMap B S hS T I hI f h α n)) =
      specAlgOverRingOut B S hS Y _ _ (stageMap B S hS T I hI f h α m) := by
  have hmk : homOf (Ideal.Quotient.mk (fibreIdealPow B S hS I h n)) ≫
      CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) =
      homOf (Ideal.Quotient.mk (fibreIdealPow B S hS I h m)) := by
    ext x
    exact Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right hmn) x
  have hψ : homOf (Ideal.Quotient.mk (fibreIdealPow B S hS I h n)) ≫
      (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) ≫
        (Scheme.ΓSpecIso _).inv) =
      ((BigFppfOver.toScheme B S hS).map (fibreStageι B S hS I h m)).appTop :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Scheme.ΓSpecIso _).inv) hmk).trans
      (appTop_specAlgOverι B S hS Y _ _).symm)
  have ht := specAlgOverLift_comp_specAlgOverι B S hS Y _ (contains_spec_fibreQuotient B S hS I h n)
    (fibreStageι B S hS I h m) _ hψ
  have hcm := completionEval_eq_comp_stageMap B S hS T I hI f h α (fibreStageι B S hS I h m)
    (hasImageIn_fibreStageι B S hS T I hI h m) n _ ht
  have hcm' : stageMap B S hS T I hI f h α m = _ := hcm
  rw [hcm']
  exact ((specAlgOverRingOut_specAlgOverLift_comp B S hS Y _ _ _ _ _ _ hψ _).trans
    (ofHom_comp_ΓSpecIso_inv_comp_hom _ _)).symm

/-- The `A`-algebra map `B → C^∧` given by `α` on the infinitesimal neighbourhoods of the closed
fibre, `A`, `B`, `C` being the rings of `X`, `X'`, `Y`. -/
def stageAlgHom :
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) :=
      ((BigFppfOver.toScheme B S hS).map f).appTop.hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
      ((BigFppfOver.toScheme B S hS).map h).appTop.hom.toAlgebra
    Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) →ₐ[Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)]
      AdicCompletion (I.map ((BigFppfOver.toScheme B S hS).map h).appTop.hom)
        Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
  letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) :=
    ((BigFppfOver.toScheme B S hS).map f).appTop.hom.toAlgebra
  letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map h).appTop.hom.toAlgebra
  AdicCompletion.liftAlgHom _
    (fun n ↦ { specAlgOverRingOut B S hS Y _ _ (stageMap B S hS T I hI f h α n) with
      commutes' := fun a ↦
        RingHom.congr_fun (specAlgOverRingOut_stageMap_comp B S hS T I hI f h α n) a })
    fun hle ↦ AlgHom.ext fun x ↦
      RingHom.congr_fun (factor_comp_specAlgOverRingOut_stageMap B S hS T I hI f h α hle) x

/-- The `N`-th component of `stageAlgHom α` is the ring map of `stageMap α N`. -/
theorem evalₐ_stageAlgHom (N : ℕ) (x : Γ((BigFppfOver.toScheme B S hS).obj X', ⊤)) :
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) :=
      ((BigFppfOver.toScheme B S hS).map f).appTop.hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
      ((BigFppfOver.toScheme B S hS).map h).appTop.hom.toAlgebra
    AdicCompletion.evalₐ _ N (stageAlgHom B S hS T I hI f h α x) =
      specAlgOverRingOut B S hS Y _ _ (stageMap B S hS T I hI f h α N) x :=
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) :=
    ((BigFppfOver.toScheme B S hS).map f).appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map h).appTop.hom.toAlgebra
  AdicCompletion.evalₐ_liftAlgHom _ _ (fun hle ↦ AlgHom.ext fun x ↦
      RingHom.congr_fun (factor_comp_specAlgOverRingOut_stageMap B S hS T I hI f h α hle) x) N x

/-- On a morphism `z : V ⟶ Y` over `T` which factors through `Spec(C ⧸ (IC)^N)` by `l`, the value
of `α` is read off from `stageAlgHom`. -/
theorem appTop_completionEval_eq {V : BigFppfOver B S hS} (z : V ⟶ Y)
    (hz : Space.HasImageIn B S hS (yoneda.obj Y)
      (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map h) ⁻¹' T) V z) (N : ℕ)
    (l : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ⧸ fibreIdealPow B S hS I h N →+*
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hl : l.comp (Ideal.Quotient.mk _) = ((BigFppfOver.toScheme B S hS).map z).appTop.hom) :
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) :=
      ((BigFppfOver.toScheme B S hS).map f).appTop.hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
      ((BigFppfOver.toScheme B S hS).map h).appTop.hom.toAlgebra
    ((BigFppfOver.toScheme B S hS).map (completionEval B S hS (G := (Over.mk (yoneda.map f)).left)
      (isSheaf_yoneda_comp_uliftFunctor B S hS X') α.left z hz)).appTop.hom =
      l.comp ((AdicCompletion.evalₐ _ N).toRingHom.comp
        (stageAlgHom B S hS T I hI f h α).toRingHom) := by
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) :=
    ((BigFppfOver.toScheme B S hS).map f).appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map h).appTop.hom.toAlgebra
  have hw : homOf (Ideal.Quotient.mk (fibreIdealPow B S hS I h N)) ≫ homTo l =
      ((BigFppfOver.toScheme B S hS).map z).appTop := CommRingCat.hom_ext hl
  have hwz := specAlgOverLift_comp_specAlgOverι B S hS Y _
    (contains_spec_fibreQuotient B S hS I h N) z _ hw
  rw [completionEval_eq_comp_stageMap B S hS T I hI f h α z hz N _ hwz]
  refine (appTop_specAlgOverLift_comp B S hS Y _ _ z _ hw _).trans ?_
  ext x
  exact congrArg l (evalₐ_stageAlgHom B S hS T I hI f h α N x).symm

end StageMaps

/-! ### Morphisms of completions as étale factorizations -/

attribute [local instance] Space.pointTopology

/-- Let `X`, `X'`, `Y` be Noetherian affine schemes of the big fppf site over `S`, let `T ⊆ |X|`
be closed, let `f : X' ⟶ X` be locally of finite type and étale over `X ∖ T`, let `h : Y ⟶ X` be
a morphism and let `α : Y_{/T} ⟶ X'_{/T}` be a morphism over `X_{/T}`. Then there are an étale
morphism `b : Y' ⟶ Y` of affine schemes inducing an isomorphism `b_{/T} : Y'_{/T} ⟶ Y_{/T}` and
a morphism `a : Y' ⟶ X'` over `X` such that `α = a_{/T} ∘ b_{/T}⁻¹`.

Here `g_{/T}` is the completion along `T`, `Space.completionOverFunctor`, which sends `g : V ⟶ X`
to `V_{/g⁻¹T} ⟶ X_{/T}`. -/
@[stacks 0AR3]
theorem exists_etale_completion_factorization {X X' Y : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X)]
    [IsNoetherian ((BigFppfOver.toScheme B S hS).obj X)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X')]
    [IsNoetherian ((BigFppfOver.toScheme B S hS).obj X')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
    [IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    (T : Set (Space.points B S hS (yoneda.obj X))) (T_closed : IsClosed T)
    (f : X' ⟶ X) [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f)]
    (hf : ∀ p : Space.points B S hS (yoneda.obj X'),
      Space.pointsMap B S hS (yoneda.obj X') (yoneda.map f) p ∉ T →
        EtaleAt ((BigFppfOver.toScheme B S hS).map f) (Space.pointsToScheme B S hS X' p))
    (h : Y ⟶ X)
    (α : (Space.completionOverFunctor B S hS T).obj (Over.mk (yoneda.map h)) ⟶
      (Space.completionOverFunctor B S hS T).obj (Over.mk (yoneda.map f))) :
    ∃ (Y' : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y'))
      (b : Y' ⟶ Y) (_ : Etale ((BigFppfOver.toScheme B S hS).map b))
      (a : Y' ⟶ X') (comm_ab : a ≫ f = b ≫ h)
      (_ : IsIso ((Space.completionOverFunctor B S hS T).map
        (Over.homMk (yoneda.map b) : Over.mk (yoneda.map b ≫ yoneda.map h) ⟶
          Over.mk (yoneda.map h)))),
      α = inv ((Space.completionOverFunctor B S hS T).map
          (Over.homMk (yoneda.map b) : Over.mk (yoneda.map b ≫ yoneda.map h) ⟶
            Over.mk (yoneda.map h))) ≫
        (Space.completionOverFunctor B S hS T).map
          (Over.homMk (yoneda.map a) (by simp only [Over.mk_hom, ← Functor.map_comp, comm_ab]) :
            Over.mk (yoneda.map b ≫ yoneda.map h) ⟶ Over.mk (yoneda.map f)) := by
  classical
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) :=
    ((BigFppfOver.toScheme B S hS).map f).appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map h).appTop.hom.toAlgebra
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) :=
    RingHom.finiteType_algebraMap.mp
      ((HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance)
  obtain ⟨I, hI⟩ := (Scheme.eq_zeroLocus_of_isClosed_of_isAffine _ _).1
    (Space.isClosed_image_pointsToScheme B S hS X T_closed)
  have hIfg : I.FG := I.fg_of_isNoetherianRing
  have hEt : Rig.IsEtaleOutside I Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) :=
    isEtaleOutside_of_forall_etaleAt ((BigFppfOver.toScheme B S hS).map f) I fun x hx ↦ by
      obtain ⟨p, rfl⟩ := Space.surjective_pointsToScheme B S hS X' x
      refine hf p fun hp ↦ hx ?_
      rw [← hI, ← Space.pointsToScheme_pointsMap]
      exact ⟨_, hp, rfl⟩
  obtain ⟨ψ, hψ, -⟩ := Rig.exists_unique_algHom_henselization_of_algHom_adicCompletion
    Γ((BigFppfOver.toScheme B S hS).obj X, ⊤) Γ((BigFppfOver.toScheme B S hS).obj X', ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) I hEt (stageAlgHom B S hS T I hI f h α)
  obtain ⟨Cp, _, _, _, _, _, g, k, hbij, hk⟩ := Rig.exists_etale_factorization_algHom_henselization
    Γ((BigFppfOver.toScheme B S hS).obj X, ⊤) Γ((BigFppfOver.toScheme B S hS).obj X', ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) I ψ
  have hY' : B.Contains (Spec (.of Cp)) := contains_spec_of_etale B S hS Y
  obtain ⟨a, hab, ha⟩ := exists_hom_specAlgOver_of_algHom B S hS Y f h hY' g.toRingHom (by
    ext x
    show g (algebraMap _ _ x) = algebraMap _ Cp (algebraMap _ _ x)
    rw [g.commutes, IsScalarTower.algebraMap_apply _ Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)])
  set b := specAlgOverι B S hS Y (CommRingCat.ofHom
    (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp)) hY' with hb
  have hiso : IsIso ((Space.completionOverFunctor B S hS T).map
      (Over.homMk (yoneda.map b) : Over.mk (yoneda.map b ≫ yoneda.map h) ⟶
        Over.mk (yoneda.map h))) := by
    have : IsIso ((Over.forget _).map ((Space.completionOverFunctor B S hS T).map
        (Over.homMk (yoneda.map b) : Over.mk (yoneda.map b ≫ yoneda.map h) ⟶
          Over.mk (yoneda.map h)))) := by
      show IsIso (Space.completionOverMap B S hS T _)
      rw [Space.completionOverMap]
      have : IsIso (Space.completionSheafMap B S hS
          (Over.homMk (yoneda.map b) : Over.mk (yoneda.map b ≫ yoneda.map h) ⟶
            Over.mk (yoneda.map h)).left
          (Space.pointsMap B S hS (Over.mk (yoneda.map h)).left
            (Over.mk (yoneda.map h)).hom ⁻¹' T)) :=
        isIso_completionSheafMap_specAlgOverι B S hS h T I hIfg hI hbij hY'
      infer_instance
    exact isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨_, inferInstance, b, etale_specAlgOverι B S hS Y hY', a, hab, hiso, ?_⟩
  rw [IsIso.eq_inv_comp]
  apply Over.OverMorphism.ext
  refine completionSheaf_hom_ext B S hS (G := (Over.mk (yoneda.map f)).left)
    (isSheaf_yoneda_comp_uliftFunctor B S hS X') fun V x hx ↦ ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj V)) :=
    V.property
  have hxb := hasImageIn_over_left_app B S hS T
    (Over.homMk (yoneda.map b) : Over.mk (yoneda.map b ≫ yoneda.map h) ⟶ Over.mk (yoneda.map h))
    x hx
  refine (completionEval_completionOverMap_comp B S hS _ T _ α.left x hx hxb).trans ?_
  refine Eq.trans ?_ (completionEval_completionOverMap B S hS T _
    (isSheaf_yoneda_comp_uliftFunctor B S hS X') x hx).symm
  show completionEval B S hS (G := (Over.mk (yoneda.map f)).left)
    (isSheaf_yoneda_comp_uliftFunctor B S hS X') α.left (x ≫ b) hxb = x ≫ a
  obtain ⟨N, hN⟩ := isNilpotent_map_of_hasImageIn B S hS h T I hIfg hI (x ≫ b) hxb
  have hker : fibreIdealPow B S hS I h N ≤
      RingHom.ker ((BigFppfOver.toScheme B S hS).map (x ≫ b)).appTop.hom :=
    Ideal.map_le_iff_le_comap.1 (le_of_eq (by rw [Ideal.map_pow, hN, Ideal.zero_eq_bot]))
  let l := Ideal.Quotient.lift _ ((BigFppfOver.toScheme B S hS).map (x ≫ b)).appTop.hom
    fun r hr ↦ hker hr
  have hl : l.comp (Ideal.Quotient.mk _) =
      ((BigFppfOver.toScheme B S hS).map (x ≫ b)).appTop.hom :=
    Ideal.Quotient.lift_comp_mk _ _ _
  have hKx := appTop_completionEval_eq B S hS T I hI f h α (x ≫ b) hxb N l hl
  let θ : Cp →+* Γ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj V), ⊤) :=
    (l.comp (AdicCompletion.evalₐ (I.map (algebraMap Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤))) N).toRingHom).comp
      ((Rig.henselizationToAdicCompletion Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)
        (I.map (algebraMap Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)))).val.toRingHom.comp k.toRingHom)
  have hθ : θ.comp (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) Cp) =
      ((BigFppfOver.toScheme B S hS).map (x ≫ b)).appTop.hom := by
    ext c
    let H₀ := (Rig.henselizationToAdicCompletion Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)
      (I.map (algebraMap Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)))).val
    let E₀ := AdicCompletion.evalₐ (I.map (algebraMap Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤))) N
    have e1 := congrArg (fun q ↦ l (E₀ (H₀ q))) (k.commutes c)
    have e2 := congrArg (fun q ↦ l (E₀ q)) (H₀.commutes c)
    have e3 := congrArg l (E₀.commutes c)
    have e4 : l (Ideal.Quotient.mk _ c) =
        ((BigFppfOver.toScheme B S hS).map (x ≫ b)).appTop.hom c :=
      Ideal.Quotient.lift_mk _ _ _
    exact e1.trans (e2.trans (e3.trans e4))
  have hx_eq := specAlgOverRingHom_eq B S hS Y _ hbij hY' x ⟨N, hN⟩ θ hθ
  have e2 : ((BigFppfOver.toScheme B S hS).map (x ≫ a)).appTop.hom =
      (specAlgOverRingHom B S hS Y hY' x).comp g.toRingHom := by
    rw [appTop_toScheme_map_comp, ha]
    rfl
  apply (BigFppfOver.toScheme B S hS).map_injective
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  refine hKx.trans ?_
  rw [e2, hx_eq]
  ext p
  have h1 : stageAlgHom B S hS T I hI f h α p =
      (Rig.henselizationToAdicCompletion Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)
        (I.map (algebraMap Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)))).val (k (g p)) := by
    rw [← hψ, ← hk]
    rfl
  exact congrArg (fun q ↦ l (AdicCompletion.evalₐ _ N q)) h1

end AlgebraicGeometry.FormalSpace

end
