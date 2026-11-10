module

public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationInitial.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.UniversalHomeomorphismFilteredColimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.PhSheafOfSections
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global functions on absolute weak normalizations sheafify the structure sheaf

On a big ph site, and on a big h site, over a scheme `S`, the rule sending an object `X` to
the ring of global functions on its absolute weak normalization is the sheafification of the
structure sheaf.

## Main definitions

* `AlgebraicGeometry.absoluteWeakNormalizationSectionsMap` is the canonical map from the
  structure sheaf, given by pullback along the absolute weak normalization morphism.

## Main results

* `AlgebraicGeometry.isLocallyInjective_absoluteWeakNormalizationSectionsMap` and
  `AlgebraicGeometry.isLocallySurjective_absoluteWeakNormalizationSectionsMap`: the canonical
  map is locally bijective for the ph topology.
* `AlgebraicGeometry.existsUnique_hom_absoluteWeakNormalizationSections`: every map from the
  structure sheaf to a sheaf of rings factors uniquely through it.  Together with the sheaf
  property of Stacks 0EVT this is the ph case of Stacks 0EVU.
* `AlgebraicGeometry.BigHOver.isSheaf_absoluteWeakNormalizationSections` and
  `AlgebraicGeometry.BigHOver.existsUnique_hom_absoluteWeakNormalizationSections`: the two
  halves of the h case of Stacks 0EVU — the rule is a sheaf for the h topology, and the
  canonical map from the structure sheaf exhibits it as the sheafification.

## Implementation notes

A section of the structure sheaf dying on the absolute weak normalization is locally
nilpotent, because the absolute weak normalization is surjective; the closed subscheme it cuts
out is then a universal homeomorphism of finite presentation onto the ambient scheme, hence a
one-member ph covering killing the section, and — being locally of finite presentation — a
one-member h covering. Conversely a global function on the absolute weak normalization of an
affine scheme is a function on a finitely presented stage of the filtered system of universal
homeomorphisms computing it, by Stacks 0EUJ, and that stage is again such a one-member
covering. Both statements are reduced to the affine case over an affine open covering by the
transitivity of the topology, which avoids any composition of coverings.

The two topologies share this argument. It is carried out once, for an arbitrary topology on a
slice of a size-bounded category of schemes which sees the one-member families on universal
homeomorphisms locally of finite presentation and the affine open families, and the ph and the
h topology are then each shown to see those two kinds of family.

The sheaf property for the h topology is not deduced from the ph one, which is a statement
about a different site; it is proved from the same two descent statements of
`StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.PhSheafOfSections` through the h
sheaf criterion of Stacks 0EU5.

## References

* [Stacks Project, Tag 0EVU](https://stacks.math.columbia.edu/tag/0EVU)
* [Stacks Project, Tag 0EVT](https://stacks.math.columbia.edu/tag/0EVT)
* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
* [Stacks Project, Tag 0EUJ](https://stacks.math.columbia.edu/tag/0EUJ)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

/-! ### Factoring a map of presheaves of rings through a locally bijective map -/

section Factorization

variable {C : Type w} [Category.{v} C] {P Q R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Two maps out of a presheaf of rings which agree after a locally surjective map agree, if
their common target is a sheaf. -/
private theorem hom_ext_of_isLocallySurjective (J : GrothendieckTopology C) (φ : P ⟶ Q)
    (hsurj : Presheaf.IsLocallySurjective J φ)
    (hR : Presheaf.IsSheaf J (R ⋙ forget CommRingCat.{u}))
    {χ₁ χ₂ : Q ⟶ R} (h : φ ≫ χ₁ = φ ≫ χ₂) : χ₁ = χ₂ := by
  refine NatTrans.ext ?_
  ext X x
  refine Presheaf.eq_of_restrict_eq J hR (Presheaf.imageSieve_mem J φ x) ?_
  intro Y f hf
  have ha := Presheaf.app_localPreimage φ x f hf
  change (R.map f.op) ((χ₁.app X).hom x) = (R.map f.op) ((χ₂.app X).hom x)
  rw [← NatTrans.naturality_apply χ₁ f.op x, ← NatTrans.naturality_apply χ₂ f.op x, ← ha]
  simpa only [NatTrans.comp_app, CategoryTheory.comp_apply] using
    congrArg (fun η : P ⟶ R => (η.app (op Y)).hom (Presheaf.localPreimage φ x f hf)) h

/-- **The universal property of sheafification for presheaves of rings.** A locally injective,
locally surjective map of presheaves of rings exhibits its target as the sheafification of its
source: every map from the source to a sheaf of rings factors through it uniquely. -/
@[ega "0 3.5.6" "special case"]
private theorem existsUnique_hom_of_isLocallyBijective (J : GrothendieckTopology C) (φ : P ⟶ Q)
    (hinj : Presheaf.IsLocallyInjective J φ) (hsurj : Presheaf.IsLocallySurjective J φ)
    (hR : Presheaf.IsSheaf J R) (ψ : P ⟶ R) : ∃! χ : Q ⟶ R, φ ≫ χ = ψ := by
  have := CommRingCat.adj.rightAdjoint_preservesLimits.{v, max v w}
  have hR' := Presheaf.isSheaf_comp_of_isSheaf J R (forget CommRingCat.{u}) hR
  obtain ⟨χ, hχ, huniq⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective J
    (Functor.whiskerRight φ (forget CommRingCat.{u}))
    (Functor.whiskerRight ψ (forget CommRingCat.{u})) hR'
  let val (X : Cᵒᵖ) : Q.obj X → R.obj X := χ.app X
  have hfac (X : Cᵒᵖ) (a : P.obj X) : val X ((φ.app X).hom a) = (ψ.app X).hom a :=
    congrArg (fun η => η.app X a) hχ
  have hnat {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : Q.obj X) :
      val Y ((Q.map f).hom a) = (R.map f).hom (val X a) :=
    NatTrans.naturality_apply χ f a
  have hzero (X : Cᵒᵖ) : val X 0 = 0 := by simpa only [map_zero] using hfac X 0
  have hone (X : Cᵒᵖ) : val X 1 = 1 := by simpa only [map_one] using hfac X 1
  have hloc (X : Cᵒᵖ) (a b : Q.obj X) (u v : R.obj X)
      (h : ∀ (Y : C) (f : X ⟶ op Y) (a' b' : P.obj (op Y)),
        (φ.app (op Y)).hom a' = (Q.map f).hom a → (φ.app (op Y)).hom b' = (Q.map f).hom b →
          (R.map f).hom u = (R.map f).hom v) : u = v := by
    refine Presheaf.eq_of_restrict_eq J hR'
      (J.intersection_covering (Presheaf.imageSieve_mem J φ a)
        (Presheaf.imageSieve_mem J φ b)) ?_
    rintro Y f ⟨⟨a', ha⟩, b', hb⟩
    exact h Y f.op a' b' ha hb
  have hadd (X : Cᵒᵖ) (a b : Q.obj X) : val X (a + b) = val X a + val X b := by
    refine hloc X a b _ _ fun Y f a' b' ha hb => ?_
    rw [map_add, ← hnat f (a + b), ← hnat f a, ← hnat f b, map_add, ← ha, ← hb,
      ← map_add, hfac, hfac, hfac, map_add]
  have hmul (X : Cᵒᵖ) (a b : Q.obj X) : val X (a * b) = val X a * val X b := by
    refine hloc X a b _ _ fun Y f a' b' ha hb => ?_
    rw [map_mul, ← hnat f (a * b), ← hnat f a, ← hnat f b, map_mul, ← ha, ← hb,
      ← map_mul, hfac, hfac, hfac, map_mul]
  let ring (X : Cᵒᵖ) : Q.obj X →+* R.obj X :=
    { toFun := val X, map_one' := hone X, map_mul' := hmul X, map_zero' := hzero X,
      map_add' := hadd X }
  refine ⟨{ app := fun X => CommRingCat.ofHom (ring X), naturality := ?_ }, ?_, ?_⟩
  · intro X Y f
    ext a
    exact hnat f a
  · ext X a
    exact hfac X a
  · intro χ' hχ'
    refine hom_ext_of_isLocallySurjective J φ hsurj hR' (hχ'.trans ?_)
    ext X a
    exact (hfac X a).symm

/-- The pullback of an equalizer sieve of two sections is the equalizer sieve of their
restrictions. -/
private theorem pullback_equalizerSieve {X : C} (x y : P.obj (op X)) {Y : C} (g : Y ⟶ X) :
    (Presheaf.equalizerSieve x y).pullback g =
      Presheaf.equalizerSieve ((P.map g.op).hom x) ((P.map g.op).hom y) := by
  ext Z h
  change (P.map (h ≫ g).op).hom x = (P.map (h ≫ g).op).hom y ↔ _
  rw [op_comp, P.map_comp]
  rfl

end Factorization

/-! ### The canonical map from the structure sheaf -/

section Map

variable {C : Type w} [Category.{v} C]

/-- The presheaf of rings on `C` assigning to an object the ring of global functions on the
absolute weak normalization of its underlying scheme. -/
def absoluteWeakNormalizationSectionsOver (T : C ⥤ Scheme.{u}) : Cᵒᵖ ⥤ CommRingCat.{u} :=
  (T ⋙ absoluteWeakNormalizationFunctor).op ⋙ Scheme.Γ

/-- Pullback along the absolute weak normalization morphism, as a map from the structure sheaf
to the presheaf of global functions on absolute weak normalizations. -/
def absoluteWeakNormalizationSectionsMap (T : C ⥤ Scheme.{u}) :
    T.op ⋙ Scheme.Γ ⟶ absoluteWeakNormalizationSectionsOver T where
  app X := Scheme.Γ.map (T.obj X.unop).absoluteWeakNormalizationHom.op
  naturality X Y f := by
    change Scheme.Γ.map (T.map f.unop).op ≫
        Scheme.Γ.map (T.obj Y.unop).absoluteWeakNormalizationHom.op =
      Scheme.Γ.map (T.obj X.unop).absoluteWeakNormalizationHom.op ≫
        Scheme.Γ.map (absoluteWeakNormalizationMap (T.map f.unop)).op
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      absoluteWeakNormalizationMap_spec (T.map f.unop)]

end Map

/-! ### The affine case -/

/-- A ring element killed by a ring map whose spectrum is a universal homeomorphism is
nilpotent. -/
private theorem isNilpotent_of_universalHomeomorphism {A R : Type u} [CommRing A] [CommRing R]
    (f : A →+* R) (hf : UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom f).op))
    {x : A} (hx : f x = 0) : IsNilpotent x := by
  have hhomeo : IsHomeomorph (Scheme.Spec.map (CommRingCat.ofHom f).op) :=
    hf.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  have hsurj : Function.Surjective (PrimeSpectrum.comap (CommRingCat.ofHom f).hom) :=
    fun p ↦ hhomeo.surjective p
  have hker : RingHom.ker (CommRingCat.ofHom f).hom ≤ nilradical (CommRingCat.of A) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mp hsurj.denseRange
  exact mem_nilradical.mp (hker (RingHom.mem_ker.mpr hx))

/-- The spectrum of the quotient by an ideal of nilpotent elements is a universal
homeomorphism onto the spectrum. -/
private theorem universalHomeomorphism_Spec_quotient (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I ≤ nilradical A) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)).op) := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hs : Surjective (Spec.map φ) :=
    ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hI).2⟩
  have hc : IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_surjective φ Ideal.Quotient.mk_surjective
  have hi : IsIntegralHom (Spec.map φ) := by
    rw [IsIntegralHom.SpecMap_iff]
    exact RingHom.isIntegral_of_surjective φ.hom Ideal.Quotient.mk_surjective
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective
    (Spec.map φ)).2 ⟨hi, inferInstance, hs⟩

/-- An element of a ring whose spectrum is a universal homeomorphism over a base ring comes
from a finitely presented stage with the same property. -/
private theorem exists_finitePresentation_stage {A R : Type u} [CommRing A] [CommRing R]
    (f : A →+* R) (hf : UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom f).op))
    (x : R) :
    ∃ (D : Under (CommRingCat.of A)) (g : D.right ⟶ CommRingCat.of R),
      D.hom.hom.FinitePresentation ∧
        UniversalHomeomorphism (Scheme.Spec.map D.hom.op) ∧
        D.hom ≫ g = CommRingCat.ofHom f ∧ ∃ b : D.right, g.hom b = x := by
  obtain ⟨J, _, _, p, hp⟩ :=
    isFilteredColimit_finitePresentation_universalHomeomorphism f hf
  let q := p.map (Under.forget (CommRingCat.of A))
  obtain ⟨i, b, hb⟩ := Concrete.isColimit_exists_rep q.diag q.isColimit x
  exact ⟨p.diag.obj i, (p.ι.app i).right, (hp i).1, (hp i).2, Under.w _, b, hb⟩

/-- The absolute weak normalization of an affine scheme is affine. -/
theorem isAffine_absoluteWeakNormalization (X : Scheme.{u}) [IsAffine X] :
    IsAffine X.absoluteWeakNormalization := by
  have : IsIntegralHom X.absoluteWeakNormalizationHom :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp
      (universalHomeomorphism_absoluteWeakNormalizationHom X)).1
  exact isAffine_of_isAffineHom X.absoluteWeakNormalizationHom

/-- A universal homeomorphism of affine schemes induces a universal homeomorphism on the
spectra of its rings of global functions. -/
private theorem universalHomeomorphism_Spec_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (hf : UniversalHomeomorphism f) :
    UniversalHomeomorphism (Scheme.Spec.map f.appTop.op) :=
  ⟨((topologically @IsHomeomorph).universally.arrow_mk_iso_iff
    (arrowIsoSpecΓOfIsAffine f)).mp hf.universally_isHomeomorph⟩

/-- A universal homeomorphism of spectra, followed by the inverse of the canonical isomorphism
onto an affine scheme, is a universal homeomorphism. -/
private theorem universalHomeomorphism_comp_isoSpec_inv {Y : Scheme.{u}} [IsAffine Y]
    {R : CommRingCat.{u}} (φ : CommRingCat.of Γ(Y, ⊤) ⟶ R)
    (hφ : UniversalHomeomorphism (Spec.map φ)) :
    UniversalHomeomorphism (Spec.map φ ≫ Y.isoSpec.inv) :=
  ⟨((topologically @IsHomeomorph).universally.cancel_right_of_respectsIso
    (Spec.map φ) Y.isoSpec.inv).mpr hφ.universally_isHomeomorph⟩

/-- A global function on the source of a universal homeomorphism of affine schemes is pulled
back from a finitely presented universal homeomorphism over the target. -/
private theorem exists_lift_section_of_universalHomeomorphism {X Y : Scheme.{u}} [IsAffine X]
    [IsAffine Y] (f : X ⟶ Y) (hf : UniversalHomeomorphism f) (x : Γ(X, ⊤)) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ Y) (k : X ⟶ Z) (b : Γ(Z, ⊤)),
      IsAffine Z ∧ UniversalHomeomorphism g ∧ LocallyOfFinitePresentation g ∧
        k ≫ g = f ∧ k.appTop.hom b = x := by
  obtain ⟨D, h, hfp, hD, hh, b, hb⟩ :=
    exists_finitePresentation_stage f.appTop.hom (universalHomeomorphism_Spec_appTop f hf) x
  let g := Spec.map D.hom ≫ Y.isoSpec.inv
  let k := X.isoSpec.hom ≫ Spec.map h
  have hg : UniversalHomeomorphism g := universalHomeomorphism_comp_isoSpec_inv D.hom hD
  have hlfp : LocallyOfFinitePresentation g := by
    have : LocallyOfFinitePresentation (Spec.map D.hom) :=
      (LocallyOfFinitePresentation.SpecMap_iff D.hom).mpr hfp
    dsimp only [g]
    infer_instance
  have hkg : k ≫ g = f := by
    change (X.isoSpec.hom ≫ Spec.map h) ≫ Spec.map D.hom ≫ Y.isoSpec.inv = f
    rw [Category.assoc, ← Category.assoc (Spec.map h), ← Spec.map_comp, hh]
    change X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp
  refine ⟨Scheme.Spec.obj (op D.right), g, k, (Scheme.ΓSpecIso D.right).inv.hom b,
    inferInstance, hg, hlfp, hkg, ?_⟩
  have heq : (Scheme.ΓSpecIso D.right).inv ≫ k.appTop = h := by
    change (Scheme.ΓSpecIso D.right).inv ≫ (Spec.map h).appTop ≫ X.isoSpec.hom.appTop = h
    rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    simp
  exact (congrArg (fun φ : D.right ⟶ CommRingCat.of Γ(X, ⊤) => φ.hom b) heq).trans hb

/-- Two morphisms from an absolute weak normalization into a universal homeomorphism over the
same scheme which agree there are equal. -/
private theorem absoluteWeakNormalization_hom_ext {X Y Z : Scheme.{u}} (f : X ⟶ Z) (p : Y ⟶ Z)
    (hp : UniversalHomeomorphism p) (g h : X.absoluteWeakNormalization ⟶ Y)
    (hg : g ≫ p = X.absoluteWeakNormalizationHom ≫ f)
    (hh : h ≫ p = X.absoluteWeakNormalizationHom ≫ f) : g = h := by
  let W : UniversalHomeomorphismOver X :=
    UniversalHomeomorphismOver.pullback f ⟨Over.mk p, hp⟩
  let a (k : X.absoluteWeakNormalization ⟶ Y)
      (hk : k ≫ p = X.absoluteWeakNormalizationHom ≫ f) :
      initial (UniversalHomeomorphismOver X) ⟶ W :=
    ⟨Over.homMk (pullback.lift X.absoluteWeakNormalizationHom k hk.symm) (by
      change pullback.lift _ _ _ ≫ pullback.fst f p = X.absoluteWeakNormalizationHom
      exact pullback.lift_fst _ _ _)⟩
  have he := initialIsInitial.hom_ext (a g hg) (a h hh)
  have hkey := congrArg
    (fun q : initial (UniversalHomeomorphismOver X) ⟶ W => q.hom.left ≫ pullback.snd f p) he
  change pullback.lift X.absoluteWeakNormalizationHom g hg.symm ≫ pullback.snd f p =
    pullback.lift X.absoluteWeakNormalizationHom h hh.symm ≫ pullback.snd f p at hkey
  simpa only [pullback.lift_snd] using hkey

/-- A global function on the absolute weak normalization of an affine scheme is pulled back
from a global function on a finitely presented universal homeomorphism over it. -/
private theorem exists_universalHomeomorphism_lift_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (x : Γ(X.absoluteWeakNormalization, ⊤)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (y : Γ(Y, ⊤)),
      UniversalHomeomorphism f ∧ LocallyOfFinitePresentation f ∧ IsAffine Y ∧
        Y.absoluteWeakNormalizationHom.appTop.hom y =
          (absoluteWeakNormalizationMap f).appTop.hom x := by
  have : IsAffine X.absoluteWeakNormalization := isAffine_absoluteWeakNormalization X
  obtain ⟨Y, f, k, b, _, hf, hfp, hk, hb⟩ :=
    exists_lift_section_of_universalHomeomorphism X.absoluteWeakNormalizationHom
      (universalHomeomorphism_absoluteWeakNormalizationHom X) x
  refine ⟨Y, f, b, hf, hfp, inferInstance, ?_⟩
  have he : Y.absoluteWeakNormalizationHom = absoluteWeakNormalizationMap f ≫ k := by
    refine absoluteWeakNormalization_hom_ext f f hf _ _ rfl ?_
    rw [Category.assoc, hk]
    exact absoluteWeakNormalizationMap_spec f
  rw [he]
  change (absoluteWeakNormalizationMap f).appTop.hom (k.appTop.hom b) = _
  rw [hb]

/-- A global function on an affine scheme dying on its absolute weak normalization dies on a
finitely presented universal homeomorphism over it. -/
private theorem exists_universalHomeomorphism_kill_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (x : Γ(X, ⊤)) (hx : X.absoluteWeakNormalizationHom.appTop.hom x = 0) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      UniversalHomeomorphism f ∧ LocallyOfFinitePresentation f ∧ IsAffine Y ∧
        f.appTop.hom x = 0 := by
  have : IsAffine X.absoluteWeakNormalization := isAffine_absoluteWeakNormalization X
  have hn := isNilpotent_of_universalHomeomorphism X.absoluteWeakNormalizationHom.appTop.hom
    (universalHomeomorphism_Spec_appTop _
      (universalHomeomorphism_absoluteWeakNormalizationHom X)) hx
  let I : Ideal Γ(X, ⊤) := Ideal.span {x}
  let q : CommRingCat.of Γ(X, ⊤) ⟶ CommRingCat.of (Γ(X, ⊤) ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hI : I ≤ nilradical Γ(X, ⊤) := by
    refine Ideal.span_le.mpr ?_
    simpa using mem_nilradical.mpr hn
  let f := Spec.map q ≫ X.isoSpec.inv
  have hf : UniversalHomeomorphism f :=
    universalHomeomorphism_comp_isoSpec_inv q (universalHomeomorphism_Spec_quotient _ I hI)
  have : LocallyOfFinitePresentation (Spec.map q) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    change (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⧸ I)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    exact Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton x)
  have hlfp : LocallyOfFinitePresentation f := by
    dsimp only [f]
    infer_instance
  refine ⟨_, f, hf, hlfp, inferInstance, ?_⟩
  have he : Scheme.Γ.mapIso X.isoSpec.op = Scheme.ΓSpecIso Γ(X, ⊤) := by
    refine Iso.ext ?_
    change X.isoSpec.hom.appTop = _
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  have hmap : f.appTop = q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⧸ I))).inv := by
    change X.isoSpec.inv.appTop ≫ (Spec.map q).appTop = _
    rw [show X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv from congrArg Iso.inv he,
      ← Scheme.ΓSpecIso_inv_naturality]
  rw [hmap]
  change (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⧸ I))).inv.hom (Ideal.Quotient.mk I x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton x)), map_zero]

/-- A universal homeomorphism of schemes which is locally of finite presentation is finite. -/
private theorem isFinite_of_universalHomeomorphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : UniversalHomeomorphism f) [LocallyOfFinitePresentation f] : IsFinite f :=
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr
    ⟨((universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp hf).1,
      inferInstance⟩

/-- A universal homeomorphism of schemes which is locally of finite presentation is a one
member ph covering. -/
private theorem isPHCovering_of_universalHomeomorphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : UniversalHomeomorphism f) [LocallyOfFinitePresentation f] :
    IsPHCovering (fun _ : PUnit.{u + 2} ↦ X) (fun _ ↦ f) := by
  have := isFinite_of_universalHomeomorphism f hf
  obtain ⟨-, -, _⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp hf
  exact IsPHCovering.reindex (surjective_proper_isPHCovering f)
    (Equiv.ofUnique PUnit.{u + 2} Unit)

/-- The source of a universal homeomorphism locally of finite presentation onto a scheme of
size below a cutoff again has size below that cutoff. -/
private theorem size_lt_of_universalHomeomorphism {κ : Cardinal.{u}} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : UniversalHomeomorphism f) [LocallyOfFinitePresentation f]
    (hY : Y.size < κ) : X.size < κ := by
  have := isFinite_of_universalHomeomorphism f hf
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hY

/-! ### Values of the canonical map -/

section Values

variable {C : Type w} [Category.{v} C] (T : C ⥤ Scheme.{u})

/-- The canonical map sends a global function to its pullback along the absolute weak
normalization morphism. -/
private theorem absoluteWeakNormalizationSectionsMap_app_apply (X : C) (x : Γ(T.obj X, ⊤)) :
    (absoluteWeakNormalizationSectionsMap T).app (op X) x =
      (T.obj X).absoluteWeakNormalizationHom.appTop.hom x :=
  rfl

end Values

/-! ### Families in a slice of a size-bounded category of schemes -/

section OverSlice

variable {κ : Cardinal.{u}} (T : SchemeBelow κ)

/-- The canonical functor from a slice of a size-bounded category of schemes to schemes. -/
private abbrev overToScheme : Over T ⥤ Scheme.{u} :=
  Over.forget T ⋙ schemeBelowInclusion κ

/-- An object of a slice of a size-bounded category of schemes, built from a morphism of
schemes into the underlying scheme of a given object. -/
private def overOfHom {X : Over T} {Y : Scheme.{u}} (f : Y ⟶ (overToScheme T).obj X)
    (hY : Y.size < κ) : Over T :=
  Over.mk ((⟨f⟩ : (⟨Y, hY⟩ : SchemeBelow κ) ⟶ X.left) ≫ X.hom)

/-- The structure morphism of `AlgebraicGeometry.overOfHom`. -/
private def overHomOfHom {X : Over T} {Y : Scheme.{u}} (f : Y ⟶ (overToScheme T).obj X)
    (hY : Y.size < κ) : overOfHom T f hY ⟶ X :=
  Over.homMk (⟨f⟩ : (⟨Y, hY⟩ : SchemeBelow κ) ⟶ X.left) rfl

/-- The one member family on a morphism of schemes into an object of a slice of a size-bounded
category of schemes, as a family in that slice. -/
private def singletonFamily {X : Over T} {Y : Scheme.{u}} (f : Y ⟶ (overToScheme T).obj X)
    (hY : Y.size < κ) : PreZeroHypercover.{u + 1} X where
  I₀ := PUnit.{u + 2}
  X _ := overOfHom T f hY
  f _ := overHomOfHom T f hY

/-- The affine opens of the underlying scheme of an object of a slice of a size-bounded
category of schemes, as a family in that slice. -/
private def affineOpenFamily (X : Over T) : PreZeroHypercover.{u + 1} X where
  I₀ := ULift.{u + 1, u} ((overToScheme T).obj X).affineOpens
  X i := overOfHom T i.down.1.ι
    (Scheme.size_lt_of_isOpenImmersion i.down.1.ι X.left.property)
  f i := overHomOfHom T i.down.1.ι
    (Scheme.size_lt_of_isOpenImmersion i.down.1.ι X.left.property)

/-- The underlying scheme of a member of the affine open family is affine. -/
private theorem isAffine_affineOpenFamily (X : Over T) (i : (affineOpenFamily T X).I₀) :
    IsAffine ((overToScheme T).obj ((affineOpenFamily T X).X i)) :=
  i.down.2

/-- The one member family on a universal homeomorphism locally of finite presentation is a ph
covering. -/
private theorem isPHCovering_singletonFamily {X : Over T} {Y : Scheme.{u}}
    (f : Y ⟶ (overToScheme T).obj X) (hY : Y.size < κ) (hf : UniversalHomeomorphism f)
    [LocallyOfFinitePresentation f] :
    IsPHCovering (fun i ↦ (overToScheme T).obj ((singletonFamily T f hY).X i))
      (fun i ↦ (overToScheme T).map ((singletonFamily T f hY).f i)) :=
  isPHCovering_of_universalHomeomorphism f hf

/-- The member of the one member family on a morphism locally of finite presentation is
locally of finite presentation. -/
private theorem locallyOfFinitePresentation_singletonFamily {X : Over T} {Y : Scheme.{u}}
    (f : Y ⟶ (overToScheme T).obj X) (hY : Y.size < κ) [LocallyOfFinitePresentation f]
    (i : (singletonFamily T f hY).I₀) :
    LocallyOfFinitePresentation ((overToScheme T).map ((singletonFamily T f hY).f i)) :=
  inferInstanceAs (LocallyOfFinitePresentation f)

/-- The affine open family of an object is a ph covering. -/
private theorem isPHCovering_affineOpenFamily (X : Over T) :
    IsPHCovering (fun i ↦ (overToScheme T).obj ((affineOpenFamily T X).X i))
      (fun i ↦ (overToScheme T).map ((affineOpenFamily T X).f i)) :=
  IsPHCovering.reindex (IsPHCovering.of_openCover
    (((overToScheme T).obj X).openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top _)))
    Equiv.ulift

/-- The members of the affine open family are open immersions, hence locally of finite
presentation. -/
private theorem locallyOfFinitePresentation_affineOpenFamily (X : Over T)
    (i : (affineOpenFamily T X).I₀) :
    LocallyOfFinitePresentation ((overToScheme T).map ((affineOpenFamily T X).f i)) :=
  inferInstanceAs (LocallyOfFinitePresentation (Scheme.Opens.ι i.down.1))

end OverSlice

/-! ### Local bijectivity of the canonical map on a slice -/

section Slice

variable {κ : Cardinal.{u}} {T : SchemeBelow κ} (J : GrothendieckTopology (Over T))

/-- A topology on a slice of a size-bounded category of schemes sees the one member family on
every universal homeomorphism locally of finite presentation onto the underlying scheme of an
object. -/
private abbrev CoversUniversalHomeomorphisms : Prop :=
  ∀ (X : Over T) (Y : Scheme.{u}) (f : Y ⟶ (overToScheme T).obj X) (hY : Y.size < κ),
    UniversalHomeomorphism f → LocallyOfFinitePresentation f →
      (singletonFamily T f hY).sieve₀ ∈ J X

/-- A topology on a slice of a size-bounded category of schemes sees the family of affine
opens of every object. -/
private abbrev CoversAffineOpens : Prop :=
  ∀ X : Over T, (affineOpenFamily T X).sieve₀ ∈ J X

/-- A sieve containing the one member family on a universal homeomorphism locally of finite
presentation onto an object is covering. -/
private theorem mem_of_singletonFamily (hJ : CoversUniversalHomeomorphisms J) {X : Over T}
    (S : Sieve X) {Y : Scheme.{u}} (f : Y ⟶ (overToScheme T).obj X) (hf : UniversalHomeomorphism f)
    [LocallyOfFinitePresentation f]
    (hS : ∀ hY : Y.size < κ, S.arrows (overHomOfHom T f hY)) : S ∈ J X := by
  have hY := size_lt_of_universalHomeomorphism f hf X.left.property
  refine J.superset_covering ?_ (hJ X Y f hY hf inferInstance)
  rw [Sieve.generate_le_iff]
  rintro V p ⟨_⟩
  exact hS hY

/-- A sieve is covering if its pullback to every member of the affine open family, which has
affine underlying scheme, is. -/
private theorem mem_of_affineOpenFamily (hJ' : CoversAffineOpens J) {X : Over T} (S : Sieve X)
    (h : ∀ i : (affineOpenFamily T X).I₀,
      IsAffine ((overToScheme T).obj ((affineOpenFamily T X).X i)) →
        S.pullback ((affineOpenFamily T X).f i) ∈ J _) : S ∈ J X := by
  refine J.transitive (hJ' X) _ ?_
  intro V p hp
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hp
  rw [Sieve.pullback_comp]
  exact J.pullback_stable a (h i (isAffine_affineOpenFamily T X i))

/-- Over an object with affine underlying scheme, a global function on the absolute weak
normalization lifts to the structure sheaf along a covering. -/
private theorem imageSieve_mem_of_isAffine (hJ : CoversUniversalHomeomorphisms J) (X : Over T)
    [IsAffine ((overToScheme T).obj X)]
    (s : Γ(((overToScheme T).obj X).absoluteWeakNormalization, ⊤)) :
    Presheaf.imageSieve (absoluteWeakNormalizationSectionsMap (overToScheme T)) (U := X) s
      ∈ J X := by
  obtain ⟨Y, f, y, hf, hfp, _, hy⟩ :=
    exists_universalHomeomorphism_lift_of_isAffine ((overToScheme T).obj X) s
  exact mem_of_singletonFamily J hJ _ f hf fun _ ↦ ⟨y, hy⟩

/-- Over an object with affine underlying scheme, two global functions with the same pullback
to the absolute weak normalization agree along a covering. -/
private theorem equalizerSieve_mem_of_isAffine (hJ : CoversUniversalHomeomorphisms J)
    (X : Over T) [IsAffine ((overToScheme T).obj X)] (x y : Γ((overToScheme T).obj X, ⊤))
    (h : (absoluteWeakNormalizationSectionsMap (overToScheme T)).app (op X) x =
      (absoluteWeakNormalizationSectionsMap (overToScheme T)).app (op X) y) :
    Presheaf.equalizerSieve (F := (overToScheme T).op ⋙ Scheme.Γ) (X := op X) x y ∈ J X := by
  rw [absoluteWeakNormalizationSectionsMap_app_apply,
    absoluteWeakNormalizationSectionsMap_app_apply] at h
  have hz : ((overToScheme T).obj X).absoluteWeakNormalizationHom.appTop.hom (x - y) = 0 := by
    rw [map_sub, h, sub_self]
  obtain ⟨Z, f, hf, hfp, _, hzero⟩ :=
    exists_universalHomeomorphism_kill_of_isAffine ((overToScheme T).obj X) _ hz
  exact mem_of_singletonFamily J hJ _ f hf fun _ ↦
    sub_eq_zero.mp ((map_sub (Scheme.Hom.appTop f).hom x y).symm.trans hzero)

/-- **Clause (2) of Stacks 0EVU.** Every global function on the absolute weak normalization of
an object is, along a covering of that object, pulled back from global functions on the
members. -/
private theorem isLocallySurjective_sectionsMap (hJ : CoversUniversalHomeomorphisms J)
    (hJ' : CoversAffineOpens J) :
    Presheaf.IsLocallySurjective J (absoluteWeakNormalizationSectionsMap (overToScheme T)) where
  imageSieve_mem {X} s := by
    refine mem_of_affineOpenFamily J hJ' _ fun i _ ↦ ?_
    rw [Presheaf.pullback_imageSieve]
    exact imageSieve_mem_of_isAffine J hJ _ _

/-- **Clause (1) of Stacks 0EVU.** A global function on an object which dies on its absolute
weak normalization dies along a covering of that object. -/
private theorem isLocallyInjective_sectionsMap (hJ : CoversUniversalHomeomorphisms J)
    (hJ' : CoversAffineOpens J) :
    Presheaf.IsLocallyInjective J (absoluteWeakNormalizationSectionsMap (overToScheme T)) where
  equalizerSieve_mem {X} x y h := by
    refine mem_of_affineOpenFamily J hJ' _ fun i _ ↦ ?_
    rw [pullback_equalizerSieve]
    refine equalizerSieve_mem_of_isAffine J hJ _ _ _ ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]

end Slice

/-! ### Covering sieves of the big ph category over a scheme -/

section Sieves

variable (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A ph covering family of an object of a big ph site generates a covering sieve, because the
site contains a combinatorially equivalent family. -/
private theorem sieve₀_mem_topology {X : B.Schemes} (E : PreZeroHypercover.{u + 1} X)
    (hE : IsPHCoveringInCutoff ⟨X, E⟩) : E.sieve₀ ∈ B.topology X := by
  obtain ⟨V, hV, he, hcomb⟩ := B.covering_representative ⟨X, E⟩ hE
  obtain ⟨Vbase, Vfam⟩ := V
  change X = Vbase at he
  subst he
  change Sieve.generate E.presieve₀ ∈ B.topology X
  rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb]
  exact Precoverage.generate_mem_toGrothendieck ((B.mem_precoverage_iff).2 ⟨Vfam, rfl, hV⟩)

/-- A family in the big ph category over `S` whose underlying family of schemes is a ph
covering generates a covering sieve. -/
private theorem sieve₀_mem_bigPHOver_topology {X : BigPHOver B S hS}
    (E : PreZeroHypercover.{u + 1} X)
    (hE : IsPHCovering (fun i ↦ (BigPHOver.toScheme B S hS).obj (E.X i))
      (fun i ↦ (BigPHOver.toScheme B S hS).map (E.f i))) :
    E.sieve₀ ∈ BigPHOver.topology B S hS X := by
  rw [BigPHOver.topology, GrothendieckTopology.mem_over_iff]
  change Sieve.overEquiv X (Sieve.ofArrows E.X E.f) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  exact sieve₀_mem_topology B (E.map (BigPHOver.forget B S hS)) hE

/-- The one member family on a universal homeomorphism locally of finite presentation onto an
object of the big ph category over `S` generates a covering sieve. -/
private theorem coversUniversalHomeomorphisms_bigPHOver :
    CoversUniversalHomeomorphisms (BigPHOver.topology B S hS) := by
  intro X Y f hY hf hfp
  exact sieve₀_mem_bigPHOver_topology B S hS (singletonFamily (B.obj S hS) f hY)
    (isPHCovering_singletonFamily (B.obj S hS) f hY hf)

/-- The affine open family of an object of the big ph category over `S` generates a covering
sieve. -/
private theorem coversAffineOpens_bigPHOver :
    CoversAffineOpens (BigPHOver.topology B S hS) := fun X ↦
  sieve₀_mem_bigPHOver_topology B S hS (affineOpenFamily (B.obj S hS) X)
    (isPHCovering_affineOpenFamily (B.obj S hS) X)

end Sieves

/-! ### Local bijectivity of the canonical map -/

section LocallyBijective

variable (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Clause (2) of Stacks 0EVU.** Every global function on the absolute weak normalization of
an object of a big ph site is, along a ph covering of that object, pulled back from a global
function on the members. -/
instance isLocallySurjective_absoluteWeakNormalizationSectionsMap :
    Presheaf.IsLocallySurjective (BigPHOver.topology B S hS)
      (absoluteWeakNormalizationSectionsMap (BigPHOver.toScheme B S hS)) :=
  isLocallySurjective_sectionsMap _ (coversUniversalHomeomorphisms_bigPHOver B S hS)
    (coversAffineOpens_bigPHOver B S hS)

/-- **Clause (1) of Stacks 0EVU.** A global function on an object of a big ph site which dies
on its absolute weak normalization dies along a ph covering of that object. -/
instance isLocallyInjective_absoluteWeakNormalizationSectionsMap :
    Presheaf.IsLocallyInjective (BigPHOver.topology B S hS)
      (absoluteWeakNormalizationSectionsMap (BigPHOver.toScheme B S hS)) :=
  isLocallyInjective_sectionsMap _ (coversUniversalHomeomorphisms_bigPHOver B S hS)
    (coversAffineOpens_bigPHOver B S hS)

/-- **Stacks Project, Tag 0EVU**, the ph case. On a big ph site over `S`, global functions on
absolute weak normalizations are the sheafification of the structure sheaf: every map from the
structure sheaf to a sheaf of rings factors uniquely through the canonical map. The other half
of the statement, that the target is a sheaf, is Stacks 0EVT. -/
@[stacks 0EVU "ph topology"]
theorem existsUnique_hom_absoluteWeakNormalizationSections
    (G : (BigPHOver B S hS)ᵒᵖ ⥤ CommRingCat.{u})
    (hG : Presheaf.IsSheaf (BigPHOver.topology B S hS) G)
    (α : (BigPHOver.toScheme B S hS).op ⋙ Scheme.Γ ⟶ G) :
    ∃! χ : absoluteWeakNormalizationSections B S hS ⟶ G,
      absoluteWeakNormalizationSectionsMap (BigPHOver.toScheme B S hS) ≫ χ = α :=
  existsUnique_hom_of_isLocallyBijective (BigPHOver.topology B S hS) _
    (isLocallyInjective_absoluteWeakNormalizationSectionsMap B S hS)
    (isLocallySurjective_absoluteWeakNormalizationSectionsMap B S hS) hG α

end LocallyBijective

/-! ### The h topology -/

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The one member family on a universal homeomorphism locally of finite presentation onto an
object of the big h category over `S` generates a covering sieve: it is a ph covering whose
member is locally of finite presentation, hence an h covering. -/
private theorem coversUniversalHomeomorphisms :
    CoversUniversalHomeomorphisms (BigHOver.topology B S hS) := by
  intro X Y f hY hf hfp
  exact sieve₀_mem_topology_of_isHCovering B S hS (singletonFamily (B.obj S hS) f hY)
    ⟨locallyOfFinitePresentation_singletonFamily (B.obj S hS) f hY,
      isPHCovering_singletonFamily (B.obj S hS) f hY hf⟩

/-- The affine open family of an object of the big h category over `S` generates a covering
sieve: its members are open immersions, hence locally of finite presentation. -/
private theorem coversAffineOpens : CoversAffineOpens (BigHOver.topology B S hS) := fun X ↦
  sieve₀_mem_topology_of_isHCovering B S hS (affineOpenFamily (B.obj S hS) X)
    ⟨locallyOfFinitePresentation_affineOpenFamily (B.obj S hS) X,
      isPHCovering_affineOpenFamily (B.obj S hS) X⟩

/-- **Clause (2) of Stacks 0EVU for the h topology.** Every global function on the absolute
weak normalization of an object of a big h site is, along an h covering of that object, pulled
back from a global function on the members. -/
instance isLocallySurjective_absoluteWeakNormalizationSectionsMap :
    Presheaf.IsLocallySurjective (BigHOver.topology B S hS)
      (absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS)) :=
  isLocallySurjective_sectionsMap _ (coversUniversalHomeomorphisms B S hS)
    (coversAffineOpens B S hS)

/-- **Clause (1) of Stacks 0EVU for the h topology.** A global function on an object of a big
h site which dies on its absolute weak normalization dies along an h covering of that
object. -/
instance isLocallyInjective_absoluteWeakNormalizationSectionsMap :
    Presheaf.IsLocallyInjective (BigHOver.topology B S hS)
      (absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS)) :=
  isLocallyInjective_sectionsMap _ (coversUniversalHomeomorphisms B S hS)
    (coversAffineOpens B S hS)

/-- **Stacks Project, Tag 0EVU**, the sheaf property in the h case. On a big h site over `S`,
global functions on absolute weak normalizations form a sheaf for the h topology.

This is the h analogue of Stacks 0EVT, and is proved from the same two descent statements —
Zariski descent and descent along a proper surjection onto an affine — through the h sheaf
criterion of Stacks 0EU5, whose second condition carries the extra hypothesis that the proper
surjection is of finite presentation. -/
@[stacks 0EVU "h topology, the sheaf property"]
theorem isSheaf_absoluteWeakNormalizationSections :
    Presheaf.IsSheaf (BigHOver.topology B S hS)
      (absoluteWeakNormalizationSectionsOver (BigHOver.toScheme B S hS)) := by
  let F := BigHOver.toScheme B S hS
  let P := F.op ⋙ absoluteWeakNormalizationSectionTypes
  have _ : ReflectsLimitsOfSize.{u, u + 1} (CategoryTheory.forget CommRingCat.{u}) :=
    { reflectsLimitsOfShape := fun {J} _ =>
      { reflectsLimit := fun {D} =>
        { reflects := fun {c} hc => ⟨isLimit_of_isLimit_forget c hc⟩ } } }
  refine Presheaf.isSheaf_of_isSheaf_comp (BigHOver.topology B S hS)
    (absoluteWeakNormalizationSectionsOver F) (CategoryTheory.forget CommRingCat.{u}) ?_
  refine (isSheaf_iff_isSheaf_of_type _ _).mpr ?_
  change Presieve.IsSheaf (BigHOver.topology B S hS) P
  have hz : BigHOver.IsZariskiSheaf B S hS P := by
    intro X E hE
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks F
      absoluteWeakNormalizationSectionTypes E.presieve₀, ← PreZeroHypercover.presieve₀_map]
    exact isSheafFor_absoluteWeakNormalizationSections_of_zariskiCover (E.map F).f hE
  refine isSheaf_of_isZariskiSheaf_of_isProperFinitePresentationSheaf hz
    (isProperFinitePresentationSheaf_of_affine hz ?_)
  intro X Y f hX hproper hsurj _
  have _ : IsAffine (F.obj X) := hX
  have _ : IsProper (F.map f) := hproper
  have _ : Surjective (F.map f) := hsurj
  rw [← Presieve.ofArrows_pUnit,
    Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks F
      absoluteWeakNormalizationSectionTypes, Presieve.map_ofArrows]
  exact isSheafFor_absoluteWeakNormalizationSections_of_properSurjective (F.map f)

/-- **Stacks Project, Tag 0EVU**, the h case. On a big h site over `S`, global functions on
absolute weak normalizations are the sheafification of the structure sheaf: every map from the
structure sheaf to a sheaf of rings factors uniquely through the canonical map. Together with
`AlgebraicGeometry.BigHOver.isSheaf_absoluteWeakNormalizationSections`, which is the other half
of the statement, this says that the rule `X ↦ Γ(Xᵃʷⁿ, 𝒪)` is the sheafification of the
structure sheaf on the big h site. -/
@[stacks 0EVU "h topology, the universal property of the sheafification"]
theorem existsUnique_hom_absoluteWeakNormalizationSections
    (G : (BigHOver B S hS)ᵒᵖ ⥤ CommRingCat.{u})
    (hG : Presheaf.IsSheaf (BigHOver.topology B S hS) G)
    (α : (BigHOver.toScheme B S hS).op ⋙ Scheme.Γ ⟶ G) :
    ∃! χ : absoluteWeakNormalizationSectionsOver (BigHOver.toScheme B S hS) ⟶ G,
      absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS) ≫ χ = α :=
  existsUnique_hom_of_isLocallyBijective (BigHOver.topology B S hS) _
    (isLocallyInjective_absoluteWeakNormalizationSectionsMap B S hS)
    (isLocallySurjective_absoluteWeakNormalizationSectionsMap B S hS) hG α

end BigHOver

end AlgebraicGeometry
