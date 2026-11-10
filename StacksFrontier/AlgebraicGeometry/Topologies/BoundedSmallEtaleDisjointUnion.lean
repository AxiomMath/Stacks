module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.BoundedSmallEtaleStandardCofinal

/-!
# Finite disjoint unions in the size-bounded small étale site

A countable family of objects of the size-bounded small étale site of a scheme `S` has a
coproduct *inside that site*: the coproduct of the underlying schemes is étale over `S`, because
étaleness is local on the source, and it is again below the size cutoff of the ambient big étale
site by `AlgebraicGeometry.Scheme.size_sigmaObj_lt`.  The inclusions are monomorphisms, they
generate a covering sieve of the union, and two distinct members meet only over an object
covered by the empty sieve.

Combined with the cofinality of the standard coverings
(`AlgebraicGeometry.SmallEtale.exists_isSmallEtaleStandardCovering_map_sieve₀_le`) this produces,
for a covering sieve of an object with affine total space, a *single* morphism out of an affine
object through which a standard covering inside the sieve factors.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sigmaObj` and `AlgebraicGeometry.SmallEtale.sigmaι`: the
  disjoint union of a countable family of objects of the site, and the inclusions of its members.

## Main results

* `AlgebraicGeometry.SmallEtale.bot_mem_topology_of_isEmpty_toScheme`: **the empty sieve covers an
  object with empty total space.**
* `AlgebraicGeometry.SmallEtale.sieve₀_sigmaι_mem_topology`: the inclusions of the members
  generate a covering sieve of the disjoint union.
* `AlgebraicGeometry.SmallEtale.bot_mem_topology_of_commSq_sigmaι_of_ne`: two distinct members of
  a disjoint union meet only over an object covered by the empty sieve.
* `AlgebraicGeometry.SmallEtale.exists_affine_sigma_refinement`: **a covering sieve of an object
  with affine total space is refined by a standard covering which factors through a single
  morphism from an affine object of the site, disjointly.**

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The coproduct of the underlying schemes of a countable family of objects of the size-bounded
small étale site is again below the size cutoff. -/
public theorem contains_sigma_toScheme {ι : Type u} (hι : #ι ≤ ℵ₀)
    (V : ι → SmallEtale B S hS) : B.Contains (∐ fun i ↦ (toScheme B S hS).obj (V i)) :=
  Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof hι _
    fun i ↦ (V i).obj.left.property

/-- The morphism to `S` induced on the coproduct of the underlying schemes of a family of
objects of the size-bounded small étale site is étale, étaleness being local on the source. -/
public theorem etale_sigmaDesc_hom {ι : Type u} (V : ι → SmallEtale B S hS) :
    Etale (Sigma.desc fun i ↦ (V i).obj.hom.hom) :=
  have _ : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  IsZariskiLocalAtSource.sigmaDesc fun i ↦ (V i).property

/-- **The disjoint union of a countable family of objects of the size-bounded small étale site**,
as an object of that site. -/
@[implicit_reducible]
public noncomputable def sigmaObj {ι : Type u} (hι : #ι ≤ ℵ₀) (V : ι → SmallEtale B S hS) :
    SmallEtale B S hS :=
  objOfEtale B S hS (contains_sigma_toScheme B S hS hι V)
    (Sigma.desc fun i ↦ (V i).obj.hom.hom) (etale_sigmaDesc_hom B S hS V)

/-- The inclusion of a member of `AlgebraicGeometry.SmallEtale.sigmaObj`. -/
@[implicit_reducible]
public noncomputable def sigmaι {ι : Type u} (hι : #ι ≤ ℵ₀) (V : ι → SmallEtale B S hS)
    (i : ι) : V i ⟶ sigmaObj B S hS hι V :=
  homMk B S hS (X := V i) (Y := sigmaObj B S hS hι V)
    (Sigma.ι (fun i ↦ (toScheme B S hS).obj (V i)) i) (Sigma.ι_comp_desc _ _)

/-- On underlying schemes, the inclusion of a member of a disjoint union is the coproduct
injection. -/
public theorem toScheme_map_sigmaι {ι : Type u} (hι : #ι ≤ ℵ₀) (V : ι → SmallEtale B S hS)
    (i : ι) : (toScheme B S hS).map (sigmaι B S hS hι V i) =
      Sigma.ι (fun i ↦ (toScheme B S hS).obj (V i)) i := rfl

/-- The total space of a disjoint union of finitely many objects with affine total space is
affine. -/
public theorem isAffine_sigmaObj {ι : Type u} [Finite ι] (hι : #ι ≤ ℵ₀)
    (V : ι → SmallEtale B S hS)
    (hV : ∀ i, _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj (V i))) :
    _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj (sigmaObj B S hS hι V)) :=
  have _ := hV
  inferInstanceAs (_root_.AlgebraicGeometry.IsAffine (∐ fun i ↦ (toScheme B S hS).obj (V i)))

/-- The inclusions of the members of a disjoint union generate a covering sieve of it. -/
public theorem sieve₀_sigmaι_mem_topology {ι : Type u} (hι : #ι ≤ ℵ₀)
    (V : ι → SmallEtale B S hS) :
    Sieve.ofArrows V (sigmaι B S hS hι V) ∈ topology B S hS (sigmaObj B S hS hι V) :=
  generate_ofArrows_mem_topology_of_jointlySurjective B S hS V (sigmaι B S hS hι V) fun x ↦
    ⟨(sigmaOpenCover fun i ↦ (toScheme B S hS).obj (V i)).idx x,
      (sigmaOpenCover fun i ↦ (toScheme B S hS).obj (V i)).covers x⟩

/-- An inclusion of a member of a disjoint union is a monomorphism. -/
public instance mono_sigmaι {ι : Type u} (hι : #ι ≤ ℵ₀) (V : ι → SmallEtale B S hS) (i : ι) :
    Mono (sigmaι B S hS hι V i) := by
  have : _root_.AlgebraicGeometry.IsOpenImmersion
      ((toScheme B S hS).map (sigmaι B S hS hι V i)) :=
    (sigmaOpenCover fun i ↦ (toScheme B S hS).obj (V i)).map_prop i
  exact (toScheme B S hS).mono_of_mono_map inferInstance

/-- **The empty sieve covers an object of the size-bounded small étale site whose total space is
empty.** -/
public theorem bot_mem_topology_of_isEmpty_toScheme (Z : SmallEtale B S hS)
    (hZ : IsEmpty ((toScheme B S hS).obj Z)) : (⊥ : Sieve Z) ∈ topology B S hS Z :=
  mem_topology_of_jointlySurjective fun x ↦ (hZ.false x).elim

/-- **Two distinct members of a disjoint union meet only over an object covered by the empty
sieve.**  If an object of the site maps into two distinct members compatibly with the
inclusions, the empty sieve covers it. -/
public theorem bot_mem_topology_of_commSq_sigmaι_of_ne {ι : Type u} (hι : #ι ≤ ℵ₀)
    (V : ι → SmallEtale B S hS) {Z : SmallEtale B S hS} {i j : ι} (gi : Z ⟶ V i)
    (gj : Z ⟶ V j) (hij : i ≠ j)
    (hcomm : gi ≫ sigmaι B S hS hι V i = gj ≫ sigmaι B S hS hι V j) :
    (⊥ : Sieve Z) ∈ topology B S hS Z := by
  refine bot_mem_topology_of_isEmpty_toScheme B S hS Z
    (isEmpty_of_commSq_sigmaι_of_ne (g := fun i ↦ (toScheme B S hS).obj (V i))
      (a := (toScheme B S hS).map gi) (b := (toScheme B S hS).map gj) ⟨?_⟩ hij)
  simpa only [Functor.map_comp, toScheme_map_sigmaι] using congrArg (toScheme B S hS).map hcomm

/-- **A covering sieve of an object with affine total space is refined by a standard covering
whose members sit disjointly inside a single affine object of the site.**  There are a standard
covering `𝒱` of `T` by arrows of `R` and a morphism `h : W ⟶ T` from an object with affine total
space through which every member of `𝒱` factors by a monomorphism `a i`; the `a i` generate a
covering sieve of `W`, and two distinct members meet only over objects covered by the empty
sieve. -/
public theorem exists_affine_sigma_refinement (T : SmallEtale B S hS)
    (hT : _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T)) {R : Sieve T}
    (hR : R ∈ topology B S hS T) :
    ∃ (𝒱 : PreZeroHypercover.{u} T) (W : SmallEtale B S hS) (h : W ⟶ T)
      (a : ∀ i, 𝒱.X i ⟶ W),
      IsSmallEtaleStandardCovering S (𝒱.map (toEtaleSite B S hS)) ∧
      (∀ i, R (𝒱.f i)) ∧
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj W) ∧
      (∀ i, a i ≫ h = 𝒱.f i) ∧
      Sieve.ofArrows 𝒱.X a ∈ topology B S hS W ∧
      (∀ i, Mono (a i)) ∧
      ∀ ⦃Z : SmallEtale B S hS⦄ ⦃i j : 𝒱.I₀⦄ (gi : Z ⟶ 𝒱.X i) (gj : Z ⟶ 𝒱.X j), i ≠ j →
        gi ≫ a i = gj ≫ a j → (⊥ : Sieve Z) ∈ topology B S hS Z := by
  obtain ⟨𝒱, h𝒱, hle⟩ :=
    exists_isSmallEtaleStandardCovering_map_sieve₀_le B S hS T hT hR
  have hfin : Finite 𝒱.I₀ := IsSmallEtaleStandardCovering.finite S h𝒱
  have hcard : #𝒱.I₀ ≤ ℵ₀ := mk_le_aleph0
  have hVaff : ∀ i, _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj (𝒱.X i)) :=
    (IsSmallEtaleStandardCovering.isAffine S h𝒱).2
  have hdesc : (Sigma.desc fun i ↦ (toScheme B S hS).map (𝒱.f i)) ≫ T.obj.hom.hom =
      (sigmaObj B S hS hcard 𝒱.X).obj.hom.hom := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [← Category.assoc, Sigma.ι_comp_desc]
    change _ = Sigma.ι _ i ≫ Sigma.desc fun i ↦ (𝒱.X i).obj.hom.hom
    rw [Sigma.ι_comp_desc]
    exact congrArg (fun k ↦ k.hom)
      (CategoryTheory.Over.w ((inclusion B S hS).map (𝒱.f i)))
  refine ⟨𝒱, sigmaObj B S hS hcard 𝒱.X,
    homMk B S hS (X := sigmaObj B S hS hcard 𝒱.X) (Y := T)
      (Sigma.desc fun i ↦ (toScheme B S hS).map (𝒱.f i)) hdesc,
    sigmaι B S hS hcard 𝒱.X, h𝒱,
    fun i ↦ hle (𝒱.f i) (𝒱.sieve₀_f i),
    isAffine_sigmaObj B S hS hcard 𝒱.X hVaff, fun i ↦ ?_,
    sieve₀_sigmaι_mem_topology B S hS hcard 𝒱.X, fun i ↦ inferInstance,
    fun Z i j gi gj hij hcomm ↦
      bot_mem_topology_of_commSq_sigmaι_of_ne B S hS hcard 𝒱.X gi gj hij hcomm⟩
  apply ObjectProperty.hom_ext
  apply CategoryTheory.Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact Sigma.ι_comp_desc _ _

end AlgebraicGeometry.SmallEtale

end
