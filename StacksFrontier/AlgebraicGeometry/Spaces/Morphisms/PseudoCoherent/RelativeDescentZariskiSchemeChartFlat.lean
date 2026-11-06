module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentZariskiSchemeCase

/-!
# Flatness and finite presentation on an affine chart

Let `g : U₀ ⟶ X₀` and `w : V ⟶ Y₀` be étale, with `V` an affine algebraic space, and let
`t : U₀ ⟶ V` satisfy `t ≫ w = g ≫ p₀`. Reading `U₀` and `V` through representing affine schemes,
the square `t ≫ w = g ≫ p₀` is a commuting square of étale charts of `p₀`, so flatness
(Stacks 03ML) and local finite presentation (Stacks 03XP) of `p₀`, which are conditions on every
such square (Stacks 03MJ), hold for the morphism `t'` of affine schemes underlying `t`. With these,
`ZariskiModelHomDescent` holds for the situation restricted along `g` (Stacks 0DKV).

## Main results

* `AlgebraicGeometry.Space.presheaf_etale_iso_comp_of_isEtale`: an étale morphism precomposed
  with an isomorphism from a representable presheaf is an étale chart.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_apply_of_isEtale`: a property holding on
  every étale chart of `f` holds for the scheme morphism underlying any square
  `t ≫ w = g ≫ f` with `g`, `w` étale, read through representing objects.
* `AlgebraicGeometry.Space.RelativeDescentSituation.exists_affineChart_of_etale_factorization`:
  `e₀ ≫ g ≫ p₀` factors as `h_{t'} ≫ w'` through an affine object `V'`, with `w'` étale and `t'`
  flat and locally of finite presentation on underlying schemes.
* `AlgebraicGeometry.Space.RelativeDescentSituation.zariskiModelHomDescent_of_etale_factorization`:
  `ZariskiModelHomDescent R K L` for the situation restricted along `g`, given a square
  `t ≫ w = g ≫ p₀` with `g`, `w` étale, read through affine objects.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An étale morphism of presheaves precomposed with an isomorphism from a representable
presheaf is an étale chart: étale after every representable base change. -/
theorem presheaf_etale_iso_comp_of_isEtale {T : BigFppfOver B S hS}
    {U F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : yoneda.obj T ≅ U) {g : U ⟶ F}
    (hg : IsEtale B S hS g) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (e.hom ≫ g) := by
  have := isMultiplicative_presheaf_etale B S hS
  have he : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf e.hom := by
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda e.hom, fun A D k fst snd hpb => ?_⟩
    have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
    have : IsIso snd := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful snd
    show AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map snd)
    infer_instance
  exact hg T e.hom he

/-- A square `t ≫ w = g ≫ f` read through `t' ≫ eV = e₀ ≫ t` gives `t' ≫ eV ≫ w = e₀ ≫ g ≫ f`. -/
private theorem comp_eq_of_square {C : Type*} [Category C] {Z V' U V F G : C} {e₀ : Z ⟶ U}
    {eV : V' ⟶ V} {g : U ⟶ F} {f : F ⟶ G} {w : V ⟶ G} {t : U ⟶ V} {t' : Z ⟶ V'}
    (ht : t ≫ w = g ≫ f) (ht' : t' ≫ eV = e₀ ≫ t) : t' ≫ eV ≫ w = e₀ ≫ g ≫ f := by
  rw [reassoc_of% ht', ht]

/-- **A property holding on every étale chart of `f`, at a square through étale morphisms.**
If `P` holds on every étale chart of `f : F ⟶ G` (Stacks 03MJ), `g : U ⟶ F` and `w : V ⟶ G` are
étale, `t ≫ w = g ≫ f`, and `t' : Z ⟶ V'` reads `t` through isomorphisms `h_Z ≅ U` and
`h_{V'} ≅ V`, then the scheme morphism underlying `t'` has `P`: the square is itself a square of
étale charts of `f`. -/
theorem holdsOnEveryEtaleChart_apply_of_isEtale {P : MorphismProperty Scheme.{u}}
    {F G U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : HoldsOnEveryEtaleChart B S hS P f) {g : U ⟶ F} (hg : IsEtale B S hS g) {w : V ⟶ G}
    (hw : IsEtale B S hS w) {t : U ⟶ V} (ht : t ≫ w = g ≫ f) {Z V' : BigFppfOver B S hS}
    (e₀ : yoneda.obj Z ≅ U) (eV : yoneda.obj V' ≅ V) (t' : Z ⟶ V')
    (ht' : yoneda.map t' ≫ eV.hom = e₀.hom ≫ t) :
    P ((BigFppfOver.toScheme B S hS).map t') :=
  hf Z V' (e₀.hom ≫ g) (eV.hom ≫ w) t' (presheaf_etale_iso_comp_of_isEtale e₀ hg)
    (presheaf_etale_iso_comp_of_isEtale eV hw)
    ((comp_eq_of_square ht ht').trans (Category.assoc _ _ _).symm)

namespace RelativeDescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : RelativeDescentSituation B S hS hZ I}

/-- Let `g : U₀ ⟶ X₀` be étale, `w : V ⟶ Y₀` étale from an affine algebraic space, and
`t : U₀ ⟶ V` with `t ≫ w = g ≫ p₀`. For any affine object `Z'` of the site with
`e₀ : h_{Z'} ≅ U₀` there are an affine object `V'`, an étale `w' : h_{V'} ⟶ Y₀` and
`t' : Z' ⟶ V'` with `h_{t'} ≫ w' = e₀ ≫ g ≫ p₀` and `t'` flat and locally of finite presentation
on underlying schemes. -/
theorem exists_affineChart_of_etale_factorization {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : U₀ ⟶ D.X₀) (hg : IsEtale B S hS g) {V : AlgebraicSpaces B S hS}
    (w : V ⟶ D.initialTarget) (t : U₀ ⟶ V.1) (hV : IsAffineSpace B S hS V.1)
    (hw : IsEtale B S hS w.hom) (ht : t ≫ w.hom = g ≫ D.p₀) {Z' : BigAffineFppf B S hS}
    (e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅ U₀) :
    ∃ (V' : BigAffineFppf B S hS)
      (w' : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V') ⟶ D.Y.obj (op D.i₀))
      (t' : (BigAffineFppf.inclusion B S hS).obj Z' ⟶ (BigAffineFppf.inclusion B S hS).obj V'),
      yoneda.map t' ≫ w' = e₀.hom ≫ g ≫ D.p₀ ∧ IsEtale B S hS w' ∧
      Flat ((BigFppfOver.toScheme B S hS).map t') ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map t') := by
  obtain ⟨T, hT, ⟨eV⟩⟩ := hV
  let V' : BigAffineFppf B S hS := ⟨T, hT⟩
  let t' : (BigAffineFppf.inclusion B S hS).obj Z' ⟶ (BigAffineFppf.inclusion B S hS).obj V' :=
    yoneda.preimage (e₀.hom ≫ t ≫ eV.hom)
  have ht' : yoneda.map t' ≫ eV.symm.hom = e₀.hom ≫ t := by simp [t']
  refine ⟨V', eV.symm.hom ≫ w.hom, t', ?_, ?_,
    holdsOnEveryEtaleChart_apply_of_isEtale D.initial_isFlat hg hw ht e₀ eV.symm t' ht',
    holdsOnEveryEtaleChart_apply_of_isEtale D.initial_isFinitePresentation.1 hg hw ht e₀ eV.symm
      t' ht'⟩
  · exact comp_eq_of_square ht ht'
  · exact isEtale_of_presheaf_etale B S hS (presheaf_etale_iso_comp_of_isEtale eV.symm hw)

/-! ### Zariski descent of homomorphisms on an affine chart -/

section Consumer

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] isDirected_laterIndex

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : RelativeDescentSituation B S hS hZ I}

/-- Let `g : U₀ ⟶ X₀` and `w : V ⟶ Y₀` be étale and `t : U₀ ⟶ V` with `t ≫ w = g ≫ p₀`; read
`U₀` and `V` through `e₀ : h_{Z'} ≅ U₀` and `e_V : h_{V'} ≅ V` for affine objects `Z'`, `V'` of
the site, and `t` as `t' : Z' ⟶ V'`. For the situation restricted along `g`, any representation
`R` of the base changes along `e₀ ≫ g ≫ p₀`, `K` pseudo-coherent, and `L` with quasi-coherent
cohomology and locally of finite Tor dimension over `t'⁻¹𝒪_{V'}`, `ZariskiModelHomDescent R K L`
holds. -/
theorem zariskiModelHomDescent_of_etale_factorization (hD : D.IsSchemeLimit)
    {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₀ : IsAlgebraicSpace B S hS U₀) (g : U₀ ⟶ D.X₀)
    (hg : IsEtale B S hS g) (hgflat : IsFlat B S hS g) (hgfp : IsFinitePresentation B S hS g)
    {V : AlgebraicSpaces B S hS} (w : V ⟶ D.initialTarget) (t : U₀ ⟶ V.1)
    (hw : IsEtale B S hS w.hom) (ht : t ≫ w.hom = g ≫ D.p₀) {Z' V' : BigAffineFppf B S hS}
    (e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅ U₀)
    (eV : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V') ≅ V.1)
    (t' : (BigAffineFppf.inclusion B S hS).obj Z' ⟶ (BigAffineFppf.inclusion B S hS).obj V')
    (ht' : yoneda.map t' ≫ eV.hom = e₀.hom ≫ t)
    (R : (D.restrict hU₀ g hgflat hgfp).AffineBaseChangeRepresentation Z'
      (e₀.hom ≫ (D.restrict hU₀ g hgflat hgfp).p₀))
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)))
    (hK : AlgebraicGeometry.RingedSpace.IsPseudoCoherent
      (X := ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace) K)
    (hLqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z')).Modules n).obj
        L).IsQuasicoherent)
    (hLtor : AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension
      (AlgebraicGeometry.RingedSpace.inverseImage
        ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj V')).toRingedSpace
        ((BigFppfOver.toScheme B S hS).map t').base)
      (AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction ((BigFppfOver.toScheme B S hS).map t')).obj L)) :
    ZariskiModelHomDescent R K L :=
  zariskiModelHomDescent_of_affineChart (D.isSchemeLimit_restrict hD hU₀ g hgflat hgfp)
    (eV.hom ≫ w.hom) t'
    (comp_eq_of_square ht ht')
    (holdsOnEveryEtaleChart_apply_of_isEtale D.initial_isFlat hg hw ht e₀ eV t' ht')
    (holdsOnEveryEtaleChart_apply_of_isEtale D.initial_isFinitePresentation.1 hg hw ht e₀ eV t' ht')
    R K L hK hLqc hLtor

end Consumer

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
