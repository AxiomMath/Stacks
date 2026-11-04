module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.GorensteinPermanence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport
public import StacksFrontier.RingTheory.Etale.PermanenceOfProperties

/-!
# Gorenstein local rings of fibres are étale local on source and target

For a morphism of germs of schemes, the local ring of the fibre at the
distinguished point being Noetherian and Gorenstein is unchanged by an
étale change of source and target germs.

## Main definitions

* `AlgebraicGeometry.HasGorensteinFiberLocalRing` expresses the property of the
  local ring of the fibre on a morphism of germs.

## Main results

* `AlgebraicGeometry.hasGorensteinFiberLocalRing_isEtaleLocalOnSourceAndTarget`
  states étale locality on the source and target of this property.
* `AlgebraicGeometry.hasGorensteinFiberLocalRing_ofSchemeHom_iff` evaluates the property
  on the germ morphism induced by a morphism of schemes: it is the same condition on the
  stalk of the fibre at the point.

## Implementation notes

A representative of the germ morphism provides a morphism of schemes near
the distinguished point. Its fibre has the canonical point
`AlgebraicGeometry.Scheme.Hom.asFiber`. The existential representative makes the condition
independent of a chosen representative. Noetherianity is included in the predicate, rather
than assumed of all fibres; it also supplies the instance needed to state
Gorensteinness.

A commutative square of germs with étale vertical arrows is reduced to a single étale
morphism of fibres, and the comparison of fibre local rings along an étale morphism of
schemes is ring-theoretic. The two inputs there are
`RingHom.isGorensteinLocalRing_iff_of_isEtaleLocalHom`, which transports Gorensteinness
across an étale local homomorphism, and
`Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff`, which transports it across a ring
isomorphism; Noetherianity is transported by
`isNoetherianRing_localization_iff_of_etale`. The stalks of the two schemes are compared
through the localizations of the rings of sections on affine opens witnessing étaleness at
the point.

## References

* [Stacks Project, Tag 0E13](https://stacks.math.columbia.edu/tag/0E13)
* [Stacks Project, Tag 04NB](https://stacks.math.columbia.edu/tag/04NB)
* [Stacks Project, Tag 04NI](https://stacks.math.columbia.edu/tag/04NI)
* [Stacks Project, Tag 0AGZ](https://stacks.math.columbia.edu/tag/0AGZ)
* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory
open MorphismOfGerms

universe u

/-- The local ring of the fibre of a morphism of germs at its distinguished
point is Noetherian and Gorenstein. -/
public abbrev HasGorensteinFiberLocalRing
    {X S : GermOfScheme.{u}} (f : MorphismOfGerms X S) : Prop :=
  ∃ g : MorphismOfGerms.Representative X S,
    MorphismOfGerms.mk g = f ∧
      ∃ h : IsNoetherianRing
          ((g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩)).presheaf.stalk
            (g.hom.asFiber ⟨X.point, g.mem_source⟩)),
        letI := h
        Dualizing.IsGorensteinLocalRing
          ((g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩)).presheaf.stalk
            (g.hom.asFiber ⟨X.point, g.mem_source⟩))

/-- Being Noetherian and Gorenstein local transfers along a ring isomorphism. -/
private lemma noetherianGorenstein_iff_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    (∃ hN : IsNoetherianRing R, @Dualizing.IsGorensteinLocalRing R _ hN _) ↔
    (∃ hN : IsNoetherianRing S, @Dualizing.IsGorensteinLocalRing S _ hN _) := by
  refine ⟨fun ⟨hR, hG⟩ => ?_, fun ⟨hS, hG⟩ => ?_⟩
  · let hS := isNoetherianRing_of_ringEquiv _ e
    exact ⟨hS, (Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff e).mp hG⟩
  · let hR := isNoetherianRing_of_ringEquiv _ e.symm
    exact ⟨hR, (Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff e).mpr hG⟩

/-- Along an étale morphism of schemes, the stalk at a point of the source is Noetherian and
Gorenstein if and only if the stalk at its image is. -/
public lemma noetherianGorenstein_iff_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X) :
    (∃ hX : IsNoetherianRing (X.presheaf.stalk x),
      @Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) _ hX _) ↔
    (∃ hY : IsNoetherianRing (Y.presheaf.stalk (f x)),
      @Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk (f x)) _ hY _) := by
  obtain ⟨U, hU, hxU, V, hV, hUV, hEtale⟩ :=
    (etale_iff_forall_etaleAt f).mp inferInstance x
  let A := Γ(Y, V)
  let B := Γ(X, U)
  let p := (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal
  let q := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : p.IsPrime := (hV.primeIdealOf ⟨f x, hUV hxU⟩).isPrime
  let : q.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  let φ := (f.appLE V U hUV).hom
  let : Algebra A B := φ.toAlgebra
  have hqp : q.comap (algebraMap A B) = p := by
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU)
  let : q.LiesOver p := ⟨hqp.symm⟩
  let : Algebra.Etale A B := hEtale.toAlgebra
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
  let : Algebra A (Localization.AtPrime q) := inferInstance
  let : Algebra B (Localization.AtPrime q) := inferInstance
  let : IsScalarTower A B (Localization.AtPrime q) := inferInstance
  let : IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q) := inferInstance
  let : Algebra.IsEtaleAt A q := inferInstance
  let : Algebra.FormallyEtale A (Localization.AtPrime q) := inferInstance
  let : Algebra.FormallyUnramified A (Localization.AtPrime q) := inferInstance
  let : Algebra.EssFiniteType A (Localization.AtPrime q) := inferInstance
  let : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp A (Localization.AtPrime p) (Localization.AtPrime q)
  have hflat : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
      (Localization.AtPrime q)).2 inferInstance
  have hformallyUnramified :
      Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.localization_base p.primeCompl
  let : Algebra (Γ(Y, V)) (Y.presheaf.stalk (f x)) :=
    Y.presheaf.algebra_section_stalk ⟨f x, hUV hxU⟩
  let : Algebra (Γ(X, U)) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) p :=
    hV.isLocalization_stalk ⟨f x, hUV hxU⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  let eY : Localization.AtPrime p ≃+* Y.presheaf.stalk (f x) :=
    IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (Y.presheaf.stalk (f x))
  let eX : Localization.AtPrime q ≃+* X.presheaf.stalk x :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
      (X.presheaf.stalk x)
  have hNoethIff : IsNoetherianRing (Localization.AtPrime p) ↔
      IsNoetherianRing (Localization.AtPrime q) :=
    isNoetherianRing_localization_iff_of_etale p q
  have hEtaleLocalOf : ∀ (_ : IsNoetherianRing (Localization.AtPrime p))
      (_ : IsNoetherianRing (Localization.AtPrime q)),
      RingHom.IsEtaleLocalHom
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    intro _ _
    refine ⟨RingHom.flat_algebraMap_iff.mpr hflat, ?_,
      RingHom.essFiniteType_algebraMap.mpr inferInstance⟩
    exact RingHom.formallyUnramified_algebraMap.mpr hformallyUnramified
  have hmid : (∃ hq : IsNoetherianRing (Localization.AtPrime q),
        @Dualizing.IsGorensteinLocalRing (Localization.AtPrime q) _ hq _) ↔
      (∃ hp : IsNoetherianRing (Localization.AtPrime p),
        @Dualizing.IsGorensteinLocalRing (Localization.AtPrime p) _ hp _) := by
    refine ⟨fun ⟨hq, hGq⟩ => ?_, fun ⟨hp, hGp⟩ => ?_⟩
    · let hp := hNoethIff.mpr hq
      exact ⟨hp, (RingHom.isGorensteinLocalRing_iff_of_isEtaleLocalHom
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
        (hEtaleLocalOf hp hq)).mpr hGq⟩
    · let hq := hNoethIff.mp hp
      exact ⟨hq, (RingHom.isGorensteinLocalRing_iff_of_isEtaleLocalHom
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
        (hEtaleLocalOf hp hq)).mp hGp⟩
  exact ((noetherianGorenstein_iff_of_ringEquiv eX.symm).trans hmid).trans
    (noetherianGorenstein_iff_of_ringEquiv eY)

private lemma noetherianGorenstein_fiber_iff_of_etale_square
    {U' U V' V : Scheme.{u}} (a : U' ⟶ U) (b : V' ⟶ V)
    (h' : U' ⟶ V') (h : U ⟶ V) [Etale a] [Etale b]
    (hcomm : a ≫ h = h' ≫ b) (x' : U') :
    (∃ hN : IsNoetherianRing
        ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')),
      @Dualizing.IsGorensteinLocalRing
        ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')) _ hN _) ↔
    (∃ hN : IsNoetherianRing
        ((h.fiber (b (h' x'))).presheaf.stalk
          (fiberMap h' a b h hcomm (h' x') (h'.asFiber x'))),
      @Dualizing.IsGorensteinLocalRing
        ((h.fiber (b (h' x'))).presheaf.stalk
          (fiberMap h' a b h hcomm (h' x') (h'.asFiber x'))) _ hN _) := by
  have := etale_fiberMap h' a b h hcomm (h' x')
  exact noetherianGorenstein_iff_of_etale (fiberMap h' a b h hcomm (h' x')) (h'.asFiber x')

private lemma noetherianGorenstein_fiber_iff_of_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) :
    (∃ hN : IsNoetherianRing
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)),
      @Dualizing.IsGorensteinLocalRing
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) _ hN _) ↔
    (∃ hN : IsNoetherianRing
        ((f.fiber y).presheaf.stalk
          ((f.fiberHomeo y).symm ⟨x, h⟩)),
      @Dualizing.IsGorensteinLocalRing
        ((f.fiber y).presheaf.stalk
          ((f.fiberHomeo y).symm ⟨x, h⟩)) _ hN _) := by
  let σIso := Scheme.Spec.mapIso (Scheme.residueFieldCongr h.symm).op
  let σ := σIso.hom
  let m : f.fiber (f x) ⟶ f.fiber y :=
    CategoryTheory.Limits.pullback.map f (Y.fromSpecResidueField (f x))
      f (Y.fromSpecResidueField y) (𝟙 X) σ (𝟙 Y) (by simp) (by
        show Y.fromSpecResidueField (f x) =
          Spec.map (Scheme.residueFieldCongr h.symm).hom ≫
            Y.fromSpecResidueField y
        exact (Y.residueFieldCongr_fromSpecResidueField h.symm).symm)
  have hm : IsIso m := by
    dsimp [m, σ, Scheme.Hom.fiber]
    infer_instance
  have hfst : m ≫ f.fiberι y = f.fiberι (f x) := by
    show (CategoryTheory.Limits.pullback.map f (Y.fromSpecResidueField (f x))
      f (Y.fromSpecResidueField y) (𝟙 X) σ (𝟙 Y) _ _ :
        f.fiber (f x) ⟶ f.fiber y) ≫
        CategoryTheory.Limits.pullback.fst f (Y.fromSpecResidueField y) =
      CategoryTheory.Limits.pullback.fst f (Y.fromSpecResidueField (f x))
    simp only [CategoryTheory.Limits.pullback.map, CategoryTheory.Limits.pullback.lift_fst,
      Category.comp_id]
  have hpoint : m (f.asFiber x) = (f.fiberHomeo y).symm ⟨x, h⟩ := by
    apply (f.fiberι y).isEmbedding.injective
    have hp := congrArg (fun k : f.fiber (f x) ⟶ X => k (f.asFiber x)) hfst
    simpa only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber,
      Scheme.Hom.fiberι_fiberHomeo_symm] using hp
  have hlocal := noetherianGorenstein_iff_of_etale m (f.asFiber x)
  rwa [hpoint] at hlocal

/-- The morphism of fibres in a commutative square sends the canonical point of the fibre
of `h'` at `x'` to the point of the fibre of `h` given by `a x'`. -/
private lemma fiberMap_asFiber
    {U' U V' V : Scheme.{u}} (a : U' ⟶ U) (b : V' ⟶ V)
    (h' : U' ⟶ V') (h : U ⟶ V) (hcomm : a ≫ h = h' ≫ b) (x' : U')
    (hy : h (a x') = b (h' x')) :
    fiberMap h' a b h hcomm (h' x') (h'.asFiber x') =
      (h.fiberHomeo (b (h' x'))).symm ⟨a x', hy⟩ := by
  let y := b (h' x')
  let f := fiberMap h' a b h hcomm (h' x')
  have hsecond : V'.fromSpecResidueField (h' x') ≫ b =
      Spec.map (b.residueFieldMap (h' x')) ≫ V.fromSpecResidueField y :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField b (h' x')).symm
  have hfst : f ≫ h.fiberι y = h'.fiberι (h' x') ≫ a := by
    show (CategoryTheory.Limits.pullback.map h'
      (V'.fromSpecResidueField (h' x')) h (V.fromSpecResidueField y)
      a (Spec.map (b.residueFieldMap (h' x'))) b hcomm.symm hsecond :
        h'.fiber (h' x') ⟶ h.fiber y) ≫
        CategoryTheory.Limits.pullback.fst h (V.fromSpecResidueField y) =
      CategoryTheory.Limits.pullback.fst h' (V'.fromSpecResidueField (h' x')) ≫ a
    rw [CategoryTheory.Limits.pullback.map,
      CategoryTheory.Limits.pullback.lift_fst]
  apply (h.fiberι y).isEmbedding.injective
  calc
    (h.fiberι y) (f (h'.asFiber x')) =
        (f ≫ h.fiberι y) (h'.asFiber x') :=
          (Scheme.Hom.comp_apply _ _ _).symm
    _ = (h'.fiberι (h' x') ≫ a) (h'.asFiber x') :=
          congrArg (fun k : h'.fiber (h' x') ⟶ U => k (h'.asFiber x')) hfst
    _ = a x' := by simp [Scheme.Hom.fiberι_asFiber]
    _ = (h.fiberι y) ((h.fiberHomeo y).symm ⟨a x', hy⟩) := by
          rw [Scheme.Hom.fiberι_fiberHomeo_symm]

private lemma noetherianGorenstein_fiber_iff_of_etale_square_at
    {U' U V' V : Scheme.{u}} (a : U' ⟶ U) (b : V' ⟶ V)
    (h' : U' ⟶ V') (h : U ⟶ V) [Etale a] [Etale b]
    (hcomm : a ≫ h = h' ≫ b) (x' : U') (x : U) (hx : a x' = x) :
    (∃ hN : IsNoetherianRing
        ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')),
      @Dualizing.IsGorensteinLocalRing
        ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')) _ hN _) ↔
    (∃ hN : IsNoetherianRing
        ((h.fiber (h x)).presheaf.stalk (h.asFiber x)),
      @Dualizing.IsGorensteinLocalRing
        ((h.fiber (h x)).presheaf.stalk (h.asFiber x)) _ hN _) := by
  have hy' : h (a x') = b (h' x') := by
    calc
      h (a x') = (a ≫ h) x' := (Scheme.Hom.comp_apply a h x').symm
      _ = (h' ≫ b) x' := by rw [hcomm]
      _ = b (h' x') := Scheme.Hom.comp_apply h' b x'
  have hy : h x = b (h' x') := by rwa [← hx]
  let y := b (h' x')
  let z := (h.fiberHomeo y).symm ⟨a x', hy'⟩
  have hlocal := noetherianGorenstein_fiber_iff_of_etale_square a b h' h hcomm x'
  rw [fiberMap_asFiber a b h' h hcomm x' hy'] at hlocal
  have hlocal' :
      (∃ hN : IsNoetherianRing
          ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')),
        @Dualizing.IsGorensteinLocalRing
          ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')) _ hN _) ↔
      (∃ hN : IsNoetherianRing ((h.fiber y).presheaf.stalk z),
        @Dualizing.IsGorensteinLocalRing ((h.fiber y).presheaf.stalk z) _ hN _) := by
    simpa only [y, z] using hlocal
  have hbase := noetherianGorenstein_fiber_iff_of_eq h x y hy
  let zbase := (h.fiberHomeo y).symm ⟨x, hy⟩
  have hbase' :
      (∃ hN : IsNoetherianRing ((h.fiber (h x)).presheaf.stalk (h.asFiber x)),
        @Dualizing.IsGorensteinLocalRing
          ((h.fiber (h x)).presheaf.stalk (h.asFiber x)) _ hN _) ↔
      (∃ hN : IsNoetherianRing ((h.fiber y).presheaf.stalk zbase),
        @Dualizing.IsGorensteinLocalRing ((h.fiber y).presheaf.stalk zbase) _ hN _) := by
    simpa [zbase] using hbase
  have hzbase : z = zbase := by
    apply (h.fiberι y).isEmbedding.injective
    simp [z, zbase, Scheme.Hom.fiberι_fiberHomeo_symm, hx]
  rw [hzbase] at hlocal'
  exact hlocal'.trans hbase'.symm

private def representativeHasGorenstein
    {X S : GermOfScheme.{u}} (g : MorphismOfGerms.Representative X S) : Prop :=
  ∃ hN : IsNoetherianRing
      ((g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩)).presheaf.stalk
        (g.hom.asFiber ⟨X.point, g.mem_source⟩)),
    @Dualizing.IsGorensteinLocalRing
      ((g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩)).presheaf.stalk
        (g.hom.asFiber ⟨X.point, g.mem_source⟩)) _ hN _

private lemma representativeHasGorenstein_iff_restrict
    {X S : GermOfScheme.{u}}
    (g : MorphismOfGerms.Representative X S) (U : X.scheme.Opens)
    (hxU : X.point ∈ U) (hU : U ≤ g.source) :
    representativeHasGorenstein g ↔
    representativeHasGorenstein (MorphismOfGerms.restrictRepresentative g U hxU hU) := by
  let i := X.scheme.homOfLE hU
  let g' := i ≫ g.hom
  let x' : U.toScheme := ⟨X.point, hxU⟩
  have hsq : i ≫ g.hom = g' ≫ 𝟙 S.scheme := by simp [g']
  have hx : i x' = ⟨X.point, g.mem_source⟩ := by
    apply Subtype.ext
    simp [i, x']
  exact (noetherianGorenstein_fiber_iff_of_etale_square_at
    i (𝟙 S.scheme) g' g.hom hsq x' ⟨X.point, g.mem_source⟩ hx).symm

private lemma representativeHasGorenstein_iff_of_agreeNear
    {X S : GermOfScheme.{u}}
    (f g : MorphismOfGerms.Representative X S) (hfg : f.AgreeNear g) :
    representativeHasGorenstein f ↔ representativeHasGorenstein g := by
  obtain ⟨U, hxU, hUf, hUg, hmap⟩ := hfg
  let rf := MorphismOfGerms.restrictRepresentative f U hxU hUf
  let rg := MorphismOfGerms.restrictRepresentative g U hxU hUg
  have heq : rf = rg := MorphismOfGerms.representative_ext_of_source_hom
    (f := rf) (g := rg) rfl (by
      simpa [rf, rg, MorphismOfGerms.restrictRepresentative] using hmap)
  rw [representativeHasGorenstein_iff_restrict f U hxU hUf,
    representativeHasGorenstein_iff_restrict g U hxU hUg]
  simp [rf, rg, heq]

private lemma hasGorensteinFiberLocalRing_iff_rep
    {X S : GermOfScheme.{u}}
    (f : MorphismOfGerms X S) (g : MorphismOfGerms.Representative X S)
    (hg : MorphismOfGerms.mk g = f) :
    HasGorensteinFiberLocalRing f ↔ representativeHasGorenstein g := by
  constructor
  · rintro ⟨g₀, hg₀, hGor⟩
    have hag : g₀.AgreeNear g :=
      MorphismOfGerms.mk_eq_mk_iff.mp (hg₀.trans hg.symm)
    exact (representativeHasGorenstein_iff_of_agreeNear g₀ g hag).mp
      (by simpa [representativeHasGorenstein] using hGor)
  · intro hGor
    exact ⟨g, hg, by simpa [representativeHasGorenstein] using hGor⟩

private lemma representativeHasGorenstein_iff_comp_precomp
    {X Y Z : GermOfScheme.{u}}
    (f : MorphismOfGerms.Representative X Y)
    (g : MorphismOfGerms.Representative Y Z) (hf : Etale f.hom) :
    representativeHasGorenstein (MorphismOfGerms.compRepresentative f g) ↔
      representativeHasGorenstein g := by
  let c := MorphismOfGerms.compRepresentative f g
  let a := (f.source.ι.isoImage _).inv ≫ f.hom ∣_ g.source
  have hcomm : a ≫ g.hom = c.hom ≫ 𝟙 Z.scheme := by
    simp [a, c, MorphismOfGerms.compRepresentative, Category.assoc]
  have ha : Etale a := by
    let : Etale f.hom := hf
    dsimp [a, c, MorphismOfGerms.compRepresentative]
    infer_instance
  have hx : a ⟨X.point, c.mem_source⟩ = ⟨Y.point, g.mem_source⟩ := by
    apply Subtype.ext
    show g.source.ι ((f.hom ∣_ g.source)
      ((f.source.ι.isoImage _).inv ⟨X.point, c.mem_source⟩)) = Y.point
    rw [← f.map_point, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
    show (((f.source.ι.isoImage _).inv ≫
      (f.hom ⁻¹ᵁ g.source).ι ≫ f.hom) ⟨X.point, c.mem_source⟩) = _
    rw [← Category.assoc, Scheme.Opens.isoImage_ι_inv_ι]
    show f.hom (X.scheme.homOfLE _ ⟨X.point, _⟩) =
      f.hom ⟨X.point, f.mem_source⟩
    apply congrArg (fun p : f.source.toScheme ↦ f.hom p)
    apply Subtype.ext
    simp
  have hlocal := noetherianGorenstein_fiber_iff_of_etale_square_at
    a (𝟙 Z.scheme) c.hom g.hom hcomm ⟨X.point, c.mem_source⟩
      ⟨Y.point, g.mem_source⟩ hx
  show representativeHasGorenstein c ↔ representativeHasGorenstein g
  unfold representativeHasGorenstein
  exact hlocal

private lemma representativeHasGorenstein_iff_comp_postcomp
    {X Y Z : GermOfScheme.{u}}
    (f : MorphismOfGerms.Representative X Y)
    (g : MorphismOfGerms.Representative Y Z) (hg : Etale g.hom) :
    representativeHasGorenstein (MorphismOfGerms.compRepresentative f g) ↔
      representativeHasGorenstein f := by
  let c := MorphismOfGerms.compRepresentative f g
  let V := f.hom ⁻¹ᵁ g.source
  have hWf : c.source ≤ f.source := by
    dsimp [c, V, MorphismOfGerms.compRepresentative]
    exact f.source.ι_image_le _
  have hcsource : c.source = f.source.ι ''ᵁ V := rfl
  let inc := (f.source.ι.isoImage V).inv
  let h' := X.scheme.homOfLE hcsource.le ≫ inc ≫ f.hom ∣_ g.source
  let h0 := X.scheme.homOfLE hWf ≫ f.hom
  let r := MorphismOfGerms.restrictRepresentative f c.source c.mem_source hWf
  have hinc :
      (X.scheme.homOfLE hcsource.le ≫ inc) ≫ V.ι = X.scheme.homOfLE hWf := by
    rw [Category.assoc, Scheme.Opens.isoImage_ι_inv_ι, Scheme.homOfLE_homOfLE]
  have hcomm₁ : (𝟙 c.source.toScheme) ≫ h0 = h' ≫ g.source.ι := by
    rw [Category.id_comp]
    dsimp [h0, h']
    calc
      _ = ((X.scheme.homOfLE hcsource.le ≫ inc) ≫ V.ι) ≫ f.hom :=
        congrArg (fun k : c.source.toScheme ⟶ f.source.toScheme => k ≫ f.hom) hinc.symm
      _ = (X.scheme.homOfLE hcsource.le ≫ inc) ≫ (V.ι ≫ f.hom) :=
        Category.assoc _ _ _
      _ = (X.scheme.homOfLE hcsource.le ≫ inc) ≫
          ((f.hom ∣_ g.source) ≫ g.source.ι) := by rw [morphismRestrict_ι]
      _ = _ := (Category.assoc _ _ _).symm
  have hcomm₂ : (𝟙 c.source.toScheme) ≫ c.hom = h' ≫ g.hom := by
    simp [c, h', inc, V, MorphismOfGerms.compRepresentative, Category.assoc]
  have hlocal₁ := noetherianGorenstein_fiber_iff_of_etale_square_at
    (𝟙 c.source.toScheme) g.source.ι h' h0 hcomm₁
    ⟨X.point, c.mem_source⟩ ⟨X.point, c.mem_source⟩ rfl
  have hlocal₁' :
      (∃ hN : IsNoetherianRing
          ((h'.fiber (h' ⟨X.point, c.mem_source⟩)).presheaf.stalk
            (h'.asFiber ⟨X.point, c.mem_source⟩)),
        @Dualizing.IsGorensteinLocalRing
          ((h'.fiber (h' ⟨X.point, c.mem_source⟩)).presheaf.stalk
            (h'.asFiber ⟨X.point, c.mem_source⟩)) _ hN _) ↔
      representativeHasGorenstein r := by
    unfold representativeHasGorenstein
    convert hlocal₁ using 1
    rfl
  have hlocal₂' : representativeHasGorenstein c ↔ _ :=
    (noetherianGorenstein_fiber_iff_of_etale_square_at (𝟙 c.source.toScheme) g.hom h' c.hom
      hcomm₂ ⟨X.point, c.mem_source⟩ ⟨X.point, c.mem_source⟩ rfl).symm
  exact (hlocal₂'.trans hlocal₁').trans
    (representativeHasGorenstein_iff_restrict f c.source c.mem_source hWf).symm

/-- **Stacks Project, Tag 0E13.** Having a Noetherian and Gorenstein
local ring of the fibre is étale local on the source and target germs. -/
@[stacks 0E13]
public theorem hasGorensteinFiberLocalRing_isEtaleLocalOnSourceAndTarget :
    MorphismOfGerms.IsEtaleLocalOnSourceAndTarget
      (@HasGorensteinFiberLocalRing.{u}) := by
  refine ⟨?_⟩
  intro U' U V' V a b h' h ha hb hsq
  obtain ⟨ar, har, haEtale⟩ := ha
  obtain ⟨br, hbr, hbEtale⟩ := hb
  obtain ⟨h'r, hh'r⟩ := MorphismOfGerms.exists_rep h'
  obtain ⟨hr, hhr⟩ := MorphismOfGerms.exists_rep h
  let ca := MorphismOfGerms.compRepresentative ar hr
  let cb := MorphismOfGerms.compRepresentative h'r br
  let compG {A B C : GermOfScheme} :=
    MorphismOfGerms.comp (X := A) (Y := B) (Z := C)
  have hca : MorphismOfGerms.mk ca = compG a h := by
    simpa [ca, compG, har, hhr] using (MorphismOfGerms.comp_mk ar hr).symm
  have hcb : MorphismOfGerms.mk cb = compG h' b := by
    simpa [cb, compG, hh'r, hbr] using (MorphismOfGerms.comp_mk h'r br).symm
  calc
    HasGorensteinFiberLocalRing h ↔ representativeHasGorenstein hr :=
      hasGorensteinFiberLocalRing_iff_rep h hr hhr
    _ ↔ representativeHasGorenstein ca :=
      (representativeHasGorenstein_iff_comp_precomp ar hr haEtale).symm
    _ ↔ HasGorensteinFiberLocalRing (compG a h) :=
      (hasGorensteinFiberLocalRing_iff_rep (compG a h) ca hca).symm
    _ ↔ HasGorensteinFiberLocalRing (compG h' b) := by
      show HasGorensteinFiberLocalRing (MorphismOfGerms.comp a h) ↔
        HasGorensteinFiberLocalRing (MorphismOfGerms.comp h' b)
      rw [← hsq]
    _ ↔ representativeHasGorenstein cb :=
      hasGorensteinFiberLocalRing_iff_rep (compG h' b) cb hcb
    _ ↔ representativeHasGorenstein h'r :=
      representativeHasGorenstein_iff_comp_postcomp h'r br hbEtale
    _ ↔ HasGorensteinFiberLocalRing h' :=
      (hasGorensteinFiberLocalRing_iff_rep h' h'r hh'r).symm

/-- For the germ morphism induced by a morphism of schemes at a point of its source, the
property of the fibre local ring is the corresponding property of the stalk of the fibre
at that point. -/
public theorem hasGorensteinFiberLocalRing_ofSchemeHom_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) :
    HasGorensteinFiberLocalRing (MorphismOfGerms.ofSchemeHom f x) ↔
      ∃ hN : IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)),
        @Dualizing.IsGorensteinLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) _ hN _ := by
  let g₀ : MorphismOfGerms.Representative ⟨X, x⟩ ⟨Y, f x⟩ :=
    ⟨⊤, by simp, X.topIso.hom ≫ f, rfl⟩
  have hg₀ : MorphismOfGerms.mk g₀ = MorphismOfGerms.ofSchemeHom f x := rfl
  rw [hasGorensteinFiberLocalRing_iff_rep _ g₀ hg₀]
  have hcomm : X.topIso.hom ≫ f = g₀.hom ≫ 𝟙 Y := by simp [g₀]
  have hx : X.topIso.hom ⟨x, (by simp : x ∈ (⊤ : X.Opens))⟩ = x := by simp
  exact noetherianGorenstein_fiber_iff_of_etale_square_at
    X.topIso.hom (𝟙 Y) g₀.hom f hcomm ⟨x, by simp⟩ x hx

/-- With the stalk of the fibre already known to be Noetherian, the fibre local ring
property of the induced germ morphism is Gorensteinness of that stalk. -/
public theorem hasGorensteinFiberLocalRing_ofSchemeHom_iff_of_isNoetherianRing
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))] :
    HasGorensteinFiberLocalRing (MorphismOfGerms.ofSchemeHom f x) ↔
      Dualizing.IsGorensteinLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
  (hasGorensteinFiberLocalRing_ofSchemeHom_iff f x).trans
    ⟨fun ⟨_, hGor⟩ => hGor, fun hGor => ⟨inferInstance, hGor⟩⟩

end AlgebraicGeometry

end
