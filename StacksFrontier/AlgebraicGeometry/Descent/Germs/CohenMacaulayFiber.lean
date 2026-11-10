module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Permanence
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.RingTheory.Etale.Basic

/-!
# Cohen–Macaulay local rings of fibres are étale local

For a morphism of germs of schemes, the local ring of the fibre at the
distinguished point being Noetherian and Cohen–Macaulay is unchanged by an
étale change of source and target germs.

## Main definitions

* `AlgebraicGeometry.HasCohenMacaulayFiberLocalRing` expresses the property of the
  local ring of the fibre on a morphism of germs.

## Main results

* `AlgebraicGeometry.hasCohenMacaulayFiberLocalRing_isEtaleLocalOnSourceAndTarget`
  states étale locality of this property.
* `AlgebraicGeometry.hasCohenMacaulayFiberLocalRing_ofSchemeHom_iff` evaluates the property
  on the germ morphism induced by a morphism of schemes: it is the same condition on the
  stalk of the fibre at the point.
* `AlgebraicGeometry.hasCohenMacaulayFiberLocalRing_ofSchemeHom_iff_of_isNoetherianRing`: when
  the stalk of the fibre is Noetherian, the property on the induced germ morphism is
  Cohen–Macaulayness of that stalk.
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory
open MorphismOfGerms

universe u

/-- The local ring of the fibre of a morphism of germs at its distinguished
point is Noetherian and Cohen–Macaulay. -/
public abbrev HasCohenMacaulayFiberLocalRing
    {X S : GermOfScheme.{u}} (f : MorphismOfGerms X S) : Prop :=
  ∃ g : MorphismOfGerms.Representative X S,
    MorphismOfGerms.mk g = f ∧
      ∃ h : IsNoetherianRing
          ((g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩)).presheaf.stalk
            (g.hom.asFiber ⟨X.point, g.mem_source⟩)),
        letI := h
        IsCohenMacaulayLocalRing
          ((g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩)).presheaf.stalk
            (g.hom.asFiber ⟨X.point, g.mem_source⟩))

private lemma isNoetherianRing_iff_of_flat_essFiniteType_local
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hflat : f.Flat) (hess : f.EssFiniteType) :
    IsNoetherianRing A ↔ IsNoetherianRing B := by
  let : Algebra A B := f.toAlgebra
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : Algebra.EssFiniteType A B := RingHom.essFiniteType_algebraMap.mp hess
    exact Algebra.EssFiniteType.isNoetherianRing A B
  · have : Module.Flat A B := hflat
    have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (A := B) (isNoetherian_of_linearEquiv
        (Algebra.TensorProduct.rid A B B).symm.toLinearEquiv)

private lemma noetherianCohenMacaulay_iff_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X) :
    (∃ hX : IsNoetherianRing (X.presheaf.stalk x),
      @IsCohenMacaulayLocalRing (X.presheaf.stalk x) _ hX _) ↔
    (∃ hY : IsNoetherianRing (Y.presheaf.stalk (f x)),
      @IsCohenMacaulayLocalRing (Y.presheaf.stalk (f x)) _ hY _) := by
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
  have hqp : q.comap (algebraMap A B) = p :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU)
  let : q.LiesOver p := ⟨hqp.symm⟩
  let : Algebra.Etale A B := hEtale.toAlgebra
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
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
    isNoetherianRing_iff_of_flat_essFiniteType_local
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
      (RingHom.flat_algebraMap_iff.mpr hflat)
      (RingHom.essFiniteType_algebraMap.mpr inferInstance)
  have hEtaleLocalOf : ∀ (_ : IsNoetherianRing (Localization.AtPrime p))
      (_ : IsNoetherianRing (Localization.AtPrime q)),
      RingHom.IsEtaleLocalHom
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := fun _ _ ↦
    ⟨RingHom.flat_algebraMap_iff.mpr hflat,
      RingHom.formallyUnramified_algebraMap.mpr hformallyUnramified,
      RingHom.essFiniteType_algebraMap.mpr inferInstance⟩
  constructor
  · rintro ⟨_, hCMX⟩
    have hNq : IsNoetherianRing (Localization.AtPrime q) :=
      isNoetherianRing_of_ringEquiv _ eX.symm
    have hNp : IsNoetherianRing (Localization.AtPrime p) := hNoethIff.mpr hNq
    have : IsNoetherianRing (Y.presheaf.stalk (f x)) := isNoetherianRing_of_ringEquiv _ eY
    exact ⟨inferInstance, (isCohenMacaulayLocalRing_iff_of_ringEquiv eY).mp
      ((RingHom.isCohenMacaulayLocalRing_iff_of_isEtaleLocalHom
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
        (hEtaleLocalOf hNp hNq)).mpr ((isCohenMacaulayLocalRing_iff_of_ringEquiv eX).mpr hCMX))⟩
  · rintro ⟨_, hCMY⟩
    have hNp : IsNoetherianRing (Localization.AtPrime p) :=
      isNoetherianRing_of_ringEquiv _ eY.symm
    have hNq : IsNoetherianRing (Localization.AtPrime q) := hNoethIff.mp hNp
    have : IsNoetherianRing (X.presheaf.stalk x) := isNoetherianRing_of_ringEquiv _ eX
    exact ⟨inferInstance, (isCohenMacaulayLocalRing_iff_of_ringEquiv eX).mp
      ((RingHom.isCohenMacaulayLocalRing_iff_of_isEtaleLocalHom
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
        (hEtaleLocalOf hNp hNq)).mp ((isCohenMacaulayLocalRing_iff_of_ringEquiv eY).mpr hCMY))⟩

private lemma noetherianCohenMacaulay_fiber_iff_of_etale_square
    {U' U V' V : Scheme.{u}} (a : U' ⟶ U) (b : V' ⟶ V)
    (h' : U' ⟶ V') (h : U ⟶ V) [Etale a] [Etale b]
    (hcomm : a ≫ h = h' ≫ b) (x' : U') :
    (∃ hN : IsNoetherianRing
        ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')),
      @IsCohenMacaulayLocalRing
        ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')) _ hN _) ↔
    (∃ hN : IsNoetherianRing
        ((h.fiber (b (h' x'))).presheaf.stalk
          (fiberMap h' a b h hcomm (h' x') (h'.asFiber x'))),
      @IsCohenMacaulayLocalRing
        ((h.fiber (b (h' x'))).presheaf.stalk
          (fiberMap h' a b h hcomm (h' x') (h'.asFiber x'))) _ hN _) := by
  let f := fiberMap h' a b h hcomm (h' x')
  have : Etale f := etale_fiberMap h' a b h hcomm (h' x')
  simpa [f] using noetherianCohenMacaulay_iff_of_etale f (h'.asFiber x')

/-- A map of fibres compatible with `a` on the underlying schemes sends `asFiber x'` to the
point of the target fibre over `a x'`. -/
private lemma map_asFiber_eq_of_comp_fiberι
    {U' U V' V : Scheme.{u}} (h' : U' ⟶ V') (h : U ⟶ V) (a : U' ⟶ U) (y : V) (x' : U')
    (m : h'.fiber (h' x') ⟶ h.fiber y) (hm : m ≫ h.fiberι y = h'.fiberι (h' x') ≫ a)
    (hx : h (a x') = y) : m (h'.asFiber x') = (h.fiberHomeo y).symm ⟨a x', hx⟩ := by
  apply (h.fiberι y).isEmbedding.injective
  simpa only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber,
    Scheme.Hom.fiberι_fiberHomeo_symm] using
    congrArg (fun k : h'.fiber (h' x') ⟶ U ↦ k (h'.asFiber x')) hm

private lemma noetherianCohenMacaulay_fiber_iff_of_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) :
    (∃ hN : IsNoetherianRing
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)),
      @IsCohenMacaulayLocalRing
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) _ hN _) ↔
    (∃ hN : IsNoetherianRing
        ((f.fiber y).presheaf.stalk
          ((f.fiberHomeo y).symm ⟨x, h⟩)),
      @IsCohenMacaulayLocalRing
        ((f.fiber y).presheaf.stalk
          ((f.fiberHomeo y).symm ⟨x, h⟩)) _ hN _) := by
  let σIso := Scheme.Spec.mapIso (Scheme.residueFieldCongr h.symm).op
  let σ := σIso.hom
  let m : f.fiber (f x) ⟶ f.fiber y :=
    CategoryTheory.Limits.pullback.map f (Y.fromSpecResidueField (f x))
      f (Y.fromSpecResidueField y) (𝟙 X) σ (𝟙 Y) (by simp) (by
        change Y.fromSpecResidueField (f x) =
          Spec.map (Scheme.residueFieldCongr h.symm).hom ≫
            Y.fromSpecResidueField y
        exact (Y.residueFieldCongr_fromSpecResidueField h.symm).symm)
  have hm : IsIso m := by
    dsimp [m, σ, Scheme.Hom.fiber]
    infer_instance
  have hfst : m ≫ f.fiberι y = f.fiberι (f x) := by
    change (CategoryTheory.Limits.pullback.map f (Y.fromSpecResidueField (f x))
      f (Y.fromSpecResidueField y) (𝟙 X) σ (𝟙 Y) _ _ :
        f.fiber (f x) ⟶ f.fiber y) ≫
        CategoryTheory.Limits.pullback.fst f (Y.fromSpecResidueField y) =
      CategoryTheory.Limits.pullback.fst f (Y.fromSpecResidueField (f x))
    simp only [CategoryTheory.Limits.pullback.map, CategoryTheory.Limits.pullback.lift_fst,
      Category.comp_id]
  have hpoint : m (f.asFiber x) = (f.fiberHomeo y).symm ⟨x, h⟩ :=
    map_asFiber_eq_of_comp_fiberι f f (𝟙 X) y x m hfst h
  have hlocal := noetherianCohenMacaulay_iff_of_etale m (f.asFiber x)
  rwa [hpoint] at hlocal

private lemma noetherianCohenMacaulay_fiber_iff_of_etale_square_at
    {U' U V' V : Scheme.{u}} (a : U' ⟶ U) (b : V' ⟶ V)
    (h' : U' ⟶ V') (h : U ⟶ V) [Etale a] [Etale b]
    (hcomm : a ≫ h = h' ≫ b) (x' : U') (x : U) (hx : a x' = x) :
    (∃ hN : IsNoetherianRing
        ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')),
      @IsCohenMacaulayLocalRing
        ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')) _ hN _) ↔
    (∃ hN : IsNoetherianRing
        ((h.fiber (h x)).presheaf.stalk (h.asFiber x)),
      @IsCohenMacaulayLocalRing
        ((h.fiber (h x)).presheaf.stalk (h.asFiber x)) _ hN _) := by
  have hy' : h (a x') = b (h' x') := by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  have hy : h x = b (h' x') := by
    rw [← hx]
    exact hy'
  let y := b (h' x')
  let f := fiberMap h' a b h hcomm (h' x')
  let z := (h.fiberHomeo y).symm ⟨a x', hy'⟩
  have hsecond : V'.fromSpecResidueField (h' x') ≫ b =
      Spec.map (b.residueFieldMap (h' x')) ≫ V.fromSpecResidueField y :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField b (h' x')).symm
  have hfst : f ≫ h.fiberι y = h'.fiberι (h' x') ≫ a := by
    change (CategoryTheory.Limits.pullback.map h'
      (V'.fromSpecResidueField (h' x')) h (V.fromSpecResidueField y)
      a (Spec.map (b.residueFieldMap (h' x'))) b hcomm.symm hsecond :
        h'.fiber (h' x') ⟶ h.fiber y) ≫
        CategoryTheory.Limits.pullback.fst h (V.fromSpecResidueField y) =
      CategoryTheory.Limits.pullback.fst h' (V'.fromSpecResidueField (h' x')) ≫ a
    rw [CategoryTheory.Limits.pullback.map,
      CategoryTheory.Limits.pullback.lift_fst]
  have hz : f (h'.asFiber x') = z := map_asFiber_eq_of_comp_fiberι h' h a y x' f hfst hy'
  have hlocal := noetherianCohenMacaulay_fiber_iff_of_etale_square
    a b h' h hcomm x'
  have hzraw : (fiberMap h' a b h hcomm (h' x')) (h'.asFiber x') = z := by
    simp [f, hz]
  rw [hzraw] at hlocal
  have hlocal' :
      (∃ hN : IsNoetherianRing
          ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')),
        @IsCohenMacaulayLocalRing
          ((h'.fiber (h' x')).presheaf.stalk (h'.asFiber x')) _ hN _) ↔
      (∃ hN : IsNoetherianRing ((h.fiber y).presheaf.stalk z),
        @IsCohenMacaulayLocalRing ((h.fiber y).presheaf.stalk z) _ hN _) := by
    simpa only [y, z] using hlocal
  have hbase := noetherianCohenMacaulay_fiber_iff_of_eq h x y hy
  let zbase := (h.fiberHomeo y).symm ⟨x, hy⟩
  have hbase' :
      (∃ hN : IsNoetherianRing ((h.fiber (h x)).presheaf.stalk (h.asFiber x)),
        @IsCohenMacaulayLocalRing
          ((h.fiber (h x)).presheaf.stalk (h.asFiber x)) _ hN _) ↔
      (∃ hN : IsNoetherianRing ((h.fiber y).presheaf.stalk zbase),
        @IsCohenMacaulayLocalRing ((h.fiber y).presheaf.stalk zbase) _ hN _) := by
    simpa [zbase] using hbase
  have hzbase : z = zbase := by
    apply (h.fiberι y).isEmbedding.injective
    simp [z, zbase, Scheme.Hom.fiberι_fiberHomeo_symm, hx]
  rw [hzbase] at hlocal'
  exact hlocal'.trans hbase'.symm

private def representativeHasCM
    {X S : GermOfScheme.{u}} (g : MorphismOfGerms.Representative X S) : Prop :=
  ∃ hN : IsNoetherianRing
      ((g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩)).presheaf.stalk
        (g.hom.asFiber ⟨X.point, g.mem_source⟩)),
    @IsCohenMacaulayLocalRing
      ((g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩)).presheaf.stalk
        (g.hom.asFiber ⟨X.point, g.mem_source⟩)) _ hN _

private lemma representativeHasCM_iff_restrict
    {X S : GermOfScheme.{u}}
    (g : MorphismOfGerms.Representative X S) (U : X.scheme.Opens)
    (hxU : X.point ∈ U) (hU : U ≤ g.source) :
    representativeHasCM g ↔
    representativeHasCM (MorphismOfGerms.restrictRepresentative g U hxU hU) := by
  let i := X.scheme.homOfLE hU
  let g' := i ≫ g.hom
  let x' : U.toScheme := ⟨X.point, hxU⟩
  have hsq : i ≫ g.hom = g' ≫ 𝟙 S.scheme := by simp [g']
  have hx : i x' = ⟨X.point, g.mem_source⟩ := by
    apply Subtype.ext
    simp [i, x']
  exact (noetherianCohenMacaulay_fiber_iff_of_etale_square_at
    i (𝟙 S.scheme) g' g.hom hsq x' ⟨X.point, g.mem_source⟩ hx).symm

private lemma representativeHasCM_iff_of_agreeNear
    {X S : GermOfScheme.{u}}
    (f g : MorphismOfGerms.Representative X S) (hfg : f.AgreeNear g) :
    representativeHasCM f ↔ representativeHasCM g := by
  obtain ⟨U, hxU, hUf, hUg, hmap⟩ := hfg
  let rf := MorphismOfGerms.restrictRepresentative f U hxU hUf
  let rg := MorphismOfGerms.restrictRepresentative g U hxU hUg
  have heq : rf = rg :=
    MorphismOfGerms.representative_ext_of_source_hom (f := rf) (g := rg) rfl (by
      simpa [rf, rg, MorphismOfGerms.restrictRepresentative] using hmap)
  rw [representativeHasCM_iff_restrict f U hxU hUf,
    representativeHasCM_iff_restrict g U hxU hUg]
  simp [rf, rg, heq]

private lemma hasCohenMacaulayFiberLocalRing_iff_rep
    {X S : GermOfScheme.{u}}
    (f : MorphismOfGerms X S) (g : MorphismOfGerms.Representative X S)
    (hg : MorphismOfGerms.mk g = f) :
    HasCohenMacaulayFiberLocalRing f ↔ representativeHasCM g := by
  constructor
  · rintro ⟨g₀, hg₀, hCM⟩
    have hag : g₀.AgreeNear g :=
      MorphismOfGerms.mk_eq_mk_iff.mp (hg₀.trans hg.symm)
    exact (representativeHasCM_iff_of_agreeNear g₀ g hag).mp
      (by simpa [representativeHasCM] using hCM)
  · intro hCM
    exact ⟨g, hg, by simpa [representativeHasCM] using hCM⟩

private lemma representativeHasCM_iff_comp_precomp
    {X Y Z : GermOfScheme.{u}}
    (f : MorphismOfGerms.Representative X Y)
    (g : MorphismOfGerms.Representative Y Z) (hf : Etale f.hom) :
    representativeHasCM (MorphismOfGerms.compRepresentative f g) ↔
      representativeHasCM g := by
  let c := MorphismOfGerms.compRepresentative f g
  let a := (f.source.ι.isoImage _).inv ≫ f.hom ∣_ g.source
  have hcomm : a ≫ g.hom = c.hom ≫ 𝟙 Z.scheme := by
    simp [a, c, MorphismOfGerms.compRepresentative, Category.assoc]
  have ha : Etale a := by
    dsimp [a, c, MorphismOfGerms.compRepresentative]
    infer_instance
  have hx : a ⟨X.point, c.mem_source⟩ = ⟨Y.point, g.mem_source⟩ := by
    apply Subtype.ext
    change g.source.ι ((f.hom ∣_ g.source)
      ((f.source.ι.isoImage _).inv ⟨X.point, c.mem_source⟩)) = Y.point
    rw [← f.map_point]
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
    change (((f.source.ι.isoImage _).inv ≫
      (f.hom ⁻¹ᵁ g.source).ι ≫ f.hom) ⟨X.point, c.mem_source⟩) = _
    rw [← Category.assoc, Scheme.Opens.isoImage_ι_inv_ι]
    change f.hom (X.scheme.homOfLE _ ⟨X.point, _⟩) =
      f.hom ⟨X.point, f.mem_source⟩
    apply congrArg (fun p : f.source.toScheme ↦ f.hom p)
    apply Subtype.ext
    simp
  exact noetherianCohenMacaulay_fiber_iff_of_etale_square_at
    a (𝟙 Z.scheme) c.hom g.hom hcomm ⟨X.point, c.mem_source⟩ ⟨Y.point, g.mem_source⟩ hx

private lemma representativeHasCM_iff_comp_postcomp
    {X Y Z : GermOfScheme.{u}}
    (f : MorphismOfGerms.Representative X Y)
    (g : MorphismOfGerms.Representative Y Z) (hg : Etale g.hom) :
    representativeHasCM (MorphismOfGerms.compRepresentative f g) ↔
      representativeHasCM f := by
  let c := MorphismOfGerms.compRepresentative f g
  let V := f.hom ⁻¹ᵁ g.source
  have hWf : c.source ≤ f.source := by
    dsimp [c, V, MorphismOfGerms.compRepresentative]
    exact f.source.ι_image_le _
  have hcsource : c.source = f.source.ι ''ᵁ V := by rfl
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
        congrArg (fun k : c.source.toScheme ⟶ f.source.toScheme ↦ k ≫ f.hom) hinc.symm
      _ = (X.scheme.homOfLE hcsource.le ≫ inc) ≫ (V.ι ≫ f.hom) :=
        Category.assoc _ _ _
      _ = (X.scheme.homOfLE hcsource.le ≫ inc) ≫
          ((f.hom ∣_ g.source) ≫ g.source.ι) := by rw [morphismRestrict_ι]
      _ = _ := (Category.assoc _ _ _).symm
  have hcomm₂ : (𝟙 c.source.toScheme) ≫ c.hom = h' ≫ g.hom := by
    simp [c, h', inc, V, MorphismOfGerms.compRepresentative, Category.assoc]
  have hlocal₁ := noetherianCohenMacaulay_fiber_iff_of_etale_square_at
    (𝟙 c.source.toScheme) g.source.ι h' h0 hcomm₁
    ⟨X.point, c.mem_source⟩ ⟨X.point, c.mem_source⟩ rfl
  have hlocal₁' :
      (∃ hN : IsNoetherianRing
          ((h'.fiber (h' ⟨X.point, c.mem_source⟩)).presheaf.stalk
            (h'.asFiber ⟨X.point, c.mem_source⟩)),
        @IsCohenMacaulayLocalRing
          ((h'.fiber (h' ⟨X.point, c.mem_source⟩)).presheaf.stalk
            (h'.asFiber ⟨X.point, c.mem_source⟩)) _ hN _) ↔
      representativeHasCM r := by
    unfold representativeHasCM
    convert hlocal₁ using 1; rfl
  have hlocal₂ := noetherianCohenMacaulay_fiber_iff_of_etale_square_at
    (𝟙 c.source.toScheme) g.hom h' c.hom hcomm₂
    ⟨X.point, c.mem_source⟩ ⟨X.point, c.mem_source⟩ rfl
  have hlocal₂' : representativeHasCM c ↔
      (∃ hN : IsNoetherianRing
          ((h'.fiber (h' ⟨X.point, c.mem_source⟩)).presheaf.stalk
            (h'.asFiber ⟨X.point, c.mem_source⟩)),
        @IsCohenMacaulayLocalRing
          ((h'.fiber (h' ⟨X.point, c.mem_source⟩)).presheaf.stalk
            (h'.asFiber ⟨X.point, c.mem_source⟩)) _ hN _) := by
    unfold representativeHasCM
    exact hlocal₂.symm
  exact (hlocal₂'.trans hlocal₁').trans
    (representativeHasCM_iff_restrict f c.source c.mem_source hWf).symm

/-- Having a Noetherian and Cohen–Macaulay local ring of the fibre is étale local on the source
and target germs. -/
@[stacks 0E0U]
public theorem hasCohenMacaulayFiberLocalRing_isEtaleLocalOnSourceAndTarget :
    MorphismOfGerms.IsEtaleLocalOnSourceAndTarget
      (@HasCohenMacaulayFiberLocalRing.{u}) := by
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
    HasCohenMacaulayFiberLocalRing h ↔ representativeHasCM hr :=
      hasCohenMacaulayFiberLocalRing_iff_rep h hr hhr
    _ ↔ representativeHasCM ca :=
      (representativeHasCM_iff_comp_precomp ar hr haEtale).symm
    _ ↔ HasCohenMacaulayFiberLocalRing (compG a h) :=
      (hasCohenMacaulayFiberLocalRing_iff_rep (compG a h) ca hca).symm
    _ ↔ HasCohenMacaulayFiberLocalRing (compG h' b) := by
      change HasCohenMacaulayFiberLocalRing (MorphismOfGerms.comp a h) ↔
        HasCohenMacaulayFiberLocalRing (MorphismOfGerms.comp h' b)
      rw [← hsq]
    _ ↔ representativeHasCM cb :=
      hasCohenMacaulayFiberLocalRing_iff_rep (compG h' b) cb hcb
    _ ↔ representativeHasCM h'r :=
      representativeHasCM_iff_comp_postcomp h'r br hbEtale
    _ ↔ HasCohenMacaulayFiberLocalRing h' :=
      (hasCohenMacaulayFiberLocalRing_iff_rep h' h'r hh'r).symm

/-- For the germ morphism induced by a morphism of schemes at a point of its source, the
property of the fibre local ring is the corresponding property of the stalk of the fibre
at that point. -/
public theorem hasCohenMacaulayFiberLocalRing_ofSchemeHom_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) :
    HasCohenMacaulayFiberLocalRing (MorphismOfGerms.ofSchemeHom f x) ↔
      ∃ hN : IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)),
        @IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) _ hN _ := by
  let g₀ : MorphismOfGerms.Representative ⟨X, x⟩ ⟨Y, f x⟩ :=
    ⟨⊤, by simp, X.topIso.hom ≫ f, rfl⟩
  have hg₀ : MorphismOfGerms.mk g₀ = MorphismOfGerms.ofSchemeHom f x := rfl
  rw [hasCohenMacaulayFiberLocalRing_iff_rep _ g₀ hg₀]
  have hcomm : X.topIso.hom ≫ f = g₀.hom ≫ 𝟙 Y := by simp [g₀]
  have hx : X.topIso.hom ⟨x, (by simp : x ∈ (⊤ : X.Opens))⟩ = x := by simp
  exact noetherianCohenMacaulay_fiber_iff_of_etale_square_at
    X.topIso.hom (𝟙 Y) g₀.hom f hcomm ⟨x, by simp⟩ x hx

/-- With the stalk of the fibre already known to be Noetherian, the fibre local ring
property of the induced germ morphism is Cohen–Macaulayness of that stalk. -/
public theorem hasCohenMacaulayFiberLocalRing_ofSchemeHom_iff_of_isNoetherianRing
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))] :
    HasCohenMacaulayFiberLocalRing (MorphismOfGerms.ofSchemeHom f x) ↔
      IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  rw [hasCohenMacaulayFiberLocalRing_ofSchemeHom_iff]
  exact ⟨fun ⟨_, hCM⟩ ↦ hCM, fun hCM ↦ ⟨inferInstance, hCM⟩⟩

end AlgebraicGeometry

end
