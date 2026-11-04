module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinOpenness
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinLimits
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinTowerExistence
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackTowerExistence
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatAlgebraizationExists

/-!
# Openness of versality for the Quot functor (Stacks 0CZW, axiom [5])

* `AlgebraicGeometry.Space.QuotSituation.exists_quotient_of_tower`: compatible towers of quotients
  over the levels of a square-zero tower of affine schemes come from one quotient over the limit;
* `AlgebraicGeometry.Space.isSquareZeroEffective_quotOverBase`: hence square-zero towers are
  effective for `Quot_{F/X/S}`;
* `AlgebraicGeometry.Space.isOpenVersality_quotOverBase`: **Stacks 0CZW, axiom [5]**, from
  Stacks 0CXU.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS) (ι : ∀ T : BigFppfOver B S hS,
    (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
  [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]

include ι in
/-- **Towers of quotients over square-zero towers of affine schemes are effective.** -/
theorem exists_quotient_of_tower (hsep : IsSeparated B S hS D.f.hom)
    (hF : D.F.IsFinitePresentationOnSite)
    {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ} {cR : Cone R} (hcR : IsLimit cR)
    (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
    (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), (RingHom.ker (R.map f).hom.toRingHom) ^ 2 = ⊥)
    {T : ℕ ⥤ BigFppfOver B S hS} {c : Cocone T}
    {e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (T.obj n) ≅ Spec (.of (R.obj (.op n)))}
    {eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt)}
    (he : ∀ {i j : ℕ} (f : i ⟶ j),
      (BigFppfOver.toScheme B S hS).map (T.map f) ≫ (e j).hom =
        (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
    (heL : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
      (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)
    (K : ∀ n, D.properlySupportedQuotients (D.testOver ι (T.obj n)))
    (hK : ∀ n, D.quotientPullback (D.testHom ι (T.map (homOfLE (n.le_add_right 1))))
      (K (n + 1)).1 = (K n).1) :
    ∃ K' : D.properlySupportedQuotients (D.testOver ι c.pt),
      ∀ n, D.quotientPullback (D.testHom ι (c.ι.app n)) K'.1 = (K n).1 := by
  obtain ⟨G, hq, hfp, hfl, hps, ψ, hψ⟩ :=
    D.exists_tower_algebraization ι hsep hcR hsurj hsq he heL K hK
  obtain ⟨K', hK'⟩ := D.exists_quotient_of_tower_of_algebraization ι hcR c he heL hF
    (surjective_toScheme_map_ι_zero hcR c heL hsurj hsq) K hK G hq hfp hfl hps ψ hψ
  exact ⟨K', hK'⟩

end QuotSituation

section OverBase

variable (X : AlgebraicSpaces B S hS) (f : X ⟶ schemeSpace (BigFppfOver.terminalObj B S hS))
  (hf : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
  (hF : F.IsQuasicoherentOnSite)

/-- **Towers of square-zero thickenings are effective for `𝒮_{Quot_{F/X/S}}`**, for `f` separated
and `F` of finite presentation. -/
theorem isSquareZeroEffective_quotOverBase (hsep : IsSeparated B S hS f.hom)
    (hFfp : F.IsFinitePresentationOnSite) :
    Deformation.Artin.IsSquareZeroEffective B S hS
      (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).val.p
      (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).isFiberedInGroupoids := by
  let D := quotOverBase X f hf F hF
  let M := D.quotSitePresheafModel
  let ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y :=
    fun T => ObjectProperty.homMk (yoneda.map (Over.homMk T.hom (by simp)))
  refine isSquareZeroEffective_fibredCategory
    fun Λ _ chart _ R cR hcR hsurj hsq T c e eLimit he heL _ t ht => ?_
  choose K hK using fun n => M.exists_ofQuot ι (t n)
  obtain ⟨K', hK'⟩ := D.exists_quotient_of_tower ι hsep hFfp hcR hsurj hsq he heL K
    (fun n => (M.map_eq_iff ι _ _ _ _ _ (hK (n + 1)) (hK n)).1 (ht n))
  obtain ⟨τ, hτ⟩ := M.exists_of_ofQuot ι K'
  exact ⟨τ, fun n => (M.map_eq_iff ι _ _ _ _ _ hτ (hK n)).2 (hK' n)⟩

/-- **Openness of versality for `Quot_{F/X/S}` from limit preservation**, by Stacks 0CXU: the
representable diagonal, (RS*), limit preservation and effectivity of square-zero towers. -/
theorem isOpenVersality_quotOverBase_of_limitPreserving [AlgebraicGeometry.IsLocallyNoetherian S]
    (hsep : IsSeparated B S hS f.hom) (hFfp : F.IsFinitePresentationOnSite)
    (hlimit : AlgebraicGeometry.LimitPreserving.{u, u, u, u} (BigFppfOver.toScheme B S hS)
      (quotOverBasePresheaf X f hf F hF)) :
    ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).val.obj)
        (hy : ((Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).val.p ⋙
          Over.post B.inclusion).obj y = U)
        (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U ((Stack.fibredCategory B S hS
          (quotOverBasePresheaf X f hf F hF)).val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' ∈ V.1, AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U ((Stack.fibredCategory B S hS
              (quotOverBasePresheaf X f hf F hF)).val.p ⋙ Over.post B.inclusion) u' y hy :=
  fun U hU y hy u hu hv =>
    Deformation.Artin.isOpenVersality_of_isSquareZeroEffective B S hS
      (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF))
      (Stack.hasRepresentableDiagonal_fibredCategory B S hS
        (isRepresentableByAlgebraicSpaces_diag_quotOverBase X f hf F hF))
      (satisfiesRSStar_quotOverBase X f hf F hF)
      (Stack.isLimitPreserving_fibredCategory B S hS hlimit)
      (isSquareZeroEffective_quotOverBase X f hf F hF hsep hFfp) U hU y hy u hu hv

/-- **Stacks 0CZW, axiom [5]: openness of versality for `Quot_{F/X/S}`.** For `S` locally
Noetherian, `f` separated and `F` of finite presentation, a finite type point of a scheme locally
of finite type over `S` at which an object of `Quot_{F/X/S}` is versal has an open neighbourhood
of finite type points at which it is versal. This is Stacks 0CXU: the diagonal is representable,
(RS*) holds, `Quot_{F/X/S}` is limit preserving (axiom [1]), and towers of square-zero thickenings
of affine schemes are effective, by Grothendieck existence for such towers (Stacks 0CXB),
representability of `Hom` sheaves (Stacks 08K6) and Nakayama. -/
@[stacks 0CZW "axiom [5]: openness of versality for Quot_{F/X/S}"]
theorem isOpenVersality_quotOverBase [AlgebraicGeometry.IsLocallyNoetherian S]
    (hsep : IsSeparated B S hS f.hom) (hFfp : F.IsFinitePresentationOnSite) :
    ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).val.obj)
        (hy : ((Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).val.p ⋙
          Over.post B.inclusion).obj y = U)
        (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U ((Stack.fibredCategory B S hS
          (quotOverBasePresheaf X f hf F hF)).val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' ∈ V.1, AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U ((Stack.fibredCategory B S hS
              (quotOverBasePresheaf X f hf F hF)).val.p ⋙ Over.post B.inclusion) u' y hy :=
  isOpenVersality_quotOverBase_of_limitPreserving X f hf F hF hsep hFfp
    (limitPreserving_quotOverBase X f hf F hF hFfp)

end OverBase

end AlgebraicGeometry.Space
