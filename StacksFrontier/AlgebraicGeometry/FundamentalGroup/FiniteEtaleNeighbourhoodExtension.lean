module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FiniteLocallyFreeAdic
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodCompletion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FormalCoverOfCompletion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FormalCoverAlgebra
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RelativeSpecOfAlgebraQuotient
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleNearClosedFibre
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Finite étale covers of a closed subscheme extend to a neighbourhood

Let `X` be a Noetherian scheme, `Y ⊆ X` a closed subscheme with ideal sheaf `I`, and `𝒱` the open
subschemes of `X` containing `Y`. If the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is
an equivalence of the full subcategories of finite locally free objects, then every finite étale
cover of `Y` is the restriction of a finite étale cover of some `V ∈ 𝒱`.

## Main definitions

* `Stacks.Algebraization.IsNeighbourhoodCompletionFiniteLocallyFree` — membership of an object
  of `Coh(X, I)` in the essential image of the finite locally free objects of
  `colim_𝒱 Coh(𝒪_V)`: it is the completion of a finite locally free coherent module on some open
  neighbourhood of the closed subscheme.

## Main results

* `Stacks.FundamentalGroup.exists_finiteEtale_neighbourhood_extension_of_completion` — the
  essential-image half of [Stacks, Tag 0EK1]: granted that completion is fully faithful
  (condition (4) of [Stacks, Tag 0EK2]) and essentially surjective on finite locally free objects,
  every finite étale cover of `Y` is the restriction of a finite étale cover of some `V ∈ 𝒱`.
* `Stacks.FundamentalGroup.exists_neighbourhood_of_isPullback` — a finite étale cover of an open
  subscheme of `X` through which `Y ⟶ X` factors, restricting to a cover of `Y` by a cartesian
  square, gives a neighbourhood extension in the sense of the restriction functor
  `colim_𝒱 FÉt_V ⟶ FÉt_Y`.

## References

* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0EIL](https://stacks.math.columbia.edu/tag/0EIL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization

/-- **Membership in the essential image of the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)`
on finite locally free objects.** The coherent adic system `F` along `I` is the completion of a
finite locally free coherent module on some open neighbourhood `V` of the closed subscheme cut out
by `I`, compared in `Coh(V, I|_V)` with the termwise restriction of `F` to `V`. -/
public def IsNeighbourhoodCompletionFiniteLocallyFree {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : Stacks.Coherent.CoherentAdicSystems I) : Prop :=
  ∃ V : X.Opens, (I.support : Set X) ⊆ V ∧
    ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf,
      AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree G.obj ∧
      Nonempty (((completionFunctor V.toScheme (I.comap V.ι)).obj G).obj ≅
        (F.obj ⋙ AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι))

end Stacks.Algebraization

namespace Stacks.FundamentalGroup

open Stacks.Algebraization Stacks.Thickenings CategoryTheory.Limits
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

/-- **A finite étale cover of an open subscheme restricting to a given cover of the closed
subscheme gives a neighbourhood extension.** If `j : T ⟶ X` is an open immersion through which the
closed immersion factors as `r ≫ j`, and `P` is a finite étale cover of `T` whose base change along
`r` is the cover `A` of the closed subscheme (as a cartesian square), then the image of `j` is a
neighbourhood over which `A` extends. -/
public theorem exists_neighbourhood_of_isPullback {X : Scheme.{u}} (Y : X.IdealSheafData)
    {T : Scheme.{u}} (j : T ⟶ X) [IsOpenImmersion j] (r : Y.subscheme ⟶ T)
    (hr : r ≫ j = Y.subschemeι) (P : FiniteEtaleOver T) (A : FiniteEtaleOver Y.subscheme)
    (a : A.left ⟶ P.left) (h : IsPullback a A.hom P.hom r) :
    ∃ (W : Neighborhood X Y) (U : FiniteEtaleOver (Neighborhood.open X Y W).toScheme),
      Nonempty ((finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W)).obj U ≅ A) := by
  let E := j.isoOpensRange
  have hP : IsFinite P.hom := P.prop.1
  have hP' : Etale P.hom := P.prop.2
  let U : FiniteEtaleOver j.opensRange.toScheme :=
    MorphismProperty.Over.mk ⊤ (P.hom ≫ E.hom) ⟨inferInstance, inferInstance⟩
  have hrE : (r ≫ E.hom) ≫ j.opensRange.ι = Y.subschemeι := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, hr]
  let W : Neighborhood X Y := OrderDual.toDual ⟨j.opensRange, r ≫ E.hom, hrE⟩
  have hW : Neighborhood.toSchemeHom X Y W = r ≫ E.hom :=
    (cancel_mono j.opensRange.ι).1 ((Neighborhood.toSchemeHom_fac X Y W).trans hrE.symm)
  have hsq : IsPullback (𝟙 P.left) P.hom (P.hom ≫ E.hom) E.hom :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp]⟩
  have H : IsPullback a A.hom U.hom (Neighborhood.toSchemeHom X Y W) := by
    rw [hW]
    have := h.paste_horiz hsq
    rwa [Category.comp_id] at this
  exact ⟨W, U, ⟨(MorphismProperty.Over.isoMk (A := A)
    (B := (finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W)).obj U)
    H.isoPullback H.isoPullback_hom_snd).symm⟩⟩

/-- A cartesian square over `S` restricts to a cartesian square over any open of `S` containing
the image of the base. -/
private theorem exists_isPullback_morphismRestrict {C N P S : Scheme.{u}} {g : C ⟶ P}
    {c : C ⟶ N} {π : P ⟶ S} {z : N ⟶ S} (hpb : IsPullback g c π z) (W : S.Opens)
    (hW : Set.range z.base ⊆ W) :
    ∃ (g' : C ⟶ (π ⁻¹ᵁ W).toScheme) (z' : N ⟶ W.toScheme), g' ≫ (π ⁻¹ᵁ W).ι = g ∧
      z' ≫ W.ι = z ∧ IsPullback g' c (π ∣_ W) z' := by
  have hz : Set.range z.base ⊆ Set.range W.ι.base := by rwa [Scheme.Opens.range_ι]
  have hg : Set.range g.base ⊆ Set.range (π ⁻¹ᵁ W).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change π.base (g.base x) ∈ W
    rw [← Scheme.Hom.comp_apply, hpb.w, Scheme.Hom.comp_apply]
    exact hW ⟨_, rfl⟩
  have hz' := IsOpenImmersion.lift_fac W.ι z hz
  have hg' := IsOpenImmersion.lift_fac (π ⁻¹ᵁ W).ι g hg
  refine ⟨IsOpenImmersion.lift _ g hg, IsOpenImmersion.lift W.ι z hz, hg', hz',
    IsPullback.of_right (h₁₂ := (π ⁻¹ᵁ W).ι) (h₂₂ := W.ι) ?_ ?_
      (isPullback_morphismRestrict π W).flip⟩
  · rwa [hg', hz']
  · apply (cancel_mono W.ι).1
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg', hpb.w, Category.assoc, hz']

/-- The cover `C₀` of the zeroth infinitesimal neighbourhood restricts to `A` by a cartesian
square. -/
private theorem InfinitesimalLift.isPullback_coverZero {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (A : FiniteEtaleOver Z) :
    IsPullback ((InfinitesimalLift.coverZeroIso i A).inv.left ≫
      finiteEtaleBaseChangeProj (nthOrderInclusion i 0) (InfinitesimalLift.cover i A 0)) A.hom
      (InfinitesimalLift.cover i A 0).hom (nthOrderInclusion i 0) := by
  let e₀ := InfinitesimalLift.coverZeroIso i A
  let e' : A.left ≅ pullback (InfinitesimalLift.cover i A 0).hom (nthOrderInclusion i 0) :=
    { hom := e₀.inv.left
      inv := e₀.hom.left
      hom_inv_id := congrArg (fun f => f.left) e₀.inv_hom_id
      inv_hom_id := congrArg (fun f => f.left) e₀.hom_inv_id }
  refine IsPullback.of_iso_pullback ⟨?_⟩ e' rfl ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (e₀.inv.left ≫ ·)
      (finiteEtaleBaseChangeProj_comp_hom _ (InfinitesimalLift.cover i A 0))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ nthOrderInclusion i 0) (MorphismProperty.Over.w e₀.inv))))
  · exact MorphismProperty.Over.w e₀.inv

/-- **A finite locally free scheme over an open, cartesian over a finite étale cover of a
thickening of the closed subscheme, gives a neighbourhood extension.** If `k : S ⟶ X` is an open
immersion, `Y ⟶ X` factors as `j₀ ≫ z ≫ k`, `π` is finite locally free over `S` with base change
along `z` the finite étale `c`, and `c` restricts along `j₀` to `A`, then `A` extends to a
neighbourhood. -/
private theorem exists_neighbourhood_of_isPullback_isFiniteLocallyFree {X : Scheme.{u}}
    (Y : X.IdealSheafData) {S N C P : Scheme.{u}} (k : S ⟶ X) [IsOpenImmersion k]
    (z : N ⟶ S) (j₀ : Y.subscheme ⟶ N) (hj₀ : j₀ ≫ z ≫ k = Y.subschemeι) (π : P ⟶ S)
    [Stacks.Morphisms.IsFiniteLocallyFree π] {g : C ⟶ P} {c : C ⟶ N} [Etale c]
    (hpb : IsPullback g c π z) (A : FiniteEtaleOver Y.subscheme) {a : A.left ⟶ C}
    (ha : IsPullback a A.hom c j₀) :
    ∃ (W : Neighborhood X Y) (U : FiniteEtaleOver (Neighborhood.open X Y W).toScheme),
      Nonempty ((finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W)).obj U ≅ A) := by
  obtain ⟨W, hW, hEt⟩ := exists_etale_morphismRestrict_of_isPullback π hpb
  obtain ⟨g', z', -, hz', hsq⟩ := exists_isPullback_morphismRestrict hpb W hW
  have : IsFinite π :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation π).mp
      inferInstance).1
  let P' : FiniteEtaleOver W.toScheme :=
    MorphismProperty.Over.mk ⊤ (π ∣_ W) ⟨inferInstance, hEt⟩
  refine exists_neighbourhood_of_isPullback Y (W.ι ≫ k) (j₀ ≫ z') ?_ P' A (a ≫ g')
    (ha.paste_horiz hsq)
  simp only [Category.assoc]
  rw [reassoc_of% hz', hj₀]

/-- **Every finite étale cover of the closed subscheme extends to a neighbourhood**, granted that
the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is an equivalence on finite locally free
objects: fully faithful (`hff`, condition (4) of [Stacks, Tag 0EK2]) and essentially surjective
(`hess`). This is the essential-image half of [Stacks, Tag 0EK1]. -/
public theorem exists_finiteEtale_neighbourhood_extension_of_completion {X : Scheme.{u}}
    [IsNoetherian X] (Y : X.IdealSheafData)
    (hff : NeighbourhoodCompletion.CompletionFullyFaithfulComplete Y.subschemeι)
    (hess : ∀ F : Stacks.Coherent.CoherentAdicSystems Y, IsFiniteLocallyFreeAdic Y F →
      IsNeighbourhoodCompletionFiniteLocallyFree Y F)
    (A : FiniteEtaleOver Y.subscheme) :
    ∃ (W : Neighborhood X Y) (U : FiniteEtaleOver (Neighborhood.open X Y W).toScheme),
      Nonempty ((finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W)).obj U ≅ A) := by
  classical
  set i := Y.subschemeι with hi
  have : IsClosedImmersion i := by
    rw [hi]
    infer_instance
  have hY : i.ker = Y := Y.ker_subschemeι
  obtain ⟨V, hVsupp, G, hGflf, ⟨e⟩⟩ := hess (InfinitesimalLift.adicSystemOfKer i A Y hY)
    (InfinitesimalLift.isFiniteLocallyFreeAdic_adicSystemOfKer i A Y hY)
  have hV : Set.range i.base ⊆ V := by rwa [hi, Scheme.IdealSheafData.range_subschemeι]
  have : G.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G.obj).1
  let D := InfinitesimalLift.formalDatumOfCompletion i A V hV Y hY G e
  have hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} G.obj :=
    (Scheme.Modules.isFiniteLocallyFree_iff _).mp hGflf
  obtain ⟨W, hW, d, hunit, hmul⟩ :=
    D.exists_algebraData (fun E F hE hF => hff V hV E F hE hF) hG
  let T := nbhdTower i V hV
  let z := T.homToOpen hW 0
  let c : (InfinitesimalLift.cover i A 0).left ⟶ (T.obj 0).left :=
    (InfinitesimalLift.cover i A 0).hom
  have hz : z ≫ W.ι = InfinitesimalLift.nbhdHom i V hV 0 := T.homToOpen_ι hW 0
  have : IsClosedImmersion (z ≫ W.ι) := hz ▸ InfinitesimalLift.isClosedImmersion_nbhdHom i V hV 0
  have : IsClosedImmersion z := IsClosedImmersion.of_comp z W.ι
  have : IsFinite c := (InfinitesimalLift.cover i A 0).prop.1
  have : Etale c := (InfinitesimalLift.cover i A 0).prop.2
  let Gw := (Scheme.Modules.pullback W.ι).obj G.obj
  let φ' : (Scheme.Modules.pullback z).obj Gw ≅
      (Scheme.Modules.pushforward c).obj (SheafOfModules.unit _) :=
    pullbackObjFactorIso G.obj z hz ≪≫ D.φ 0
  have happ : ∀ (U : W.toScheme.Opens) (s : Γ(Gw, U)), (D.nearMap hW 0).app U s =
      ((Scheme.Modules.pullbackPushforwardAdjunction z).unit.app Gw ≫
        (Scheme.Modules.pushforward z).map φ'.hom).app U s := fun U s => rfl
  have : Gw.IsQuasicoherent := Stacks.Modules.isQuasicoherent_pullback W.ι G.obj inferInstance
  obtain ⟨P, π, hπ, eπ, g, hpb⟩ := @exists_isPullback_of_algebraQuotient _ _ _ z
    inferInstance c inferInstance Gw inferInstance d (D.nearMap hW 0)
    (fun U y => by
      obtain ⟨s, hs⟩ := (unit_comp_pushforward_surjective_ker z Gw _ φ' U).1 y
      exact ⟨s, (happ U.1 s).trans hs⟩)
    (fun U s hs => (unit_comp_pushforward_surjective_ker z Gw _ φ' U).2 s
      ((happ U.1 s).symm.trans hs))
    hunit hmul
  have : Stacks.Morphisms.IsFiniteLocallyFree π :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff π).mpr
      ⟨hπ, @SheafOfModules.IsFiniteLocallyFree.of_iso _ _ _ eπ.symm
        (Stacks.Chow.isFiniteLocallyFree_pullback W.ι G.obj hG)⟩
  refine exists_neighbourhood_of_isPullback_isFiniteLocallyFree Y (W.ι ≫ V.ι) z
    (nthOrderInclusion i 0) ?_ π hpb A (InfinitesimalLift.isPullback_coverZero i A)
  rw [reassoc_of% hz]
  exact (nthOrderInclusion i 0 ≫= InfinitesimalLift.nbhdHom_ι i V hV 0).trans
    (nthOrderInclusion_toBase i 0)

end Stacks.FundamentalGroup

end
