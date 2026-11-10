module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.Topology.NoetherianSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Noetherian.Retrocompact
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Germ
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian

/-!
# Extension of finite étale covers across a pure complement

*Purity* holds for a local ring `R` when every finite étale cover of its punctured spectrum is
the restriction of a finite étale cover of `Spec R`.  If `j : U ⟶ X` is an open immersion of
Noetherian schemes and purity holds for `𝒪_{X, x}` at every point `x` outside the image of `j`,
then every finite étale cover of `U` extends to one of `X`.

## Main definitions

* `AlgebraicGeometry.HasPurity`: purity for a local ring.

## Main results

* `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_hasPurity`: [Stacks, Tag 0EY7], the
  restriction functor `FÉt_X ⟶ FÉt_U` is essentially surjective.

## Implementation notes

Noetherian induction is run as maximality of the set of opens to which the given cover extends.
At a maximal open `W ≠ ⊤` one picks the generic point `x` of a maximal irreducible closed subset
of the complement; then the preimage of `W` in `Spec 𝒪_{X, x}` is exactly the punctured spectrum,
so purity extends the cover over `Spec 𝒪_{X, x}`.  The cover over `W` and the cover over
`Spec 𝒪_{X, x}` form a gluing datum in the sense of
`AlgebraicGeometry.GlueingNearPoint.glueingDataNearPoint`, whose preimage under the equivalence of
[Stacks, Tag 0BQ5] is a scheme of finite presentation over a neighbourhood of `W ∪ {x}`; it is
finite and étale over a smaller such neighbourhood by [Stacks, Tag 0EY3].  That contradicts
maximality of `W`.

## References

* [Stacks Project, Lemma 58.21.6 (0EY7)](https://stacks.math.columbia.edu/tag/0EY7)
* [Stacks Project, Lemma 32.14.3 (0BQ5)](https://stacks.math.columbia.edu/tag/0BQ5)
* [Stacks Project, Lemma 32.20.4 (0EY3)](https://stacks.math.columbia.edu/tag/0EY3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-! ### Finite étale covers as schemes of finite presentation -/

private def finitePresentationFunctorOfFiniteEtale {T : Scheme.{u}} [IsLocallyNoetherian T] :
    FiniteEtaleOver T ⥤ FinitePresentationOver T :=
  ObjectProperty.lift
    (show ObjectProperty (Over T) from fun X ↦ FinitePresentation X.hom)
    (MorphismProperty.Over.forget finiteEtale ⊤ T)
    (fun V ↦ finitePresentation_of_finiteEtale V)

private def finitePresentationBaseChangeFiniteEtaleCompat
    {S T : Scheme.{u}} [IsLocallyNoetherian S] [IsLocallyNoetherian T] (f : T ⟶ S) :
    finiteEtaleBaseChange f ⋙ finitePresentationFunctorOfFiniteEtale (T := T) ≅
      finitePresentationFunctorOfFiniteEtale (T := S) ⋙ finitePresentationBaseChange f := by
  let P : ObjectProperty (Over T) := fun X ↦ FinitePresentation X.hom
  let e := MorphismProperty.Over.pullbackCompForgetIso (P := finiteEtale) (Q := ⊤) (f := f)
  exact NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk P (e.app A))
    fun g ↦ P.ι.map_injective (e.hom.naturality g)

/-! ### Transport along isomorphisms of covers -/

/-- Base change along `f` followed by base change along `g` is the identity when `f ≫ g = 𝟙`. -/
private def finiteEtaleBaseChangeObjIsoSelf {S T : Scheme.{u}} {f : S ⟶ T} {g : T ⟶ S}
    (h : f ≫ g = 𝟙 S) (E : FiniteEtaleOver S) :
    (finiteEtaleBaseChange f).obj ((finiteEtaleBaseChange g).obj E) ≅ E :=
  ((finiteEtaleBaseChangeComp f g (𝟙 S) h.symm).app E).symm ≪≫ finiteEtaleBaseChangeId.app E

/-- A property of morphisms stable under base change is invariant under isomorphisms in `Over T`. -/
private lemma prop_iff_overIso {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {T : Scheme.{u}} {A B : Over T} (e : A ≅ B) : P A.hom ↔ P B.hom :=
  have := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := P)
  MorphismProperty.arrow_mk_iso_iff P
    (Arrow.isoMk ((Over.forget T).mapIso e) (Iso.refl T) (by cat_disch))

/-- Pulling back along `h = f ≫ g` is pulling back along `g`, then along `f`. -/
private def overPullbackIsoOfComp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (w : f ≫ g = h) (A : Over Z) :
    (Over.pullback h).obj A ≅ (Over.pullback f).obj ((Over.pullback g).obj A) := by
  subst w
  exact (Over.pullbackComp f g).app A

/-- If `P` holds for the pullback of `A` to a larger open, it holds for the pullback to a
smaller one. -/
private lemma prop_pullback_ι_of_le {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} {V W : S.Opens} (hVW : V ≤ W) {A : Over S}
    (h : P ((Over.pullback W.ι).obj A).hom) : P ((Over.pullback V.ι).obj A).hom := by
  refine (prop_iff_overIso (overPullbackIsoOfComp (f := S.homOfLE hVW) (g := W.ι) (by simp)
    A)).mpr ?_
  exact MorphismProperty.pullback_snd _ _ h

/-! ### The punctured spectrum at a generic point of the complement -/

private lemma stalkPullback_eq_puncturedSpectrum_of_genericPoint
    {S : Scheme.{u}} (U : S.Opens) (x : S) (C : Set S)
    (hCsub : C ⊆ (U : Set S)ᶜ)
    (hCmax : ∀ D : Set S, IsIrreducible D → D ⊆ (U : Set S)ᶜ → C ⊆ D → D = C)
    (hgen : IsGenericPoint x C) :
    (S.fromSpecStalk x) ⁻¹ᵁ U = Stacks.puncturedSpectrum (S.presheaf.stalk x) := by
  ext y
  refine ⟨fun hy hclosed ↦ ?_, fun hy ↦ ?_⟩
  · subst y
    have hxU : x ∈ U := by
      change S.fromSpecStalk x (IsLocalRing.closedPoint (S.presheaf.stalk x)) ∈ U at hy
      simpa only [Scheme.fromSpecStalk_closedPoint] using hy
    exact (hCsub hgen.mem hxU).elim
  · by_contra hyU
    have hspec : S.fromSpecStalk x y ⤳ x := by
      have hmem : S.fromSpecStalk x y ∈ Set.range (S.fromSpecStalk x) := ⟨y, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at hmem
    have hCsubClosure : C ⊆ closure ({S.fromSpecStalk x y} : Set S) := by
      rw [← hgen.def]
      exact closure_minimal
        (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hspec)) isClosed_closure
    have hEq : closure ({S.fromSpecStalk x y} : Set S) = C :=
      hCmax _ isIrreducible_singleton.closure
        (closure_minimal (Set.singleton_subset_iff.mpr hyU) (isClosed_compl_iff.mpr U.2))
        hCsubClosure
    have hygen : IsGenericPoint (S.fromSpecStalk x y) C := by
      rw [isGenericPoint_def, hEq]
    exact hy ((S.fromSpecStalk x).isEmbedding.injective (by
      simpa only [Scheme.fromSpecStalk_closedPoint] using (hgen.eq hygen).symm))

private lemma exists_genericPoint_maximal_irreducible_subset
    {S : Scheme.{u}} [IsNoetherian S] (Z : Set S) (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ (C : Set S) (x : S), IsIrreducible C ∧ IsClosed C ∧ C ⊆ Z ∧
      (∀ D : Set S, IsIrreducible D → D ⊆ Z → C ⊆ D → D = C) ∧ IsGenericPoint x C := by
  classical
  obtain ⟨F, hFfin, hFclosed, hFirred, hFZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible (α := S) hZ
  have hFne : F.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    have hz' : z ∈ ⋃₀ F := by simpa [hFZ] using hz
    rcases Set.mem_sUnion.mp hz' with ⟨C, hCF, _⟩
    exact ⟨C, hCF⟩
  obtain ⟨C, hCF, hCmax⟩ := hFfin.exists_maximal hFne
  have hCsub : C ⊆ Z := by
    rw [hFZ]
    exact Set.subset_sUnion_of_mem hCF
  have hCmax' : ∀ D : Set S, IsIrreducible D → D ⊆ Z → C ⊆ D → D = C := by
    intro D hDir hDZ hCD
    obtain ⟨E, hEF, hDE⟩ := isIrreducible_iff_sUnion_isClosed.mp hDir hFfin.toFinset
      (fun E hE ↦ hFclosed E (hFfin.mem_toFinset.mp hE))
      (by simpa [hFZ, hFfin.coe_toFinset] using hDZ)
    have hCE : C ⊆ E := hCD.trans hDE
    have hEC : E = C := Set.Subset.antisymm (hCmax (hFfin.mem_toFinset.mp hEF) hCE) hCE
    exact Set.Subset.antisymm (hEC ▸ hDE) hCD
  exact ⟨C, (hFirred C hCF).genericPoint, hFirred C hCF, hFclosed C hCF, hCsub, hCmax',
    (hFirred C hCF).isGenericPoint_genericPoint (hFclosed C hCF)⟩

/-! ### Purity -/

/-- Purity for a local ring: every finite étale cover of its punctured spectrum is, up to
isomorphism, the restriction of a finite étale cover of its spectrum. -/
abbrev HasPurity (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  (finiteEtaleBaseChange (Stacks.puncturedSpectrum R).ι).EssSurj

private lemma purity_extends_cover_on_stalkOpen
    {S : Scheme.{u}} (U : S.Opens) (x : S)
    (hOpen : (S.fromSpecStalk x) ⁻¹ᵁ U = Stacks.puncturedSpectrum (S.presheaf.stalk x))
    (hPurity : HasPurity (S.presheaf.stalk x))
    (E : FiniteEtaleOver ((S.fromSpecStalk x) ⁻¹ᵁ U).toScheme) :
    ∃ F : FiniteEtaleOver (Spec (S.presheaf.stalk x)),
      Nonempty ((finiteEtaleBaseChange (((S.fromSpecStalk x) ⁻¹ᵁ U).ι)).obj F ≅ E) := by
  let A := Stacks.puncturedSpectrum (S.presheaf.stalk x)
  let B := (S.fromSpecStalk x) ⁻¹ᵁ U
  let R := Spec (S.presheaf.stalk x)
  let e : A.toScheme ≅ B.toScheme := R.isoOfEq hOpen.symm
  let bc {Y Z : Scheme.{u}} (f : Y ⟶ Z) := finiteEtaleBaseChange f
  obtain ⟨F, ⟨i⟩⟩ := hPurity.mem_essImage ((bc e.hom).obj E)
  let leftIso : (bc B.ι).obj F ≅ (bc e.inv).obj ((bc A.ι).obj F) :=
    (finiteEtaleBaseChangeComp e.inv A.ι B.ι (Scheme.isoOfEq_inv_ι R hOpen.symm).symm).app F
  exact ⟨F, ⟨leftIso ≪≫ (bc e.inv).mapIso i ≪≫ finiteEtaleBaseChangeObjIsoSelf e.inv_hom_id E⟩⟩

/-! ### Gluing a cover over an open to a cover over the local scheme -/

private def isoCommaMk {A B C : Type (u + 1)} [Category.{u} A] [Category.{u} B] [Category.{u} C]
    {F : A ⥤ C} {G : B ⥤ C} (a : A) (b : B) (i : F.obj a ≅ G.obj b) : IsoComma F G :=
  ⟨⟨a, b, i.hom⟩, inferInstanceAs (IsIso i.hom)⟩

/-- The cover `E` over `U` together with an extension over `Spec 𝒪_{S, x}` of its restriction
to the preimage of `U` forms a glueing datum near `x`, in the sense of
`AlgebraicGeometry.GlueingNearPoint.glueingDataNearPoint`. -/
private lemma finiteEtale_glueingDataNearPoint_of_extends
    {S : Scheme.{u}} (U : S.Opens) (x : S)
    [IsLocallyNoetherian U.toScheme] [IsLocallyNoetherian (Spec (S.presheaf.stalk x))]
    [IsLocallyNoetherian (((S.fromSpecStalk x) ⁻¹ᵁ U).toScheme)]
    (E : FiniteEtaleOver U.toScheme)
    (hE : ∃ L : FiniteEtaleOver (Spec (S.presheaf.stalk x)),
      Nonempty ((finiteEtaleBaseChange (((S.fromSpecStalk x) ⁻¹ᵁ U).ι)).obj L ≅
        (finiteEtaleBaseChange ((S.fromSpecStalk x) ∣_ U)).obj E)) :
    ∃ (L : FiniteEtaleOver (Spec (S.presheaf.stalk x)))
      (D : GlueingNearPoint.glueingDataNearPoint S U x),
      (GlueingNearPoint.openComponent S U x).obj D =
        (show ObjectProperty (Over U.toScheme) from fun X ↦ FinitePresentation X.hom).ι.obj
          ((finitePresentationFunctorOfFiniteEtale (T := U.toScheme)).obj E) ∧
      (GlueingNearPoint.localComponent S U x).obj D =
        (show ObjectProperty (Over (Spec (S.presheaf.stalk x))) from
          fun X ↦ FinitePresentation X.hom).ι.obj
          ((finitePresentationFunctorOfFiniteEtale
            (T := Spec (S.presheaf.stalk x))).obj L) := by
  obtain ⟨L, ⟨i⟩⟩ := hE
  let fpU := finitePresentationFunctorOfFiniteEtale (T := U.toScheme)
  let fpR := finitePresentationFunctorOfFiniteEtale (T := Spec (S.presheaf.stalk x))
  let fpP := finitePresentationFunctorOfFiniteEtale
    (T := ((S.fromSpecStalk x) ⁻¹ᵁ U).toScheme)
  let overlap :=
    ((finitePresentationBaseChangeFiniteEtaleCompat ((S.fromSpecStalk x) ∣_ U)).app E).symm ≪≫
    (fpP.mapIso i).symm ≪≫
    (finitePresentationBaseChangeFiniteEtaleCompat (((S.fromSpecStalk x) ⁻¹ᵁ U).ι)).app L
  exact ⟨L, isoCommaMk (fpU.obj E) (fpR.obj L) (by
    simpa [GlueingNearPoint.restrictOpenToPuncturedLocal,
      GlueingNearPoint.restrictLocalToPuncturedLocal, fpU, fpR] using overlap), rfl, rfl⟩

private lemma finiteEtale_glueingDataNearPoint_of_purity
    {S : Scheme.{u}} (U : S.Opens) (x : S)
    (hOpen : (S.fromSpecStalk x) ⁻¹ᵁ U = Stacks.puncturedSpectrum (S.presheaf.stalk x))
    (hPurity : HasPurity (S.presheaf.stalk x))
    [IsLocallyNoetherian U.toScheme] [IsLocallyNoetherian (Spec (S.presheaf.stalk x))]
    [IsLocallyNoetherian (((S.fromSpecStalk x) ⁻¹ᵁ U).toScheme)]
    (E : FiniteEtaleOver U.toScheme) :
    ∃ (L : FiniteEtaleOver (Spec (S.presheaf.stalk x)))
      (D : GlueingNearPoint.glueingDataNearPoint S U x),
      (GlueingNearPoint.openComponent S U x).obj D =
        (show ObjectProperty (Over U.toScheme) from fun X ↦ FinitePresentation X.hom).ι.obj
          ((finitePresentationFunctorOfFiniteEtale (T := U.toScheme)).obj E) ∧
      (GlueingNearPoint.localComponent S U x).obj D =
        (show ObjectProperty (Over (Spec (S.presheaf.stalk x))) from
          fun X ↦ FinitePresentation X.hom).ι.obj
          ((finitePresentationFunctorOfFiniteEtale
            (T := Spec (S.presheaf.stalk x))).obj L) :=
  finiteEtale_glueingDataNearPoint_of_extends U x E
    (purity_extends_cover_on_stalkOpen U x hOpen hPurity _)

private lemma neighborhood_model_of_gluingData
    (S : Scheme.{u}) (U : S.Opens) (x : S) (hU : IsRetrocompact (U : Set S))
    (D : GlueingNearPoint.glueingDataNearPoint S U x) :
    ∃ M : GlueingNearPoint.FinitePresentationNeighborhoodModel S U x,
      Nonempty ((Over.pullback U.ι).obj
          ((GlueingNearPoint.neighborhoodModelToAmbient S U x).obj M) ≅
        (GlueingNearPoint.openComponent S U x).obj D) ∧
      Nonempty ((Over.pullback (S.fromSpecStalk x)).obj
          ((GlueingNearPoint.neighborhoodModelToAmbient S U x).obj M) ≅
        (GlueingNearPoint.localComponent S U x).obj D) := by
  classical
  let W := GlueingNearPoint.FinitePresentationNeighborhoodModel.restrictionMorphisms
    (S := S) (U := U) (s := x)
  obtain ⟨e, a, b, -⟩ := GlueingNearPoint.glueingEquivalenceNearPoint S U x hU
  obtain ⟨M, ⟨i⟩⟩ := (Localization.essSurj W.Q W).mem_essImage (e.inverse.obj D)
  let ec : e.functor.obj (W.Q.obj M) ≅ D := e.functor.mapIso i ≪≫ e.counitIso.app D
  exact ⟨M, ⟨(a.app M).symm ≪≫ (GlueingNearPoint.openComponent S U x).mapIso ec⟩,
    ⟨(b.app M).symm ≪≫ (GlueingNearPoint.localComponent S U x).mapIso ec⟩⟩

/-! ### Extending a cover to a strictly larger open -/

/-- **Extending a cover across one point.** Let `S` be a locally Noetherian scheme, `U ⊆ S` a
retrocompact open, `x ∉ U` a point and `E` a finite étale cover of `U`. If the restriction of
`E` to the preimage of `U` in `Spec 𝒪_{S, x}` extends to a finite étale cover of
`Spec 𝒪_{S, x}`, then `E` extends to a finite étale cover of an open `V ⊇ U` containing `x`.

This is the step of [Stacks, Tag 0EY7] and of [Stacks, Tag 0H2W] which spreads a local
extension out over a neighbourhood: the two covers form a glueing datum near `x`, which by
[Stacks, Tag 0BQ5] comes from a scheme of finite presentation over a neighbourhood of
`U ∪ {x}`, finite and étale over a smaller such neighbourhood by [Stacks, Tag 0EY3]. -/
public theorem exists_finiteEtale_extension_neighborhood_of_extends
    {S : Scheme.{u}} [IsLocallyNoetherian S] (U : S.Opens) (hU : IsRetrocompact (U : Set S))
    (x : S) (hx : x ∉ U) (E : FiniteEtaleOver U.toScheme)
    (hE : ∃ L : FiniteEtaleOver (Spec (S.presheaf.stalk x)),
      Nonempty ((finiteEtaleBaseChange (((S.fromSpecStalk x) ⁻¹ᵁ U).ι)).obj L ≅
        (finiteEtaleBaseChange ((S.fromSpecStalk x) ∣_ U)).obj E)) :
    ∃ (V : S.Opens) (hUV : U ≤ V) (_hxV : x ∈ V) (F : FiniteEtaleOver V.toScheme),
      Nonempty ((finiteEtaleBaseChange (S.homOfLE hUV)).obj F ≅ E) := by
  obtain ⟨L, D, hDopen, hDlocal⟩ := finiteEtale_glueingDataNearPoint_of_extends U x E hE
  obtain ⟨M, ⟨iU⟩, ⟨iR⟩⟩ := neighborhood_model_of_gluingData S U x hU D
  let ambient := (GlueingNearPoint.neighborhoodModelToAmbient S U x).obj M
  let fpU := finitePresentationFunctorOfFiniteEtale (T := U.toScheme)
  let P_U : ObjectProperty (Over U.toScheme) := fun Y ↦ FinitePresentation Y.hom
  let iU' := iU ≪≫ eqToIso hDopen
  let iR' := iR ≪≫ eqToIso hDlocal
  have hFiniteU : IsFinite ((Over.pullback U.ι).obj ambient).hom :=
    (prop_iff_overIso iU').mpr E.prop.1
  have hEtaleU : Etale ((Over.pullback U.ι).obj ambient).hom :=
    (prop_iff_overIso iU').mpr E.prop.2
  have hFiniteR : IsFinite ((Over.pullback (S.fromSpecStalk x)).obj ambient).hom :=
    (prop_iff_overIso iR').mpr L.prop.1
  have hEtaleR : Etale ((Over.pullback (S.fromSpecStalk x)).obj ambient).hom :=
    (prop_iff_overIso iR').mpr L.prop.2
  obtain ⟨Vf, hUVf, _, hxVf, hFiniteVf⟩ :=
    GlueingNearPoint.exists_open_isFinite S U x hx hU M hFiniteU hFiniteR
  obtain ⟨Ve, hUVe, _, hxVe, hEtaleVe⟩ :=
    GlueingNearPoint.exists_open_etale S U x hx hU M hEtaleU hEtaleR
  let V := Vf ⊓ Ve
  have hUV : U ≤ V := le_inf hUVf hUVe
  have hxV : x ∈ V := ⟨hxVf, hxVe⟩
  have hFiniteV : IsFinite ((Over.pullback V.ι).obj ambient).hom :=
    prop_pullback_ι_of_le inf_le_left hFiniteVf
  have hEtaleV : Etale ((Over.pullback V.ι).obj ambient).hom :=
    prop_pullback_ι_of_le inf_le_right hEtaleVe
  let Z := (Over.pullback V.ι).obj ambient
  let F : FiniteEtaleOver V.toScheme :=
    MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) (X := V.toScheme) Z.hom
      ⟨hFiniteV, hEtaleV⟩
  let gU := S.homOfLE hUV
  let isoU := overPullbackIsoOfComp (f := gU) (g := V.ι) (h := U.ι) (by simp [gU]) ambient
  let fpFEIso : P_U.ι.obj (fpU.obj E) ≅
      (MorphismProperty.Over.forget finiteEtale ⊤ U.toScheme).obj E := Over.isoMk (Iso.refl _)
  let iExtend' : (Over.pullback gU).obj Z ≅
      (MorphismProperty.Over.forget finiteEtale ⊤ U.toScheme).obj E :=
    isoU.symm ≪≫ iU' ≪≫ fpFEIso
  exact ⟨V, hUV, hxV, F, ⟨MorphismProperty.Over.isoMk
    ((Over.forget U.toScheme).mapIso iExtend') iExtend'.hom.w⟩⟩

private lemma exists_finiteEtale_extension_neighborhood
    {S : Scheme.{u}} [IsNoetherian S] (U : S.Opens) (x : S) (hx : x ∉ U)
    (hOpen : (S.fromSpecStalk x) ⁻¹ᵁ U = Stacks.puncturedSpectrum (S.presheaf.stalk x))
    (hPurity : HasPurity (S.presheaf.stalk x)) (E : FiniteEtaleOver U.toScheme) :
    ∃ (V : S.Opens) (hUV : U ≤ V) (_hxV : x ∈ V) (F : FiniteEtaleOver V.toScheme),
      Nonempty ((finiteEtaleBaseChange (S.homOfLE hUV)).obj F ≅ E) :=
  exists_finiteEtale_extension_neighborhood_of_extends U
    (noetherianSpace_isRetrocompact S U) x hx E
    (purity_extends_cover_on_stalkOpen U x hOpen hPurity _)

/-! ### Essential surjectivity -/

/-- **Stacks Project, Tag 0EY7.** Let `j : U ⟶ X` be an open immersion of Noetherian schemes
such that purity holds for `𝒪_{X, x}` at every point `x` outside the image of `j`.  Then every
finite étale cover of `U` is the restriction of a finite étale cover of `X`. -/
@[stacks 0EY7]
theorem essSurj_finiteEtaleBaseChange_of_hasPurity
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X]
    (h : ∀ x : X, x ∉ j.opensRange → HasPurity (X.presheaf.stalk x)) :
    (finiteEtaleBaseChange j).EssSurj := by
  classical
  refine ⟨fun E ↦ ?_⟩
  let U₀ : X.Opens := j.opensRange
  let e₀ : U ≅ U₀.toScheme := IsOpenImmersion.isoOfRangeEq j U₀.ι (by simp [U₀])
  let E₀ := (finiteEtaleBaseChange e₀.inv).obj E
  have hE₀ : Nonempty ((finiteEtaleBaseChange e₀.hom).obj E₀ ≅ E) :=
    ⟨finiteEtaleBaseChangeObjIsoSelf e₀.hom_inv_id E⟩
  let Ext (V : X.Opens) : Prop :=
    ∃ (hUV : U₀ ≤ V) (F : FiniteEtaleOver V.toScheme),
      Nonempty ((finiteEtaleBaseChange (X.homOfLE hUV)).obj F ≅ E₀)
  have hExt₀ : Ext U₀ :=
    ⟨le_rfl, E₀, ⟨eqToIso (congrArg (fun f ↦ (finiteEtaleBaseChange f).obj E₀)
      (Scheme.homOfLE_rfl X U₀)) ≪≫ finiteEtaleBaseChangeId.app E₀⟩⟩
  obtain ⟨W, -, hWmax⟩ := exists_maximal_ge_of_wellFoundedGT Ext U₀ hExt₀
  obtain ⟨hU₀W, EW, ⟨iW⟩⟩ := hWmax.1
  have hWtop : W = ⊤ := by
    by_contra hWneq
    have hZne : ((W : Set X)ᶜ).Nonempty := Set.nonempty_compl.mpr fun hWuniv ↦
      hWneq (SetLike.coe_injective (by simpa using hWuniv))
    obtain ⟨C, x, -, -, hCZ, hCmax, hgen⟩ :=
      exists_genericPoint_maximal_irreducible_subset ((W : Set X)ᶜ)
        (isClosed_compl_iff.mpr W.2) hZne
    have hxW : x ∉ W := hCZ hgen.mem
    obtain ⟨V, hWV, hxV, EV, ⟨iWV⟩⟩ :=
      exists_finiteEtale_extension_neighborhood W x hxW
        (stalkPullback_eq_puncturedSpectrum_of_genericPoint W x C hCZ hCmax hgen)
        (h x (fun hx ↦ hxW (hU₀W hx))) EW
    have hExtV : Ext V :=
      ⟨hU₀W.trans hWV, EV, ⟨(finiteEtaleBaseChangeComp (X.homOfLE hU₀W) (X.homOfLE hWV) _
          (Scheme.homOfLE_homOfLE X hU₀W hWV).symm).app EV ≪≫
        (finiteEtaleBaseChange (X.homOfLE hU₀W)).mapIso iWV ≪≫ iW⟩⟩
    exact hxW (hWmax.2 hExtV hWV hxV)
  let eTop : W.toScheme ≅ X := X.isoOfEq hWtop ≪≫ X.topIso
  have hFinalMap : j ≫ eTop.inv = e₀.hom ≫ X.homOfLE hU₀W := by
    have heTop : eTop.hom = W.ι := by simp [eTop, Scheme.isoOfEq_hom_ι]
    apply (cancel_mono eTop.hom).1
    rw [Category.assoc, eTop.inv_hom_id, Category.comp_id, Category.assoc, heTop,
      Scheme.homOfLE_ι]
    exact (IsOpenImmersion.isoOfRangeEq_hom_fac j U₀.ι (by simp [U₀])).symm
  exact ⟨(finiteEtaleBaseChange eTop.inv).obj EW,
    ⟨((finiteEtaleBaseChangeComp j eTop.inv).app EW).symm ≪≫
      (finiteEtaleBaseChangeComp e₀.hom (X.homOfLE hU₀W) _ hFinalMap).app EW ≪≫
      (finiteEtaleBaseChange e₀.hom).mapIso iW ≪≫ Classical.choice hE₀⟩⟩

end AlgebraicGeometry
