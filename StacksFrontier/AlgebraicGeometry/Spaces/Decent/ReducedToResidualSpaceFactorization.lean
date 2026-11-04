module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Subfunctor.Subobject
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.ResidueFieldFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.GenericPointsAndDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.MonoToZeroDimensionalLocalSpectra
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine

/-!
# Factoring a morphism through a residual space

Let `S` be a scheme, let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` and let `x` be
a point of `|X|`. If the image of `|Y| → |X|` is contained in `{x}`, if `Y` is reduced and if
`X` is locally Noetherian, then `f` factors — uniquely — through a residual space of `X` at
`x`. This is Stacks 0H1S.

## Main results

* `AlgebraicGeometry.Space.existsUnique_comp_eq_of_isResidualSpaceAt`: the unique factorization
  through any given residual space of `X` at `x`.
* `AlgebraicGeometry.Space.exists_isResidualSpaceAt_and_existsUnique_comp_eq`: there is a residual
  space of `X` at `x` through which `f` factors uniquely.

## References

* [Stacks Project, Tag 0H1S](https://stacks.math.columbia.edu/tag/0H1S)
* [Stacks Project, Tag 0H1N](https://stacks.math.columbia.edu/tag/0H1N)
* [Stacks Project, Tag 0H1Q](https://stacks.math.columbia.edu/tag/0H1Q)
* [Stacks Project, Tag 06QZ](https://stacks.math.columbia.edu/tag/06QZ)
* [Stacks Project, Tag 06R0](https://stacks.math.columbia.edu/tag/06R0)
* [Stacks Project, Tag 06MG](https://stacks.math.columbia.edu/tag/06MG)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Factoring through a monomorphism of sheaves -/

section Descent

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

/-- A morphism `f : G ⟶ F` whose restriction along a locally surjective `q : H ⟶ G` factors
through a subfunctor `Z` of `F` factors through `Z`, provided `F` and `Z` are sheaves. -/
private theorem exists_comp_subfunctorι_eq_of_isLocallySurjective
    {F G H : Cᵒᵖ ⥤ Type u} (Z : Subfunctor F) (f : G ⟶ F) (q : H ⟶ G)
    (hq : Presheaf.IsLocallySurjective J q)
    (hF : Presieve.IsSheaf J F) (hZ : Presieve.IsSheaf J Z.toFunctor)
    (g : H ⟶ Z.toFunctor) (hg : g ≫ Z.ι = q ≫ f) :
    ∃ g' : G ⟶ Z.toFunctor, g' ≫ Z.ι = f := by
  have hmem (A : Cᵒᵖ) (s : G.obj A) : f.app A s ∈ Z.obj A := by
    have hc : Z.sieveOfSection (f.app A s) ∈ J A.unop := by
      refine J.superset_covering ?_ (hq.imageSieve_mem s)
      rintro W c ⟨t, ht⟩
      show F.map c.op (f.app A s) ∈ Z.obj (Opposite.op W)
      rw [← NatTrans.naturality_apply f c.op s, ← ht, ← types_comp_apply (q.app _) (f.app _),
        ← NatTrans.comp_app, ← hg]
      exact (g.app (Opposite.op W) t).property
    exact (Z.isSheaf_iff hF).1 hZ A (f.app A s) hc
  let g' : G ⟶ Z.toFunctor :=
    { app A := ↾fun s => ⟨f.app A s, hmem A s⟩
      naturality := by
        intro A A' c
        ext s
        apply Subtype.ext
        exact NatTrans.naturality_apply f c s }
  refine ⟨g', ?_⟩
  ext A s
  rfl

/-- The range of a monomorphism of sheaves is a sheaf. -/
private theorem isSheaf_range_of_mono {F Z : Cᵒᵖ ⥤ Type u} (i : Z ⟶ F) [Mono i]
    (hZ : Presheaf.IsSheaf J Z) : Presieve.IsSheaf J (Subfunctor.range i).toFunctor :=
  Presieve.isSheaf_iso J (asIso (Subfunctor.toRange i)) ((isSheaf_iff_isSheaf_of_type J Z).mp hZ)

/-- The inverse of the isomorphism of a monomorphism onto its range composes with the
monomorphism to the inclusion of the range. -/
private theorem inv_toRange_comp_eq_ι {F Z : Cᵒᵖ ⥤ Type u} (i : Z ⟶ F) [Mono i] :
    inv (Subfunctor.toRange i) ≫ i = (Subfunctor.range i).ι := by
  rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]

/-- A morphism `f : G ⟶ F` whose restriction along a locally surjective `q : H ⟶ G` factors
through a monomorphism `i : Z ⟶ F` of sheaves factors through `i`. -/
private theorem exists_comp_eq_of_mono_of_isLocallySurjective
    {F G H Z : Cᵒᵖ ⥤ Type u} (i : Z ⟶ F) [Mono i]
    (f : G ⟶ F) (q : H ⟶ G) (hq : Presheaf.IsLocallySurjective J q)
    (hF : Presheaf.IsSheaf J F) (hZ : Presheaf.IsSheaf J Z)
    (g : H ⟶ Z) (hg : g ≫ i = q ≫ f) :
    ∃ g' : G ⟶ Z, g' ≫ i = f := by
  obtain ⟨g', hg'⟩ := exists_comp_subfunctorι_eq_of_isLocallySurjective (Subfunctor.range i) f q hq
    ((isSheaf_iff_isSheaf_of_type J F).mp hF) (isSheaf_range_of_mono i hZ)
    (g ≫ Subfunctor.toRange i) (by rwa [Category.assoc, Subfunctor.toRange_ι])
  exact ⟨g' ≫ inv (Subfunctor.toRange i), by simpa [inv_toRange_comp_eq_ι] using hg'⟩

end Descent

/-! ### Opens of an object of the site -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The object of the big fppf site over `S` cut out by an open of the scheme underlying an
object `U`: the open subscheme, with the structure morphism inherited from `U`. It lies in the
site because an open subscheme is no larger than the scheme it sits in. -/
private def residualOpenSiteObject (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) : BigFppfOver B S hS :=
  Over.mk ((B.inclusion.preimage (X := B.obj
    (lt_of_le_of_lt (Scheme.size_coe_opens_le _ W) U.left.property))
    (Y := U.left) W.ι) ≫ U.hom)

/-- The inclusion of the object cut out by an open into the object it came from. -/
private def residualOpenSiteInclusion (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    residualOpenSiteObject B S hS U W ⟶ U :=
  Over.homMk (B.inclusion.preimage W.ι)

/-- The morphism of schemes underlying the inclusion of an open is the inclusion of that
open. -/
private theorem residualOpenSiteInclusion_map (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).map (residualOpenSiteInclusion B S hS U W) = W.ι := by
  let kobj := B.obj (lt_of_le_of_lt (Scheme.size_coe_opens_le _ W) U.left.property)
  show B.inclusion.map (B.inclusion.preimage (X := kobj) (Y := U.left) W.ι) = _
  exact B.inclusion.map_preimage _

/-- A family of opens covering the scheme underlying `U` generates a covering sieve of `U`
in the big fppf site over `S`: the inclusions are flat and locally of finite presentation,
being open immersions, and they are jointly surjective. -/
private theorem generate_residualOpenSiteInclusion_mem_topology (U : BigFppfOver B S hS)
    {I : Type u} (W : I → ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (hW : ⨆ j, W j = ⊤) :
    Sieve.generate (Presieve.ofArrows (fun j => residualOpenSiteObject B S hS U (W j))
      (fun j => residualOpenSiteInclusion B S hS U (W j))) ∈ BigFppfOver.topology B S hS U := by
  refine BigFppfOver.sieve_generate_ofArrows_mem_topology
    (fun j => residualOpenSiteObject B S hS U (W j))
    (fun j => residualOpenSiteInclusion B S hS U (W j)) ?_
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun z => ?_, fun j => ?_⟩
  · have hz : z ∈ (⨆ j, W j : ((BigFppfOver.toScheme B S hS).obj U).Opens) := by
      rw [hW]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    refine ⟨j, ⟨⟨z, hj⟩, ?_⟩⟩
    rw [residualOpenSiteInclusion_map]
    rfl
  · rw [residualOpenSiteInclusion_map]
    constructor
    · exact inferInstanceAs (Flat (W j).ι)
    · exact inferInstanceAs (LocallyOfFinitePresentation (W j).ι)

/-! ### Factoring a field-valued point through a residual space -/

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A field-valued point of `X` representing `x` factors through a residual space of `X`
at `x`.** -/
private theorem exists_comp_eq_fieldMorphism_of_isResidualSpaceAt
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X) (i : Z ⟶ X)
    (hi : IsResidualSpaceAt B S hS X x i)
    (p : FieldValuedPoint B S hS X) (hp : p.class B S hS X = x) :
    ∃ g : yoneda.obj (FieldValuedPoint.siteObject B S hS X p) ⟶ Z,
      g ≫ i = fieldMorphism B S hS X p := by
  classical
  obtain ⟨hZalg, hmono, -, -, ⟨z⟩, -, hsupp⟩ := hi
  have _ : Mono i := hmono
  let T := FieldValuedPoint.siteObject B S hS X p
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Zs : AlgebraicSpaces B S hS := ⟨Z, hZalg⟩
  let Ts : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let iz : Zs ⟶ Xs := ObjectProperty.homMk i
  let it : Ts ⟶ Xs := ObjectProperty.homMk (fieldMorphism B S hS X p)
  have _ : Mono iz.hom := by change Mono i; infer_instance
  let Ws := AlgebraicSpaces.fiberProduct B S hS iz it
  let pr : Ws ⟶ Zs := ObjectProperty.homMk (pullback.fst iz.hom it.hom)
  let pt : Ws ⟶ Ts := ObjectProperty.homMk (pullback.snd iz.hom it.hom)
  have hsq : IsPullback pr pt iz it := AlgebraicSpaces.isPullback_fiberProduct B S hS iz it
  have _ : Mono pt.hom := by
    show Mono (pullback.snd iz.hom it.hom); infer_instance
  let taut := (p.tautologicalPoint B S hS X).class B S hS (yoneda.obj T)
  have hcompat : pointsMap B S hS Zs.1 iz.hom z = pointsMap B S hS Ts.1 it.hom taut := by
    show pointsMap B S hS Z i z =
      pointsMap B S hS (yoneda.obj T) (fieldMorphism B S hS X p) taut
    rw [hsupp z, pointsMap_fieldMorphism_tautologicalPoint, hp]
  obtain ⟨w, -, -⟩ := exists_point_of_isPullback B S hS hsq z taut hcompat
  have hdich := isEmpty_points_or_isIso_of_mono_to_spec_field B S hS Ws.property pt.hom T
    (Iso.refl _) p.carrier (Iso.refl _)
  have _ : IsIso pt.hom := hdich.resolve_left fun h => h.false w
  refine ⟨inv pt.hom ≫ pr.hom, ?_⟩
  have hcond : pr.hom ≫ i = pt.hom ≫ fieldMorphism B S hS X p := pullback.condition
  rw [Category.assoc, hcond, IsIso.inv_hom_id_assoc]

/-- **A field-valued point of a chart whose image in `|X|` is `x` factors through a residual
space of `X` at `x`.** -/
private theorem exists_comp_eq_fieldMorphism_chart_of_isResidualSpaceAt
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X) (i : Z ⟶ X)
    (hi : IsResidualSpaceAt B S hS X x i)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (q : FieldValuedPoint B S hS (yoneda.obj U))
    (hq : pointsMap B S hS (yoneda.obj U) a (q.class B S hS (yoneda.obj U)) = x) :
    ∃ g : yoneda.obj (FieldValuedPoint.siteObject B S hS (yoneda.obj U) q) ⟶ Z,
      g ≫ i = fieldMorphism B S hS (yoneda.obj U) q ≫ a := by
  obtain ⟨g, hg⟩ := exists_comp_eq_fieldMorphism_of_isResidualSpaceAt B S hS hX x i hi
    (FieldValuedPoint.map B S hS (yoneda.obj U) a q) (by rwa [← pointsMap_class])
  exact ⟨g, hg.trans (fieldMorphism_map B S hS (yoneda.obj U) a q)⟩

/-! ### Factoring a scheme chart through a residual space -/

/-- **A reduced scheme of the site mapping into `X` through an étale chart, with all of its
points above `x`, factors through a residual space of `X` at `x`.** -/
private theorem exists_comp_eq_of_chart_of_isResidualSpaceAt
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X) (i : Z ⟶ X)
    (hi : IsResidualSpaceAt B S hS X x i)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (b : V ⟶ U) (hV : IsReduced ((BigFppfOver.toScheme B S hS).obj V))
    (hb : ∀ w : points B S hS (yoneda.obj V),
      pointsMap B S hS (yoneda.obj V) (yoneda.map b ≫ a) w = x) :
    ∃ g : yoneda.obj V ⟶ Z, g ≫ i = yoneda.map b ≫ a := by
  classical
  have hZalg := hi.1
  have _ : Mono i := hi.2.1
  let L := BigFppfOver.toScheme B S hS
  have _ : IsLocallyNoetherian (L.obj U) :=
    (exists_atlas_iff_forall_etale B S hS X
      (fun T : Scheme.{u} => IsLocallyNoetherian T) hX).mp hN U a ha
  have _ : IsReduced (L.obj V) := hV
  let E : Set (L.obj U) := {z | pointsMap B S hS (yoneda.obj U) a
    ((schemePointRepresentative B S hS U z).class B S hS (yoneda.obj U)) = x}
  have hE : ∀ z z' : E, z.1 ⤳ z'.1 → z.1 = z'.1 := by
    intro z z' hs
    refine (eq_of_specializes_of_chartPoint_of_isLocallyNoetherian B S hS hX U a ha
      z'.1 z.1 x ?_ ?_ hs).symm
    · exact ⟨schemePointRepresentative B S hS U z'.1,
        schemePointRepresentative_point B S hS U z'.1, z'.2⟩
    · exact ⟨schemePointRepresentative B S hS U z.1,
        schemePointRepresentative_point B S hS U z.1, z.2⟩
  have hcanon : ∀ q : FieldValuedPoint B S hS (yoneda.obj U),
      (schemePointRepresentative B S hS U (schemePoint B S hS U q)).class B S hS
        (yoneda.obj U) = q.class B S hS (yoneda.obj U) :=
    fun q => schemePointRepresentative_class B S hS U q
  have himage : ∀ w : L.obj V, L.map b w ∈ E := by
    intro w
    let q := schemePointRepresentative B S hS V w
    have hq : schemePoint B S hS U
        (FieldValuedPoint.map B S hS (yoneda.obj V) (yoneda.map b) q) = L.map b w := by
      rw [schemePoint_map_yoneda, schemePointRepresentative_point]
    show pointsMap B S hS (yoneda.obj U) a
      ((schemePointRepresentative B S hS U (L.map b w)).class B S hS (yoneda.obj U)) = x
    rw [← hq, hcanon, ← pointsMap_class, ← pointsMap_comp_apply]
    exact hb _
  let family : E → Scheme.{u} := fun z => Spec (.of ((L.obj U).residueField z.1))
  let fam : (z : E) → family z ⟶ L.obj U := fun z => (L.obj U).fromSpecResidueField z.1
  obtain ⟨c₀, hc₀⟩ := exists_factorization_through_residueFields (L.map b) E hE himage
  let c : L.obj V ⟶ ∐ family := c₀
  let d : (∐ family) ⟶ L.obj U := Sigma.desc fam
  have hc : c ≫ d = L.map b := hc₀
  let W : E → (L.obj V).Opens := fun z => c ⁻¹ᵁ (Sigma.ι family z).opensRange
  have hsig : ⨆ z, (Sigma.ι family z).opensRange = ⊤ :=
    (sigmaOpenCover family).iSup_opensRange
  have hW : ⨆ z, W z = ⊤ := by
    show ⨆ z, c ⁻¹ᵁ (Sigma.ι family z).opensRange = ⊤
    rw [← Scheme.Hom.preimage_iSup, hsig]
    simp
  let R := Subfunctor.range i
  let e : Z ≅ R.toFunctor := asIso (Subfunctor.toRange i)
  have hR := isSheaf_range_of_mono i hZalg.isSheaf
  have hmem : yonedaEquiv (yoneda.map b ≫ a) ∈ R.obj (Opposite.op V) := by
    apply (R.isSheaf_iff ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)).mp hR
    apply (BigFppfOver.topology B S hS).superset_covering _
      (generate_residualOpenSiteInclusion_mem_topology B S hS V W hW)
    rw [Sieve.generate_le_iff]
    rintro A morphism ⟨z⟩
    let q := schemePointRepresentative B S hS U z.1
    let Tq := FieldValuedPoint.siteObject B S hS (yoneda.obj U) q
    obtain ⟨lift, hlift⟩ :=
      exists_comp_eq_fieldMorphism_chart_of_isResidualSpaceAt B S hS hX x i hi U a q z.2
    let piece := residualOpenSiteObject B S hS V (W z)
    let incl := residualOpenSiteInclusion B S hS V (W z)
    have hincl : L.map incl = (W z).ι := residualOpenSiteInclusion_map B S hS V (W z)
    let k : L.obj piece ⟶ L.obj Tq :=
      c.resLE (Sigma.ι family z).opensRange (W z) le_rfl ≫
        (Sigma.ι family z).isoOpensRange.inv
    let ι' : L.obj Tq ⟶ ∐ family := Sigma.ι family z
    have hkι : k ≫ ι' = L.map incl ≫ c := by
      rw [hincl]
      show (c.resLE (Sigma.ι family z).opensRange (W z) le_rfl ≫
        (Sigma.ι family z).isoOpensRange.inv) ≫ Sigma.ι family z = (W z).ι ≫ c
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
      exact Scheme.Hom.resLE_comp_ι c le_rfl
    have hqval : L.map q.value = (L.obj U).fromSpecResidueField z.1 :=
      toScheme_map_siteHom_schemePointRepresentative B S hS U z.1
    have hιd : ι' ≫ d = L.map q.value := by
      rw [hqval]
      show Sigma.ι family z ≫ Sigma.desc fam = (L.obj U).fromSpecResidueField z.1
      have hd : Sigma.ι family z ≫ Sigma.desc fam = fam z := by simp
      exact hd
    have hk : k ≫ L.map q.value = L.map incl ≫ L.map b := by
      rw [← hιd, ← Category.assoc, hkι, Category.assoc, hc]
    let kbase : piece.left ⟶ Tq.left := B.inclusion.preimage k
    have hkbase : kbase ≫ q.value.left = incl.left ≫ b.left := by
      apply B.inclusion.map_injective
      rwa [B.inclusion.map_comp, B.inclusion.map_preimage, B.inclusion.map_comp]
    let ksite : piece ⟶ Tq := Over.homMk kbase
      ((congrArg (kbase ≫ ·) (Over.w q.value)).symm.trans
        (by rw [reassoc_of% hkbase, Over.w b, Over.w incl]))
    have hksite : ksite ≫ q.value = incl ≫ b := Over.OverMorphism.ext hkbase
    have hfm : fieldMorphism B S hS (yoneda.obj U) q = yoneda.map q.value :=
      fieldMorphism_yoneda B S hS q
    have heq : (yoneda.map ksite ≫ lift) ≫ i =
        yoneda.map incl ≫ (yoneda.map b ≫ a) := by
      rw [Category.assoc, hlift, hfm, ← Category.assoc, ← yoneda.map_comp, hksite,
        yoneda.map_comp, Category.assoc]
    show X.map incl.op (yonedaEquiv (yoneda.map b ≫ a)) ∈ R.obj _
    rw [yonedaEquiv_naturality, ← heq, yonedaEquiv_comp]
    exact ⟨_, rfl⟩
  let lift : yoneda.obj V ⟶ R.toFunctor := yonedaEquiv.symm ⟨_, hmem⟩
  refine ⟨lift ≫ e.inv, ?_⟩
  have hinv : e.inv ≫ i = R.ι := inv_toRange_comp_eq_ι i
  rw [Category.assoc, hinv]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  have hl : yonedaEquiv lift =
      (⟨yonedaEquiv (yoneda.map b ≫ a), hmem⟩ : R.toFunctor.obj (Opposite.op V)) :=
    (yonedaEquiv (F := R.toFunctor)).apply_symm_apply _
  rw [hl]
  rfl

/-! ### Stacks 0H1S -/

/-- **A morphism from a reduced space with image one point of a locally Noetherian space factors
through every residual space at that point.** Let `S` be a scheme, let `f : Y ⟶ X` be a morphism of
algebraic spaces over `S` and let `x` be a point of `|X|`. Assume that the image of `|Y| → |X|` is
contained in `{x}`, that `Y` is reduced and that `X` is locally Noetherian. Then `f` factors
uniquely through any residual space `i : Z ⟶ X` of `X` at `x`. -/
@[stacks 0H1S "the factorization through a given residual space at the point"]
theorem existsUnique_comp_eq_of_isResidualSpaceAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : Y ⟶ X) (x : points B S hS X) (i : Z ⟶ X)
    (hi : IsResidualSpaceAt B S hS X x i)
    (himage : Set.range (pointsMap B S hS Y f) ⊆ {x})
    (hred : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    ∃! g : Y ⟶ Z, g ≫ i = f := by
  classical
  have hZalg := hi.1
  have _ : Mono i := hi.2.1
  let PEtale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let PSurjective := MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  have _ : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have _ : PEtale.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ := MorphismProperty.relative_isStableUnderComposition PEtale (F := yoneda)
  have _ := MorphismProperty.relative_isStableUnderBaseChange PEtale (F := yoneda)
  have _ := MorphismProperty.relative_isStableUnderBaseChange PSurjective (F := yoneda)
  have hf : ∀ w : points B S hS Y, pointsMap B S hS Y f w = x :=
    fun w => himage ⟨w, rfl⟩
  have hallReduced := (exists_atlas_iff_forall_etale B S hS Y
    (fun T : Scheme.{u} => IsReduced T) hY).mp hred
  obtain ⟨V, v, hvSurjective, hvEtale, -⟩ := hred
  obtain ⟨U, a, haSurjective, haEtale⟩ := hX.exists_atlas
  let rep := haSurjective.1
  let P := rep.pullback (v ≫ f)
  let q := rep.snd (v ≫ f)
  let b := yoneda.preimage (rep.fst (v ≫ f))
  have hsq : IsPullback (yoneda.map b) (yoneda.map q) a (v ≫ f) := by
    simpa [b] using rep.isPullback (v ≫ f)
  have hqSurjective : PSurjective.presheaf (yoneda.map q) :=
    MorphismProperty.of_isPullback hsq haSurjective
  have hqEtale : PEtale.presheaf (yoneda.map q) :=
    MorphismProperty.of_isPullback hsq haEtale
  have hqvEtale : PEtale.presheaf (yoneda.map q ≫ v) :=
    MorphismProperty.comp_mem _ _ _ hqEtale hvEtale
  have hPReduced : IsReduced ((BigFppfOver.toScheme B S hS).obj P) :=
    hallReduced P (yoneda.map q ≫ v) hqvEtale
  have hbPoints : ∀ w : points B S hS (yoneda.obj P),
      pointsMap B S hS (yoneda.obj P) (yoneda.map b ≫ a) w = x := by
    intro w
    rw [hsq.w, ← Category.assoc, pointsMap_comp_apply]
    exact hf _
  obtain ⟨gP, hgP⟩ := exists_comp_eq_of_chart_of_isResidualSpaceAt B S hS hX x i hi hN
    U P a haEtale b hPReduced hbPoints
  have hgP' : gP ≫ i = yoneda.map q ≫ (v ≫ f) := hgP.trans hsq.w
  obtain ⟨gV, hgV⟩ := exists_comp_eq_of_mono_of_isLocallySurjective i (v ≫ f) (yoneda.map q)
    (isLocallySurjective_of_surjective_etale B S hS (yoneda.map q) hqSurjective hqEtale)
    hX.isSheaf hZalg.isSheaf gP hgP'
  obtain ⟨g, hg⟩ := exists_comp_eq_of_mono_of_isLocallySurjective i f v
    (isLocallySurjective_of_surjective_etale B S hS v hvSurjective hvEtale)
    hX.isSheaf hZalg.isSheaf gV hgV
  exact ⟨g, hg, fun g' hg' => (cancel_mono i).mp (hg'.trans hg.symm)⟩

/-- **A morphism from a reduced space with image one point of a locally Noetherian space factors
through a residual space.** Let `f : Y ⟶ X` be a morphism of algebraic spaces whose image in `|X|`
is contained in `{x}`, with `Y` reduced and `X` locally Noetherian. Then there is a residual space
of `X` at `x` through which `f` factors, by a unique morphism. -/
@[stacks 0H1S]
theorem exists_isResidualSpaceAt_and_existsUnique_comp_eq
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : Y ⟶ X) (x : points B S hS X)
    (himage : Set.range (pointsMap B S hS Y f) ⊆ {x})
    (hred : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : Z ⟶ X),
      IsResidualSpaceAt B S hS X x i ∧ ∃! g : Y ⟶ Z, g ≫ i = f := by
  obtain ⟨Z, i, hi⟩ := exists_isResidualSpaceAt B S hS hX x
  exact ⟨Z, i, hi, existsUnique_comp_eq_of_isResidualSpaceAt B S hS hX hY f x i hi himage hred hN⟩

end AlgebraicGeometry.Space

end
