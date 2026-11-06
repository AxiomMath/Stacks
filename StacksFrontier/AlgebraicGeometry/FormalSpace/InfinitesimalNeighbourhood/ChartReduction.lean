module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.ReducedPoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective

/-!
# The reduction of a formal algebraic space on an affine formal chart

Let `W` be a formal algebraic space with reduction `i : W_red ⟶ W` and let `f : Spf A ⟶ W` be
representable by algebraic spaces and étale, with `A` weakly admissible and `𝔞 ⊆ A` its ideal of
topologically nilpotent elements. A section `s` of `Spf A` maps into `W_red` exactly when it lies
in the stage `Spec(A/𝔞)`: `Spf A ×_W W_red = Spec(A/𝔞)`, the reduction of `Spf A`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affineOpenCover_mem`: the affine opens of an object of the
  site form a covering family.
* `AlgebraicGeometry.FormalSpace.mem_range_nilStage_iff`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The affine open subschemes of an object of the big fppf site, as objects of the site, form a
covering family of open immersions. -/
theorem exists_affineOpenCover_mem (V : BigFppfOver B S hS) :
    ∃ (ι : Type u) (U : ι → BigFppfOver B S hS) (k : ∀ i, U i ⟶ V),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (U i))) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (k i))) ∧
      Sieve.ofArrows U k ∈ BigFppfOver.topology B S hS V := by
  let X := (BigFppfOver.toScheme B S hS).obj V
  let 𝒰 := X.affineCover
  let U : 𝒰.I₀ → BigFppfOver B S hS := fun x =>
    Over.mk (ObjectProperty.homMk (X := ⟨𝒰.X x,
      (Scheme.size_le_of_isOpenImmersion (𝒰.f x)).trans_lt V.left.2⟩) (Y := B.obj hS)
      (𝒰.f x ≫ V.hom.hom))
  let k : ∀ x, U x ⟶ V := fun x => Over.homMk (ObjectProperty.homMk (𝒰.f x)) rfl
  refine ⟨𝒰.I₀, U, k, fun x => inferInstanceAs (IsAffine (Spec _)), fun x =>
    inferInstanceAs (IsOpenImmersion (𝒰.f x)), ?_⟩
  exact fppf_ofArrows_mem B S hS U k (fun x => inferInstanceAs (Flat (𝒰.f x)))
    (fun x => inferInstanceAs (LocallyOfFinitePresentation (𝒰.f x)))
    (fun y => ⟨𝒰.idx y, 𝒰.covers y⟩)

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- The image of the reduction stage in a formal spectrum is a sheaf. -/
theorem isSheaf_range_nilStage (hA : IsWeaklyAdmissible A) (D : QuotientSystem B S hS A) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS)
      (Subfunctor.range (stageIncl D (nilWeakIdeal hA)).hom).toFunctor := by
  let Jt := BigFppfOver.topology B S hS
  have : Mono (stageIncl D (nilWeakIdeal hA)) :=
    mono_formalSpectrumInclusion_of_isWeaklyAdmissible hA D (OrderDual.toDual (nilWeakIdeal hA))
  have : Mono (stageIncl D (nilWeakIdeal hA)).hom :=
    (sheafToPresheaf Jt (Type (u + 1))).map_mono _
  exact (isSheaf_iff_isSheaf_of_type Jt _).1 ((Presheaf.isSheaf_of_iso_iff (asIso
    (Subfunctor.toRange (stageIncl D (nilWeakIdeal hA)).hom))).1
      ((Sheaf.sheafifiedYoneda Jt).obj _).property)

/-- If the restriction of `σ` along `k` lies in a subfunctor, so does its restriction along
`g ≫ k`. -/
private theorem map_comp_mem_subfunctor {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type*}
    (G : Subfunctor F) {X Y Z : C} (g : X ⟶ Y) (k : Y ⟶ Z) (σ : F.obj (op Z))
    (h : F.map k.op σ ∈ G.obj (op Y)) : F.map (g ≫ k).op σ ∈ G.obj (op X) := by
  rw [op_comp, Functor.map_comp_apply]
  exact G.map g.op h

/-- Membership in the image of the reduction stage is local. -/
theorem mem_range_nilStage_of_mem (hA : IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    {T : BigFppfOver B S hS} (s : (formalSpectrum D).obj.obj (op T))
    (hs : (Subfunctor.range (stageIncl D (nilWeakIdeal hA)).hom).sieveOfSection s ∈
      BigFppfOver.topology B S hS T) :
    s ∈ (Subfunctor.range (stageIncl D (nilWeakIdeal hA)).hom).obj (op T) :=
  ((Subfunctor.range (stageIncl D (nilWeakIdeal hA)).hom).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type _ _).1 (formalSpectrum D).property)).1
      (isSheaf_range_nilStage hA D) (op T) s hs

/-- **A section of a formal spectrum over a reduced object lies in the reduction stage.** -/
theorem mem_range_nilStage_of_isReduced (hA : IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) {V : BigFppfOver B S hS}
    (hV : IsReduced ((BigFppfOver.toScheme B S hS).obj V))
    (σ : (formalSpectrum D).obj.obj (op V)) :
    σ ∈ (Subfunctor.range (stageIncl D (nilWeakIdeal hA)).hom).obj (op V) := by
  let Jt := BigFppfOver.topology B S hS
  have : Jt.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨ι, U, k, haff, hopen, hmem⟩ := exists_affineOpenCover_mem V
  refine mem_range_nilStage_of_mem hA D σ (Jt.superset_covering ?_ hmem)
  rintro T' _ ⟨T'', g, _, ⟨i⟩, rfl⟩
  have := haff i
  have := hopen i
  have := hV
  have hred : IsReduced ((BigFppfOver.toScheme B S hS).obj (U i)) :=
    isReduced_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map (k i))
  obtain ⟨z, hz⟩ := exists_factor_nilStage_of_isReduced hA D hred
    ((Sheaf.sectionEquiv Jt).symm ((formalSpectrum D).obj.map (k i).op σ))
  have hmemi : (formalSpectrum D).obj.map (k i).op σ ∈
      (Subfunctor.range (stageIncl D (nilWeakIdeal hA)).hom).obj (op (U i)) := by
    refine ⟨Sheaf.sectionEquiv Jt ((Sheaf.sheafifiedYoneda Jt).map z), ?_⟩
    rw [← Sheaf.sectionEquiv_comp, hz, Equiv.apply_symm_apply]
  exact map_comp_mem_subfunctor _ g (k i) σ hmemi

/-- **A section of an affine formal chart mapping into the reduction lies in the reduction
stage.** Let `f : Spf A ⟶ W` be representable by algebraic spaces and étale and `i : W_red ⟶ W`
a reduction. A section of `Spf A` whose image in `W` lies in `W_red` lies in `Spec(A/𝔞)`. Locally
its image lifts to a reduced étale chart `U` of `W_red`; then it lifts to the fibre product
`U ×_W Spf A`, an algebraic space étale over `U`, hence locally to one of its reduced charts, over
which every section of `Spf A` lies in the reduction stage. -/
theorem mem_range_nilStage_of_mapsTo_reduction (hA : IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) {W Wred : FppfSheaf B S hS} {i : Wred ⟶ W}
    (hred : IsReduction B S hS W Wred i) (f : formalSpectrum D ⟶ W)
    (hfrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hfet : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hfrep)
    {T : BigFppfOver B S hS} (s : (formalSpectrum D).obj.obj (op T))
    (r : Wred.obj.obj (op T)) (hr : i.hom.app (op T) r = f.hom.app (op T) s) :
    s ∈ (Subfunctor.range (stageIncl D (nilWeakIdeal hA)).hom).obj (op T) := by
  classical
  let Jt := BigFppfOver.topology B S hS
  let Rg := Subfunctor.range (stageIncl D (nilWeakIdeal hA)).hom
  refine mem_range_nilStage_of_mem hA D s ?_
  obtain ⟨Uc, c, hcs, hce, hcred⟩ := hred.reduced
  have : Presheaf.IsLocallySurjective Jt c :=
    isLocallySurjective_of_surjective_etale_uliftYoneda B S hS c hcs hce
  refine Jt.transitive (Presheaf.imageSieve_mem Jt c r) _ ?_
  rintro T1 h1 ⟨u, hu⟩
  let a : uliftYoneda.{u + 1}.obj Uc ⟶ W.obj := c ≫ i.hom
  obtain ⟨Ve, e, hes, hee, hVred⟩ :=
    hasEtaleLocalPropertyULift_isReduced_of_isEtale_over_isReduced B S hS Uc hcred
      (pullback a f.hom) (hfrep Uc a) (pullback.fst a f.hom) (hfet Uc a)
  have hpt : a.app (op T1) u = f.hom.app (op T1) ((formalSpectrum D).obj.map h1.op s) := by
    show i.hom.app _ (c.app _ u) = _
    rw [hu, NatTrans.naturality_apply i.hom, hr, NatTrans.naturality_apply f.hom]
  have hsq := (IsPullback.of_hasPullback a f.hom).map
    ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type (u + 1))).obj (op T1))
  obtain ⟨p, -, hp2⟩ := Types.exists_of_isPullback hsq u _ hpt
  have : Presheaf.IsLocallySurjective Jt e :=
    isLocallySurjective_of_surjective_etale_uliftYoneda B S hS e hes hee
  refine Jt.transitive (Presheaf.imageSieve_mem Jt e p) _ ?_
  rintro T2 h2 ⟨⟨w⟩, hv⟩
  refine Jt.superset_covering ?_ (Jt.top_mem T2)
  intro T3 g _
  let σ := (e ≫ pullback.snd a f.hom).app (op Ve) (ULift.up (𝟙 Ve))
  have hσ := mem_range_nilStage_of_isReduced hA D hVred σ
  have hw : (uliftYoneda.{u + 1}.obj Ve).map w.op (ULift.up (𝟙 Ve)) = ULift.up w :=
    ULift.ext (Category.comp_id w)
  have h3 : (pullback.snd a f.hom).app (op T2) (e.app (op T2) (ULift.up w)) =
      (formalSpectrum D).obj.map w.op σ := by
    show (e ≫ pullback.snd a f.hom).app (op T2) (ULift.up w) = _
    exact (congrArg _ hw.symm).trans (NatTrans.naturality_apply _ w.op _)
  have key : (formalSpectrum D).obj.map (h2 ≫ h1).op s =
      (formalSpectrum D).obj.map w.op σ := by
    calc (formalSpectrum D).obj.map (h2 ≫ h1).op s
        = (formalSpectrum D).obj.map h2.op ((formalSpectrum D).obj.map h1.op s) := by
          rw [op_comp, Functor.map_comp_apply]
      _ = (formalSpectrum D).obj.map h2.op ((pullback.snd a f.hom).app (op T1) p) :=
          congrArg _ hp2.symm
      _ = (pullback.snd a f.hom).app (op T2) ((pullback a f.hom).map h2.op p) :=
          (NatTrans.naturality_apply (pullback.snd a f.hom) h2.op p).symm
      _ = (pullback.snd a f.hom).app (op T2) (e.app (op T2) (ULift.up w)) := by rw [hv]
      _ = _ := h3
  exact map_comp_mem_subfunctor Rg g (h2 ≫ h1) s (key ▸ Rg.map w.op hσ)

/-- The reduction stage `Spec(A/𝔞)` is reduced. -/
theorem isReduced_stageObj_nilWeakIdeal (hA : IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj (D.stageObj (nilWeakIdeal hA))) := by
  show IsReduced (Spec (.of (A ⧸ topologicalNilradical A)))
  have : _root_.IsReduced (A ⧸ topologicalNilradical A) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp
      (TopologicalRing.topologicalNilradical_isRadical (B := A))
  infer_instance

/-- **A section of an affine formal chart in the reduction stage maps into the reduction.** The
reduction stage is a reduced algebraic space, so its morphism to `W` factors through `W_red`. -/
theorem exists_mapsTo_reduction_of_mem_range_nilStage (hA : IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) {W Wred : FppfSheaf B S hS} {i : Wred ⟶ W}
    (hred : IsReduction B S hS W Wred i) (f : formalSpectrum D ⟶ W)
    {T : BigFppfOver B S hS} (s : (formalSpectrum D).obj.obj (op T))
    (hs : s ∈ (Subfunctor.range (stageIncl D (nilWeakIdeal hA)).hom).obj (op T)) :
    ∃ r : Wred.obj.obj (op T), i.hom.app (op T) r = f.hom.app (op T) s := by
  let Jt := BigFppfOver.topology B S hS
  let N := nilWeakIdeal hA
  let U : FppfSheaf B S hS := ⟨uliftYoneda.{u + 1}.obj (D.stageObj N),
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (D.stageObj N)).isSheaf⟩
  obtain ⟨g, hg, -⟩ := hred.universal U
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (D.stageObj N))
    (hasEtaleLocalPropertyULift_isReduced_uliftYoneda B S hS _
      (isReduced_stageObj_nilWeakIdeal hA D))
    ((sheafificationIso U).hom ≫ stageIncl D N ≫ f)
  obtain ⟨y, rfl⟩ := hs
  refine ⟨g.hom.app _ ((sheafificationIso U).inv.hom.app _ y), ?_⟩
  refine (congrArg (fun φ : U ⟶ W => φ.hom.app (op T)
    ((sheafificationIso U).inv.hom.app _ y)) hg).trans ?_
  show ((sheafificationIso U).inv ≫ (sheafificationIso U).hom ≫ stageIncl D N ≫ f).hom.app
    (op T) y = _
  rw [Iso.inv_hom_id_assoc]
  rfl

end AlgebraicGeometry.FormalSpace

end
