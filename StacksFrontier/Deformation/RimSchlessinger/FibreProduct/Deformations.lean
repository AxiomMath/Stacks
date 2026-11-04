module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.Examples.Geometric.Rings
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldComparison
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransport
public import StacksFrontier.RingTheory.MilnorPatching.Algebras

/-!
# Deformations of an algebra satisfy the Rim–Schlessinger condition

The projection from flat algebras over `𝒞_Λ` to `𝒞_Λ` satisfies condition (RS): given two
morphisms of flat algebras into a common target, one of them surjective on the bases, the fibre
product exists and is computed on the bases. The fibre product of the bases is the one of Stacks
06GH; the flat algebra over it is the fibre product of the two flat algebras, which is flat by
Milnor patching, and the two squares it sits in are pushouts.

Consequently, for any `k`-algebra `P` the deformation category of `P` is a deformation category.

## Main results

* `Deformation.Examples.flatAlgebraCategory_projection_satisfiesRS`: flat algebras over `𝒞_Λ`
  satisfy the Rim–Schlessinger condition.
* `Deformation.Examples.ringDeformationCategory_isDeformationCategory`: deformations of a
  `k`-algebra form a deformation category.

## Implementation notes

The first assertion is about the projection from all flat algebras; the second is about the slice
over the flat algebra `(k, P)`. The passage from the first to the second is
`Deformation.Examples.isDeformationCategory_objectsOverFunctor_of_baseIso`, which localizes at an
object whose image is merely isomorphic to `Deformation.residueFieldObject`: the image here is
`Deformation.Examples.residueFieldBase`, whose carrier is `k` rather than `ULift k`, and
`Deformation.Examples.residueFieldBaseIso` is the comparison.

Flatness of the fibre product, and the two base-change squares it sits in, are Milnor patching
for ring maps in one universe: `MilnorPatching.pullback_flat_of_components`,
`MilnorPatching.pullback_baseChange` and `MilnorPatching.flat_baseChange_pullback` of
`StacksFrontier/RingTheory/MilnorPatching/Algebras.lean`.

## References

* [Stacks Project, Tag 0DY2](https://stacks.math.columbia.edu/tag/0DY2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace Deformation.Examples

open scoped TensorProduct

/-- Two morphisms of flat algebras into a common target, one of them surjective on the bases,
admit a fibre product, and it is computed on the bases. -/
private theorem flatAlgebraCategory_pullback_exists
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {x₁ x₂ x : FlatAlgebraCategory.{u, w} Λ k}
    (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x)
    (hf₂ : Function.Surjective f₂.base.hom) :
    ∃ c : PullbackCone f₁ f₂,
      Nonempty (IsLimit c) ∧
        Nonempty (IsLimit (c.map (FlatAlgebraCategory.projection (Λ := Λ) (k := k)))) := by
  classical
  let bdata := ArtinianLocalAlgCat.hasPullback_of_surjective f₁.base f₂.base (Or.inr hf₂)
  let bp := bdata.1
  let toBase : x₁.base.carrier →+* x.base.carrier := f₁.base.hom.toRingHom
  let surjection : x₂.base.carrier →+* x.base.carrier := f₂.base.hom.toRingHom
  let base : RingFibreProduct.Situation toBase surjection (RingHom.ker surjection) :=
    ⟨hf₂, rfl⟩
  let e : bp.obj.carrier ≃+* RingHom.pullback toBase surjection := {
    toFun := fun z =>
      (⟨z.1, (show toBase z.1.1 = surjection z.1.2 from z.2)⟩ :
        RingHom.pullback toBase surjection)
    invFun := fun z =>
      (⟨z.1, (show f₁.base.hom z.1.1 = f₂.base.hom z.1.2 from z.2)⟩ :
        bp.obj.carrier)
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
  let BtoD : x₁.base.carrier →+* x₁.fiber := algebraMap x₁.base x₁.fiber
  let A'toC' : x₂.base.carrier →+* x₂.fiber := algebraMap x₂.base x₂.fiber
  let AtoC : x.base.carrier →+* x.fiber := algebraMap x.base x.fiber
  let DtoC : x₁.fiber →+* x.fiber := f₁.map.hom
  let C'toC : x₂.fiber →+* x.fiber := f₂.map.hom
  have hD : IsPushout (CommRingCat.ofHom BtoD) (CommRingCat.ofHom toBase)
      (CommRingCat.ofHom DtoC) (CommRingCat.ofHom AtoC) := by
    simpa [BtoD, toBase, DtoC, AtoC, FlatAlgebraCategory.structureMap,
      FlatAlgebraCategory.baseMap] using f₁.cartesian
  have hC' : IsPushout (CommRingCat.ofHom A'toC') (CommRingCat.ofHom surjection)
      (CommRingCat.ofHom C'toC) (CommRingCat.ofHom AtoC) := by
    simpa [A'toC', surjection, C'toC, AtoC, FlatAlgebraCategory.structureMap,
      FlatAlgebraCategory.baseMap] using f₂.cartesian
  let P := RingHom.pullback DtoC C'toC
  have hcomm₁ : DtoC.comp BtoD = AtoC.comp toBase := congrArg CommRingCat.Hom.hom hD.w
  have hcomm₂ : C'toC.comp A'toC' = AtoC.comp surjection := congrArg CommRingCat.Hom.hom hC'.w
  have hsq : ∀ a b, toBase a = surjection b → DtoC (BtoD a) = C'toC (A'toC' b) := by
    intro a b h
    calc DtoC (BtoD a) = AtoC (toBase a) := DFunLike.congr_fun hcomm₁ a
      _ = AtoC (surjection b) := by rw [h]
      _ = _ := (DFunLike.congr_fun hcomm₂ b).symm
  let g : base.fibreProduct →+* P := RingHom.codRestrict
    ((BtoD.comp base.pullbackCone.fst.hom).prod
      (A'toC'.comp base.pullbackCone.snd.hom)) P (by
        intro r
        show DtoC (BtoD (base.pullbackCone.fst.hom r)) =
          C'toC (A'toC' (base.pullbackCone.snd.hom r))
        exact hsq _ _ (congrArg (fun q => q r) base.pullbackCone.condition))
  have hg₁ : ∀ r, (g r).1.1 = BtoD (base.pullbackCone.fst.hom r) := fun _ => rfl
  have hg₂ : ∀ r, (g r).1.2 = A'toC' (base.pullbackCone.snd.hom r) := fun _ => rfl
  let g' : bp.obj.carrier →+* P := g.comp e.toRingHom
  have hflatAlg : ∀ x : FlatAlgebraCategory.{u, w} Λ k, (algebraMap x.base x.fiber).Flat :=
    fun x => RingHom.flat_algebraMap_iff.2 x.flat
  have hflat₁ : BtoD.Flat := hflatAlg x₁
  have hflat₂ : A'toC'.Flat := hflatAlg x₂
  have hflatG : g.Flat :=
    MilnorPatching.pullback_flat_of_components base BtoD A'toC' AtoC DtoC C'toC hD hC' g
      hg₁ hg₂ hflat₁ hflat₂
  have hpushG := MilnorPatching.pullback_baseChange base BtoD A'toC' AtoC
    DtoC C'toC hD hC' g hg₁ hg₂
  have hflatG' : g'.Flat := (RingHom.Flat.comp_iff_of_bijective_right e.bijective).2 hflatG
  have hcart₁ : IsPushout (CommRingCat.ofHom g')
      (CommRingCat.ofHom (bp.fst.hom.toRingHom))
      (CommRingCat.ofHom (DtoC.pullbackFst C'toC)) (CommRingCat.ofHom BtoD) := by
    apply hpushG.1.of_iso' e.toCommRingCatIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · ext z
      all_goals
        dsimp [CommRingCat.Hom.hom, g', e, RingEquiv.toRingHom]
        simp
    · ext z
      rw [bp.fst_hom]
      rfl
    · rfl
    · rfl
  have hcart₂ : IsPushout (CommRingCat.ofHom g')
      (CommRingCat.ofHom (bp.snd.hom.toRingHom))
      (CommRingCat.ofHom (DtoC.pullbackSnd C'toC)) (CommRingCat.ofHom A'toC') := by
    apply hpushG.2.of_iso' e.toCommRingCatIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · ext z
      all_goals
        dsimp [CommRingCat.Hom.hom, g', e, RingEquiv.toRingHom]
        simp
    · ext z
      rw [bp.snd_hom]
      rfl
    · rfl
    · rfl
  let y : FlatAlgebraCategory.{u, w} Λ k :=
    { base := bp.obj
      fiber := P
      algebra := g'.toAlgebra
      flat := hflatG' }
  let p₁ : y ⟶ x₁ :=
    { base := bp.fst
      map := CommRingCat.ofHom (DtoC.pullbackFst C'toC)
      cartesian := by
        simpa [FlatAlgebraCategory.structureMap, FlatAlgebraCategory.baseMap, y,
          BtoD, A'toC', AtoC] using hcart₁ }
  let p₂ : y ⟶ x₂ :=
    { base := bp.snd
      map := CommRingCat.ofHom (DtoC.pullbackSnd C'toC)
      cartesian := by
        simpa [FlatAlgebraCategory.structureMap, FlatAlgebraCategory.baseMap, y,
          BtoD, A'toC', AtoC] using hcart₂ }
  have hcone : p₁ ≫ f₁ = p₂ ≫ f₂ := by
    apply FlatAlgebraCategory.Hom.ext
    · ext z
      exact congrArg (fun q => q.hom z) bp.isPullback.w
    · ext z
      exact z.2
  let c : PullbackCone f₁ f₂ := PullbackCone.mk p₁ p₂ hcone
  let forgetRing : ArtinianLocalAlgCat.{u, w, w} Λ k ⥤ CommRingCat.{w} := {
    obj := fun A => CommRingCat.of A.carrier
    map := fun f => CommRingCat.ofHom f.hom.toRingHom
    map_id _ := by
      ext
      rfl
    map_comp _ _ := by
      ext
      rfl }
  have hpb : ∀ {A B C : Type w} [CommRing A] [CommRing B] [CommRing C] (f : A →+* C)
      (g : B →+* C), IsPullback (CommRingCat.ofHom (f.pullbackFst g))
        (CommRingCat.ofHom (f.pullbackSnd g)) (CommRingCat.ofHom f) (CommRingCat.ofHom g) :=
    fun f g => IsPullback.of_isLimit
      (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom f) (CommRingCat.ofHom g))
  have hbase : IsPullback (forgetRing.map bp.fst) (forgetRing.map bp.snd)
      (forgetRing.map f₁.base) (forgetRing.map f₂.base) := by
    apply (hpb toBase surjection).of_iso' e.toCommRingCatIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · apply CommRingCat.hom_ext
      ext z
      show (toBase.pullbackFst surjection) (e z) = bp.fst.hom.toRingHom z
      rw [bp.fst_hom]
      rfl
    · apply CommRingCat.hom_ext
      ext z
      show (toBase.pullbackSnd surjection) (e z) = bp.snd.hom.toRingHom z
      rw [bp.snd_hom]
      rfl
    · rfl
    · rfl
  have hP := hpb DtoC C'toC
  let lift (s : PullbackCone f₁ f₂) : s.pt ⟶ y := by
    let m := bp.isPullback.lift s.fst.base s.snd.base (congrArg (fun q => q.base) s.condition)
    have hm₁ : m ≫ bp.fst = s.fst.base := bp.isPullback.lift_fst _ _ _
    have hm₂ : m ≫ bp.snd = s.snd.base := bp.isPullback.lift_snd _ _ _
    have hqcond : ∀ z : s.pt.fiber,
        DtoC (s.fst.map.hom z) = C'toC (s.snd.map.hom z) :=
      DFunLike.congr_fun (congrArg (fun q => q.map.hom) s.condition)
    let q : s.pt.fiber →+* P := RingHom.codRestrict
      (s.fst.map.hom.prod s.snd.map.hom) P hqcond
    let fZ := FlatAlgebraCategory.structureMap s.pt
    let mRing := forgetRing.map m
    have hm₁' : mRing ≫ forgetRing.map bp.fst = forgetRing.map s.fst.base := by
      simpa [Functor.map_comp] using congrArg forgetRing.map hm₁
    have hm₂' : mRing ≫ forgetRing.map bp.snd = forgetRing.map s.snd.base := by
      simpa [Functor.map_comp] using congrArg forgetRing.map hm₂
    let hpush := IsPushout.of_hasPushout fZ mRing
    let inlE := pushout.inl fZ mRing
    let inrE := pushout.inr fZ mRing
    have hflatZ : CommRingCat.flat fZ := by
      rw [CommRingCat.flat_ofHom_iff]
      simpa [fZ, FlatAlgebraCategory.structureMap] using hflatAlg s.pt
    have hflatE : CommRingCat.flat inrE :=
      MorphismProperty.pushout_inr fZ mRing hflatZ
    have hext : ∀ (x : FlatAlgebraCategory.{u, w} Λ k) (g : s.pt ⟶ x) (r : bp.obj ⟶ x.base),
        mRing ≫ forgetRing.map r = forgetRing.map g.base →
          {e : pushout fZ mRing ⟶ CommRingCat.of x.fiber //
            inlE ≫ e = CommRingCat.ofHom g.map.hom ∧
            inrE ≫ e = CommRingCat.ofHom ((algebraMap x.base x.fiber).comp r.hom.toRingHom) ∧
            IsPushout (forgetRing.map r) inrE (FlatAlgebraCategory.structureMap x) e} := by
      intro x g r hr
      have hdesc : fZ ≫ CommRingCat.ofHom g.map.hom =
          mRing ≫ CommRingCat.ofHom ((algebraMap x.base x.fiber).comp r.hom.toRingHom) := by
        calc
          _ = forgetRing.map g.base ≫ FlatAlgebraCategory.structureMap x := g.cartesian.w
          _ = mRing ≫ forgetRing.map r ≫ FlatAlgebraCategory.structureMap x := by
            rw [← Category.assoc, hr]
          _ = _ := by
            apply CommRingCat.hom_ext
            ext z
            rfl
      let e := pushout.desc (CommRingCat.ofHom g.map.hom)
        (CommRingCat.ofHom ((algebraMap x.base x.fiber).comp r.hom.toRingHom)) hdesc
      have he_inl : inlE ≫ e = CommRingCat.ofHom g.map.hom := pushout.inl_desc _ _ _
      have he_inr : inrE ≫ e =
          CommRingCat.ofHom ((algebraMap x.base x.fiber).comp r.hom.toRingHom) :=
        pushout.inr_desc _ _ _
      have hc : forgetRing.map r ≫ FlatAlgebraCategory.structureMap x = inrE ≫ e := by
        rw [he_inr]
        apply CommRingCat.hom_ext
        ext z
        rfl
      have ht : IsPushout (mRing ≫ forgetRing.map r) fZ
          (FlatAlgebraCategory.structureMap x) (inlE ≫ e) := by
        rw [hr, he_inl]
        exact g.cartesian.flip
      exact ⟨e, he_inl, he_inr, (hpush.flip.paste_horiz_iff hc).mp ht⟩
    obtain ⟨eD, heD_inl, heD_inr, h1flip⟩ := hext x₁ s.fst bp.fst hm₁'
    obtain ⟨eC', heC'_inl, heC'_inr, h2flip⟩ := hext x₂ s.snd bp.snd hm₂'
    have hcommE : eD ≫ CommRingCat.ofHom DtoC = eC' ≫ CommRingCat.ofHom C'toC := by
      apply pushout.hom_ext
      · rw [← Category.assoc, heD_inl, ← Category.assoc, heC'_inl]
        exact congrArg (fun q => q.map) s.condition
      · apply CommRingCat.hom_ext
        ext a
        rw [← Category.assoc, heD_inr, ← Category.assoc, heC'_inr]
        show DtoC (BtoD (bp.fst.hom a)) = C'toC (A'toC' (bp.snd.hom a))
        refine hsq _ _ ?_
        show f₁.base.hom (bp.fst.hom a) = f₂.base.hom (bp.snd.hom a)
        simpa only [AlgHom.comp_apply, ArtinianLocalAlgCat.comp_hom] using
          congrArg (fun f => f.hom a) bp.isPullback.w
    have hEpull : IsPullback eD eC' (CommRingCat.ofHom DtoC) (CommRingCat.ofHom C'toC) :=
      MilnorPatching.flat_baseChange_pullback hbase hflatE h1flip.flip h2flip.flip hD hC' hcommE
    let iE : pushout fZ mRing ≅ CommRingCat.of P := hEpull.isoIsPullback _ _ hP
    have hq₁ : (CommRingCat.ofHom q) ≫ CommRingCat.ofHom (DtoC.pullbackFst C'toC) =
        CommRingCat.ofHom s.fst.map.hom := by
      apply CommRingCat.hom_ext
      ext z
      rfl
    have hq₂ : (CommRingCat.ofHom q) ≫ CommRingCat.ofHom (DtoC.pullbackSnd C'toC) =
        CommRingCat.ofHom s.snd.map.hom := by
      apply CommRingCat.hom_ext
      ext z
      rfl
    have hg₁' : (CommRingCat.ofHom g') ≫ CommRingCat.ofHom (DtoC.pullbackFst C'toC) =
        CommRingCat.ofHom (BtoD.comp (bp.fst.hom.toRingHom)) := by
      apply CommRingCat.hom_ext
      ext a
      show (g (e a)).1.1 = BtoD (bp.fst.hom a)
      rw [hg₁, bp.fst_hom]
      rfl
    have hg₂' : (CommRingCat.ofHom g') ≫ CommRingCat.ofHom (DtoC.pullbackSnd C'toC) =
        CommRingCat.ofHom (A'toC'.comp (bp.snd.hom.toRingHom)) := by
      apply CommRingCat.hom_ext
      ext a
      show (g (e a)).1.2 = A'toC' (bp.snd.hom a)
      rw [hg₂, bp.snd_hom]
      rfl
    have hi₁ : inlE ≫ iE.hom = CommRingCat.ofHom q := by
      apply hP.hom_ext
      · rw [Category.assoc, hEpull.isoIsPullback_hom_fst _ _ hP, heD_inl, hq₁]
      · rw [Category.assoc, hEpull.isoIsPullback_hom_snd _ _ hP, heC'_inl, hq₂]
    have hi₂ : inrE ≫ iE.hom = CommRingCat.ofHom g' := by
      apply hP.hom_ext
      · rw [Category.assoc, hEpull.isoIsPullback_hom_fst _ _ hP, heD_inr, hg₁']
      · rw [Category.assoc, hEpull.isoIsPullback_hom_snd _ _ hP, heC'_inr, hg₂']
    have hcart : IsPushout fZ mRing (CommRingCat.ofHom q) (CommRingCat.ofHom g') :=
      hpush.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) iE rfl rfl hi₁ hi₂
    exact ⟨m, CommRingCat.ofHom q, by
      simpa [FlatAlgebraCategory.structureMap, FlatAlgebraCategory.baseMap, y,
        fZ, mRing, forgetRing] using hcart⟩
  have hfac₁ : ∀ s : PullbackCone f₁ f₂, lift s ≫ p₁ = s.fst := by
    intro s
    apply FlatAlgebraCategory.Hom.ext
    · exact bp.isPullback.lift_fst _ _ _
    · apply CommRingCat.hom_ext
      rfl
  have hfac₂ : ∀ s : PullbackCone f₁ f₂, lift s ≫ p₂ = s.snd := by
    intro s
    apply FlatAlgebraCategory.Hom.ext
    · exact bp.isPullback.lift_snd _ _ _
    · apply CommRingCat.hom_ext
      rfl
  have hlim : IsLimit c := PullbackCone.IsLimit.mk hcone lift hfac₁ hfac₂ (by
    intro s m hm₁ hm₂
    apply FlatAlgebraCategory.Hom.ext
    · apply bp.isPullback.hom_ext
      · exact congrArg (fun q => q.base) (hm₁.trans (hfac₁ s).symm)
      · exact congrArg (fun q => q.base) (hm₂.trans (hfac₂ s).symm)
    · apply hP.hom_ext
      · exact congrArg (fun q => q.map) (hm₁.trans (hfac₁ s).symm)
      · exact congrArg (fun q => q.map) (hm₂.trans (hfac₂ s).symm))
  have hlimBase : IsLimit (c.map (FlatAlgebraCategory.projection (Λ := Λ) (k := k))) := by
    let d : PullbackCone f₁.base f₂.base :=
      PullbackCone.mk bp.fst bp.snd bp.isPullback.w
    have hd : IsLimit d := bp.isPullback.isLimit
    let i : d ≅ c.map (FlatAlgebraCategory.projection (Λ := Λ) (k := k)) :=
      PullbackCone.ext (Iso.refl _) rfl rfl
    exact IsLimit.ofIsoLimit hd i
  exact ⟨c, ⟨hlim⟩, ⟨hlimBase⟩⟩

/-- Flat algebras over Artinian local bases satisfy the Rim–Schlessinger condition. -/
@[stacks 0DY2 "Rim–Schlessinger condition"]
theorem flatAlgebraCategory_projection_satisfiesRS
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    SatisfiesRS (FlatAlgebraCategory.projection (Λ := Λ) (k := k)) := by
  refine ⟨flatAlgebraCategory_projection_isCofiberedInGroupoids, ?_⟩
  intro x₁ x₂ x f₁ f₂ hf₂
  exact flatAlgebraCategory_pullback_exists f₁ f₂ hf₂

/-- Deformations of any `k`-algebra form a deformation category. -/
@[stacks 0DY2 "deformation category"]
theorem ringDeformationCategory_isDeformationCategory
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] :
    IsDeformationCategory
      (objectsOverFunctor (FlatAlgebraCategory.projection (Λ := Λ) (k := k))
        (residueFieldAlgebra (Λ := Λ) (k := k) P)) :=
  isDeformationCategory_objectsOverFunctor_of_baseIso
    (FlatAlgebraCategory.projection (Λ := Λ) (k := k))
    flatAlgebraCategory_projection_satisfiesRS
    (residueFieldAlgebra (Λ := Λ) (k := k) P) residueFieldBaseIso

end Deformation.Examples

end
