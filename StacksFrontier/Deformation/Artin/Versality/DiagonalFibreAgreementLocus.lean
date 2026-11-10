module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalLocus
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibreSetoid
public import StacksFrontier.Deformation.Artin.Versality.SetoidGeneralization

/-!
# Agreement loci in the fibres of the diagonal

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `V` be an
object of that site and `y` an object of `𝒳 × 𝒳` over `V`. An object of the 2-fibre product
`𝒲 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` over a scheme `T` over `V` amounts to an isomorphism
`y₁|_T ⟶ y₂|_T` (`CategoryTheory.TwoFibreProductOver.sectOf`). For two objects of `𝒲`, over `U`
and `U'`, the locus of `U ×_V U'` where the two isomorphisms agree is the locus where the
automorphism `s₁ ≫ s₂⁻¹` of `y₁|_{U ×_V U'}` is trivial. If the second diagonal of `𝒳` is
representable by algebraic spaces and `𝒳` is limit preserving, this locus is a monomorphism of
schemes locally of finite type
(`AlgebraicGeometry.Stack.exists_mono_locallyOfFiniteType_trivialLocus`), so `𝒲` has agreement
loci in the sense of `Deformation.Artin.HasAgreementLoci`.

## Main results

* `Deformation.Artin.hasAgreementLoci_diagonalFibre`: the fibres of the diagonal have agreement
  loci locally of finite type.

## References

* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
* [Stacks Project, Tag 0CXV](https://stacks.math.columbia.edu/tag/0CXV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.TwoFibreProductOver CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace Deformation.Artin

universe u

attribute [local implicit_reducible] _root_.CategoryTheory.TwoFibreProductOver.fst
  _root_.CategoryTheory.TwoFibreProductOver.snd
  _root_.CategoryTheory.TwoFibreProductOver.diagonal

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (AlgebraicGeometry.BigFppfOver B S hS))
  (V : AlgebraicGeometry.BigFppfOver B S hS)
  (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
  (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)

include hy in
/-- **Agreement loci in the fibres of the diagonal.** If the second diagonal of `𝒳` is
representable by algebraic spaces and `𝒳` is limit preserving, then the 2-fibre product
`(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`, over the big fppf site of `V`, has agreement loci locally of
finite type. -/
theorem hasAgreementLoci_diagonalFibre
    (h1 : AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces B S hS
      (AlgebraicGeometry.Stack.relativeDiagonalBasedFunctor B S hS 𝒳
        (CatFiberedInGroupoids.product 𝒳 𝒳)
        (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳)))
    (h3 : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳) :
    HasAgreementLoci B V.left.1 V.left.2
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor) := by
  classical
  intro x ξ' hxl _
  have hp : 𝒳.val.p.IsFiberedInGroupoids := 𝒳.isFiberedInGroupoids
  let : 𝒳.val.p.IsFibered := hp.isFibered
  let VV := AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2
  have hY₁ : Y₁' y ⋙ 𝒳.val.p = Over.map V.hom := h1' hy
  have hY₂ : Y₂' y ⋙ 𝒳.val.p = Over.map V.hom := h2' hy
  let fU : VV.obj x.x ⟶ V.left.1 := B.inclusion.map x.x.hom
  let fU' : VV.obj ξ'.x ⟶ V.left.1 := B.inclusion.map ξ'.x.hom
  have hPc : B.Contains (pullback fU fU') :=
    Scheme.size_pullback_lt fU fU' x.x.left.2 ξ'.x.left.2
  let P : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 :=
    Over.mk (ObjectProperty.homMk (X := B.obj hPc) (Y := B.obj V.left.2) (pullback.fst fU fU' ≫ fU))
  let pr₁ : P ⟶ x.x := Over.homMk (ObjectProperty.homMk (pullback.fst fU fU')) (by
    apply ObjectProperty.hom_ext
    rfl)
  let pr₂ : P ⟶ ξ'.x := Over.homMk (ObjectProperty.homMk (pullback.snd fU fU')) (by
    apply ObjectProperty.hom_ext
    exact pullback.condition.symm)
  let σx : VertHom 𝒳.val.p (Over.map V.hom) (Y₁' y) (Y₂' y) x.x :=
    ⟨sectOf x, isHomLift_sectOf hy x⟩
  let σξ : VertHom 𝒳.val.p (Over.map V.hom) (Y₁' y) (Y₂' y) ξ'.x :=
    ⟨sectOf ξ', isHomLift_sectOf hy ξ'⟩
  let s₁ := VertHom.restrict hp hY₁ hY₂ pr₁ σx
  let s₂ := VertHom.restrict hp hY₁ hY₂ pr₂ σξ
  have := isIso_vertHom P s₂ hp
  let θ : (Y₁' y).obj P ⟶ (Y₁' y).obj P := s₁.1 ≫ CategoryTheory.inv s₂.1
  have hθ : 𝒳.val.p.map θ = 𝟙 _ := by
    have := s₁.2
    have := s₂.2
    have : 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj P)) (CategoryTheory.inv s₂.1) :=
      IsHomLift.lift_id_inv_isIso 𝒳.val.p _ s₂.1
    have : 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj P)) θ := by
      have : 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj P) ≫ 𝟙 ((Over.map V.hom).obj P)) θ :=
        inferInstance
      simpa using this
    rw [IsHomLift.fac' 𝒳.val.p (𝟙 ((Over.map V.hom).obj P)) θ]
    simp
  obtain ⟨Z, ι, hι, hιl, -, hZ⟩ :=
    AlgebraicGeometry.Stack.exists_mono_locallyOfFiniteType_trivialLocus B S hS 𝒳 h1 h3
      ((Y₁' y).obj P) θ hθ
  have hPobj : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (𝒳.val.p.obj ((Y₁' y).obj P)) = pullback fU fU' :=
    congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (Functor.congr_obj hY₁ P)
  let ι' : Z ⟶ pullback fU fU' := ι ≫ eqToHom hPobj
  have : Mono ι' := inferInstance
  have : LocallyOfFiniteType ι' := inferInstance
  have : LocallyOfFiniteType fU := hxl
  have key : ∀ (T : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2) (h : T ⟶ P),
      (∃ g : VV.obj T ⟶ Z, g ≫ ι' = VV.map h) ↔
        VertHom.restrict hp hY₁ hY₂ h s₁ = VertHom.restrict hp hY₁ hY₂ h s₂ := by
    intro T h
    have hc := hZ ((Y₁' y).obj T) ((Y₁' y).map h)
    have hTobj : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        (𝒳.val.p.obj ((Y₁' y).obj T)) = VV.obj T :=
      congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (Functor.congr_obj hY₁ T)
    have hmap : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝒳.val.p.map
        ((Y₁' y).map h)) = eqToHom hTobj ≫ VV.map h ≫ eqToHom hPobj.symm := by
      have := Functor.congr_hom hY₁ h
      simp only [Functor.comp_map] at this
      rw [this]
      simp
      rfl
    have hleft : (∃ g : VV.obj T ⟶ Z, g ≫ ι' = VV.map h) ↔
        (∃ g : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
          (𝒳.val.p.obj ((Y₁' y).obj T)) ⟶ Z,
          g ≫ ι = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
            (𝒳.val.p.map ((Y₁' y).map h))) := by
      rw [hmap]
      constructor
      · rintro ⟨g, hg⟩
        refine ⟨eqToHom hTobj ≫ g, ?_⟩
        rw [← hg]
        simp [ι']
      · rintro ⟨g, hg⟩
        refine ⟨eqToHom hTobj.symm ≫ g, ?_⟩
        simp [ι', reassoc_of% hg]
    rw [hleft, hc]
    constructor
    · intro h'
      apply VertHom.ext
      have e₁ := VertHom.restrict_fac hp hY₁ hY₂ h s₁
      have e₂ := VertHom.restrict_fac hp hY₁ hY₂ h s₂
      have : 𝒳.val.p.IsHomLift ((Over.map V.hom).map h) ((Y₂' y).map h) :=
        VertHom.isHomLift_map hY₂ h
      have : 𝒳.val.p.IsStronglyCartesian ((Over.map V.hom).map h) ((Y₂' y).map h) :=
        hp.isStronglyCartesian_homLift _ _
      have hr₁ := (VertHom.restrict hp hY₁ hY₂ h s₁).2
      have hr₂ := (VertHom.restrict hp hY₁ hY₂ h s₂).2
      refine Functor.IsStronglyCartesian.ext 𝒳.val.p ((Over.map V.hom).map h) ((Y₂' y).map h)
        (𝟙 _) ?_
      rw [e₁, e₂]
      have h'' : (Y₁' y).map h ≫ s₁.1 ≫ CategoryTheory.inv s₂.1 = (Y₁' y).map h := h'
      rw [← cancel_mono s₂.1] at h''
      simpa using h''
    · intro h'
      have e₁ := VertHom.restrict_fac hp hY₁ hY₂ h s₁
      have e₂ := VertHom.restrict_fac hp hY₁ hY₂ h s₂
      change (Y₁' y).map h ≫ s₁.1 ≫ CategoryTheory.inv s₂.1 = (Y₁' y).map h
      rw [← Category.assoc, ← e₁, h', e₂, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine ⟨Z, ι' ≫ pullback.fst fU fU', ι' ≫ pullback.snd fU fU', ⟨?_, ?_, ?_, ?_⟩, inferInstance⟩
  · change (ι' ≫ pullback.fst fU fU') ≫ fU = (ι' ≫ pullback.snd fU fU') ≫ fU'
    simp only [Category.assoc, pullback.condition]
  · intro T g g' h₁ h₂
    apply (cancel_mono ι').mp
    apply pullback.hom_ext
    · simpa only [Category.assoc] using h₁
    · simpa only [Category.assoc] using h₂
  · intro z d d'
    have e₁ := congrArg B.inclusion.map (Over.w d.a)
    have e₂ := congrArg B.inclusion.map (Over.w d'.a)
    rw [B.inclusion.map_comp] at e₁ e₂
    have hcomm : VV.map d.a ≫ fU = VV.map d'.a ≫ fU' := e₁.trans e₂.symm
    let h : z.x ⟶ P := Over.homMk (ObjectProperty.homMk (pullback.lift _ _ hcomm)) (by
      apply ObjectProperty.hom_ext
      change pullback.lift _ _ hcomm ≫ pullback.fst fU fU' ≫ fU = _
      rw [pullback.lift_fst_assoc]
      exact e₁)
    have hh₁ : h ≫ pr₁ = d.a := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact pullback.lift_fst _ _ _
    have hh₂ : h ≫ pr₂ = d'.a := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact pullback.lift_snd _ _ _
    have hagree : VertHom.restrict hp hY₁ hY₂ h s₁ = VertHom.restrict hp hY₁ hY₂ h s₂ := by
      change VertHom.restrict hp hY₁ hY₂ h
          (VertHom.restrict hp hY₁ hY₂ pr₁ ⟨sectOf x, isHomLift_sectOf hy x⟩) =
        VertHom.restrict hp hY₁ hY₂ h
          (VertHom.restrict hp hY₁ hY₂ pr₂ ⟨sectOf ξ', isHomLift_sectOf hy ξ'⟩)
      let σz : VertHom 𝒳.val.p (Over.map V.hom) (Y₁' y) (Y₂' y) z.x :=
        ⟨sectOf z, isHomLift_sectOf hy z⟩
      calc VertHom.restrict hp hY₁ hY₂ h (VertHom.restrict hp hY₁ hY₂ pr₁ σx)
          = VertHom.restrict hp hY₁ hY₂ (h ≫ pr₁) σx :=
            (VertHom.restrict_comp hp hY₁ hY₂ h pr₁ σx).symm
        _ = VertHom.restrict hp hY₁ hY₂ d.a σx :=
            congrArg (fun k => VertHom.restrict hp hY₁ hY₂ k σx) hh₁
        _ = σz := (VertHom.restrict_uniq hp hY₁ hY₂ d.a σx σz (sectOf_naturality d)).symm
        _ = VertHom.restrict hp hY₁ hY₂ d'.a σξ :=
            VertHom.restrict_uniq hp hY₁ hY₂ d'.a σξ σz (sectOf_naturality d')
        _ = VertHom.restrict hp hY₁ hY₂ (h ≫ pr₂) σξ :=
            congrArg (fun k => VertHom.restrict hp hY₁ hY₂ k σξ) hh₂.symm
        _ = VertHom.restrict hp hY₁ hY₂ h (VertHom.restrict hp hY₁ hY₂ pr₂ σξ) :=
            VertHom.restrict_comp hp hY₁ hY₂ h pr₂ σξ
    obtain ⟨g, hg⟩ := (key z.x h).mpr hagree
    refine ⟨g, ?_, ?_⟩
    · rw [← Category.assoc, hg]
      change VV.map h ≫ VV.map pr₁ = _
      rw [← VV.map_comp, hh₁]
      rfl
    · rw [← Category.assoc, hg]
      change VV.map h ≫ VV.map pr₂ = _
      rw [← VV.map_comp, hh₂]
      rfl
  · intro T g hg
    let h : T ⟶ P := Over.homMk (ObjectProperty.homMk (g ≫ ι')) (by
      apply ObjectProperty.hom_ext
      change (g ≫ ι') ≫ pullback.fst fU fU' ≫ fU = _
      simp only [Category.assoc]
      exact hg)
    let m : VertHom 𝒳.val.p (Over.map V.hom) (Y₁' y) (Y₂' y) T :=
      VertHom.restrict hp hY₁ hY₂ (h ≫ pr₁) σx
    let zT := objOf hy T m hp
    have hm : m = VertHom.restrict hp hY₁ hY₂ (h ≫ pr₂) σξ :=
      (VertHom.restrict_comp hp hY₁ hY₂ h pr₁ σx).trans
        (((key T h).mp ⟨g, rfl⟩).trans (VertHom.restrict_comp hp hY₁ hY₂ h pr₂ σξ).symm)
    have hz₁ : sectOf zT ≫ (Y₂' y).map (h ≫ pr₁) = (Y₁' y).map (h ≫ pr₁) ≫ σx.1 :=
      (congrArg (· ≫ (Y₂' y).map (h ≫ pr₁)) (sectOf_objOf hy T m hp)).trans
        (VertHom.restrict_fac hp hY₁ hY₂ _ _)
    have hz₂ : sectOf zT ≫ (Y₂' y).map (h ≫ pr₂) = (Y₁' y).map (h ≫ pr₂) ≫ σξ.1 :=
      (congrArg (· ≫ (Y₂' y).map (h ≫ pr₂)) ((sectOf_objOf hy T m hp).trans
        (congrArg Subtype.val hm))).trans (VertHom.restrict_fac hp hY₁ hY₂ _ _)
    obtain ⟨d, hd⟩ := exists_hom_of_sectOf hp hy (A := zT) (B := x) (h ≫ pr₁) hz₁
    obtain ⟨d', hd'⟩ := exists_hom_of_sectOf hp hy (A := zT) (B := ξ') (h ≫ pr₂) hz₂
    refine ⟨zT, d, d', rfl, ?_, ?_⟩
    · change 𝟙 _ ≫ VV.map d.a = _
      rw [hd, Category.id_comp]
      exact (VV.map_comp h pr₁).trans (Category.assoc _ _ _)
    · change 𝟙 _ ≫ VV.map d'.a = _
      rw [hd', Category.id_comp]
      exact (VV.map_comp h pr₂).trans (Category.assoc _ _ _)

end Deformation.Artin

end
