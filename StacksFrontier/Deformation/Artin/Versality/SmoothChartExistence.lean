module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingSetoidRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSliceAtlas
public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.Artin.FormalObject.BaseContains
public import StacksFrontier.Deformation.Artin.FormalObject.RealizationVersality
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation
public import StacksFrontier.Deformation.Artin.Versality.SmoothChartVersality
public import StacksFrontier.Deformation.CofiberedPresentation.Criteria
public import StacksFrontier.Deformation.Schlessinger.VersalExistence

/-!
# A smooth chart through a finite type point (Stacks 07XY)

-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `0`-th infinitesimal thickening of the closed point of a local ring maps every point to
the closed point. -/
theorem adicThickeningι_zero_apply (R : Type u) [CommRing R] [IsLocalRing R]
    (z : Spec (.of (R ⧸ maximalIdeal R ^ (0 + 1)))) :
    adicThickeningι R (maximalIdeal R) 0 z = closedPoint R := by
  apply PrimeSpectrum.ext
  change Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) z.asIdeal = maximalIdeal R
  refine ((maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
  intro a ha
  have : Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)) a = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
    exact ha
  change Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)) a ∈ z.asIdeal
  rw [this]
  exact z.asIdeal.zero_mem

/-- The comparison isomorphism between the spectra of two equal complete local bases preserves
the closed point. -/
theorem eqToHom_spec_formalBase_closedPoint {A₁ A₂ : FormalBase S} (h : A₁ = A₂) :
    (eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) h)) (closedPoint A₁.R) =
      closedPoint A₂.R := by
  subst h
  rfl

/-- **A versal object over a finite type neighbourhood.** Let `𝒳` be a category fibred in
groupoids over the big fppf site of a locally Noetherian scheme `S`, satisfying (RS), whose
tangent spaces at the point `x₀ : Spec k ⟶ 𝒳` are finite dimensional, whose formal objects are
effective and which is limit preserving on objects, and let `Spec Λ ⊆ S` be an affine open
through which `Spec k ⟶ S` factors with `Λ → k` finite. If the local ring of `S` at the image of
`Spec k` is a G-ring, there are a scheme `U` of finite type over `S`, an object `x` of `𝒳` over
`U` versal at a finite type point `u₀` of `U`, and an arrow `x₀ ⟶ x`. -/
theorem exists_isVersalAt_of_affineChart [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ] (x₀ : 𝒳.val.obj)
    (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (htangent :
      letI := (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀).category
      ∀ hD : IsDeformationCategory
          (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection,
        letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
            (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀
              hx₀).projection).p) := ⟨hD.predeformation⟩
        letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
            (BasedCategory.ofFunctor
              (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
            hD.predeformation.cofibered))) := ⟨tangentConditionS2 hD⟩
        FiniteDimensional k (tangentSpaceArtinian Λ k (isomorphismClasses
          (BasedCategory.ofFunctor
            (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
          hD.predeformation.cofibered)))
    (heff : ∀ ξ : FormalObject B S hS 𝒳.val.p,
      FormalObject.IsEffective B S hS 𝒳.val.p 𝒳.property ξ)
    (hG : IsGRing (S.presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) (closedPoint k))))
    (hlimit : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (Approximation.baseFiberedCategory B S hS) (Approximation.structureMorphism B S hS 𝒳)) :
    ∃ (U : Over S) (u₀ : U.left) (V : BigFppfOver B S hS)
      (_ : (Over.post B.inclusion).obj V = U) (x : 𝒳.val.p.Fiber V)
      (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x.1 = U),
      LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom ∧ IsFiniteTypePoint u₀ ∧
      IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x.1 hx ∧
      ∃ a : x₀ ⟶ x.1, ∀ w, (((𝒳.val.p ⋙ Over.post B.inclusion).map a).left ≫
        eqToHom (congrArg Over.left hx)) w = u₀ := by
  have : IsLocallyNoetherian (Spec (.of Λ)) := isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  let p := 𝒳.val.p
  have hp : p.IsFiberedInGroupoids := 𝒳.isFiberedInGroupoids
  let q := p ⋙ Over.post B.inclusion
  let D := predeformationCategory iΛ q x₀ hx₀
  let := D.category
  have hD : IsDeformationCategory D.projection :=
    isDeformationCategory_predeformationCategory B S hS p hp hRS iΛ x₀ hx₀ hfinite.1 hfinite.2
  let 𝓕 := BasedCategory.ofFunctor D.projection
  obtain ⟨ξ, hξ⟩ := Deformation.exists_versalFormalObject Λ k 𝓕 hD.predeformation
    (Deformation.schlessingerConditionS1_of_satisfiesRS hD.satisfiesRS)
    (Deformation.schlessingerConditionS2_of_satisfiesRS hD.satisfiesRS) (htangent hD)
  let ξ' := FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ
  have hA : B.Contains (Spec (.of ξ'.base.R)) := ξ'.contains_spec_base
  obtain ⟨y, hy, ⟨R⟩⟩ :=
    FormalObject.exists_realization_of_isEffective (ξ := ξ') (hA := hA) hp (heff ξ')
  let s := ξ'.base.toS (closedPoint ξ'.base.R)
  let algA : Algebra (S.presheaf.stalk s) ξ'.base.R :=
    (Scheme.stalkClosedPointTo ξ'.base.toS).hom.toAlgebra
  have hΛ : Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) ξ'.base.R)) ≫
      S.fromSpecStalk s = ξ'.base.toS :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'.base.toS
  have hver := isVersal_stalk_ofPredeformation_of_realization B S hS p hp iΛ hx₀ hfinite ξ hξ R
    (algA := algA) s rfl hΛ
  have hring : algebraMap Λ k = (completeResidueMap ξ.base).comp (algebraMap Λ ξ.base) := by
    ext a
    change _ = ξ.base.residueEquiv (algebraMap Λ (ResidueField ξ.base) a)
    exact (ξ.base.residueEquiv.commutes a).symm
  have : IsLocalHom (completeResidueMap ξ.base) := by
    unfold completeResidueMap
    exact RingHom.isLocalHom_comp _ _
  have h1 : Spec.map (CommRingCat.ofHom (completeResidueMap ξ.base)) (closedPoint k) =
      closedPoint ξ.base := Spec_closedPoint (f := CommRingCat.ofHom (completeResidueMap ξ.base))
  have hs : s = (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) (closedPoint k) := by
    calc s = (Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ)
          (Spec.map (CommRingCat.ofHom (completeResidueMap ξ.base)) (closedPoint k)) := by
          rw [h1]; rfl
      _ = (Spec.map (CommRingCat.ofHom (completeResidueMap ξ.base)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ) (closedPoint k) := rfl
      _ = _ := by conv_rhs => rw [hring, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  obtain ⟨U, u₀, V, hV, x, hx, hlft, hqc, hu₀, -, hversal, xR, ⟨e⟩, r, eR, -, hr⟩ :=
    exists_finiteType_versal_approximation B S hS 𝒳 ξ' (heff ξ') s rfl (hs ▸ hG) hlimit
      (S.fromSpecStalk s) rfl hΛ hver
  obtain ⟨r', hbase, -, -, -, hsch⟩ := (approximationFunctorData B S hS p hp).2
  have C1 := hsch xR 0
  let T := BigFppfOver.toScheme B S hS
  let G := (approximationFunctorData B S hS p hp).1
  let ι₀ := adicThickeningι (G.obj xR).base.R (maximalIdeal (G.obj xR).base.R) 0 ≫
    eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hbase xR))
  let ψ := Spec.map (CommRingCat.ofHom eR.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
      (Scheme.completedLocalRing U.left u₀))) ≫ U.left.fromSpecStalk u₀
  have h1 : T.map (p.map (r' xR 0)) = T.map (eqToHom ((G.obj xR).level_eq 0)) ≫ ι₀ ≫
      T.map (eqToHom (chosenBase_eq B S hS p xR.obj).symm) := by
    calc T.map (p.map (r' xR 0)) = T.map (eqToHom ((G.obj xR).level_eq 0)) ≫
          T.map (eqToHom ((G.obj xR).level_eq 0).symm ≫ p.map (r' xR 0) ≫
            eqToHom (chosenBase_eq B S hS p xR.obj)) ≫
          T.map (eqToHom (chosenBase_eq B S hS p xR.obj).symm) := by
          simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_refl,
            Category.comp_id, eqToHom_trans_assoc, Category.id_comp]
      _ = _ := by rw [C1]; rfl
  have hr' : T.map (eqToHom (chosenBase_eq B S hS p xR.obj).symm) ≫ T.map (p.map r) ≫
      eqToHom (congrArg Over.left hx) =
      ψ := by
    rw [← Category.assoc, ← Functor.map_comp]
    exact hr
  let a₀ : x₀ ⟶ ξ'.level 0 := (D.objects (ξ.level 0)).arrow
  refine ⟨U, u₀, V, hV, x, hx, hlft, hqc, hu₀, hversal, a₀ ≫ e.hom.app 0 ≫ r' xR 0 ≫ r, ?_⟩
  intro w
  have hmain : T.map (p.map (a₀ ≫ e.hom.app 0 ≫ r' xR 0 ≫ r)) ≫ eqToHom (congrArg Over.left hx) =
      T.map (p.map (a₀ ≫ e.hom.app 0)) ≫ T.map (eqToHom ((G.obj xR).level_eq 0)) ≫ ι₀ ≫ ψ := by
    rw [← hr']
    simp only [Functor.map_comp, Category.assoc]
    rw [h1]
    simp only [Category.assoc]
    rfl
  change (T.map (p.map (a₀ ≫ e.hom.app 0 ≫ r' xR 0 ≫ r)) ≫ eqToHom (congrArg Over.left hx)) w =
    u₀
  rw [hmain]
  have := hlft
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  have : IsLocalHom (CommRingCat.ofHom eR.toRingHom).hom :=
    ⟨fun a ha => by simpa using ha.map eR.symm.toRingHom⟩
  have : IsLocalHom (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
      (Scheme.completedLocalRing U.left u₀))).hom :=
    inferInstanceAs (IsLocalHom (algebraMap (U.left.presheaf.stalk u₀)
      (Scheme.completedLocalRing U.left u₀)))
  have hΨ : ∀ z, (ι₀ ≫ ψ) z = u₀ := by
    intro z
    have hz1 := adicThickeningι_zero_apply (G.obj xR).base.R z
    have hz2 := eqToHom_spec_formalBase_closedPoint S (hbase xR)
    have hz3 : Spec.map (CommRingCat.ofHom eR.toRingHom)
        (closedPoint (chosenBase B S hS p xR.obj).R) =
        closedPoint (Scheme.completedLocalRing U.left u₀) :=
      Spec_closedPoint (f := CommRingCat.ofHom eR.toRingHom)
    have hz4 : Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
          (Scheme.completedLocalRing U.left u₀)))
          (closedPoint (Scheme.completedLocalRing U.left u₀)) =
        closedPoint (U.left.presheaf.stalk u₀) :=
      Spec_closedPoint (f := CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
          (Scheme.completedLocalRing U.left u₀)))
    calc _ = U.left.fromSpecStalk u₀ (Spec.map (CommRingCat.ofHom (algebraMap
          (U.left.presheaf.stalk u₀) (Scheme.completedLocalRing U.left u₀)))
          (Spec.map (CommRingCat.ofHom eR.toRingHom)
          ((eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hbase xR)))
          (adicThickeningι (G.obj xR).base.R (maximalIdeal (G.obj xR).base.R) 0 z)))) := rfl
      _ = u₀ := by rw [hz1, hz2, hz3, hz4, Scheme.fromSpecStalk_closedPoint]
  exact hΨ _

/-- The image of a finite type point under an open immersion is a finite type point. -/
theorem isFiniteTypePoint_map_of_isOpenImmersion {T T' : Scheme.{u}} (f : T' ⟶ T)
    [IsOpenImmersion f] (t : T') (ht : IsFiniteTypePoint t) : IsFiniteTypePoint (f t) := by
  have hres : Spec.map (f.residueFieldMap t) ≫ T.fromSpecResidueField (f t) =
      T'.fromSpecResidueField t ≫ f :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f t
  have : IsIso (Spec.map (f.residueFieldMap t)) := inferInstance
  have h : T.fromSpecResidueField (f t) =
      inv (Spec.map (f.residueFieldMap t)) ≫ T'.fromSpecResidueField t ≫ f := by
    rw [← hres, IsIso.inv_hom_id_assoc]
  have := ht.1
  have := ht.2
  rw [IsFiniteTypePoint, h]
  exact ⟨inferInstance, inferInstance⟩

/-- The comparison isomorphism between equal schemes followed by its inverse is the identity on
points. -/
theorem eqToHom_apply_eqToHom_symm {X Y : Scheme.{u}} (h : X = Y) (t : Y) :
    (eqToHom h) ((eqToHom h.symm) t) = t := by
  subst h
  rfl

/-- **Versality is local for open immersions.** If an arrow `x' ⟶ x` of a category fibred in
groupoids over the big fppf site lies over an open immersion `j`, then `x'` is versal at a point
`u` exactly when `x` is versal at `j u` (`Deformation.Artin.isVersalAt_iff_restrict`). -/
theorem isVersalAt_iff_of_isOpenImmersion_map
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) {x x' : 𝒳.val.obj}
    (ρ : x' ⟶ x) (hj : IsOpenImmersion (B.inclusion.map (𝒳.val.p.map ρ).left))
    (u : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x').left) :
    IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x')
      (𝒳.val.p ⋙ Over.post B.inclusion) u x' rfl ↔
    IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x)
      (𝒳.val.p ⋙ Over.post B.inclusion) ((B.inclusion.map (𝒳.val.p.map ρ).left) u) x rfl := by
  let q := 𝒳.val.p ⋙ Over.post B.inclusion
  let U := q.obj x
  let U' := q.obj x'
  let j : U'.left ⟶ U.left := B.inclusion.map (𝒳.val.p.map ρ).left
  have hρ : schemeMap q rfl rfl ρ = j := by
    simp only [schemeMap, eqToHom_refl, Category.id_comp]
    exact Category.comp_id _
  have hjU : j ≫ U.hom = U'.hom := comp_hom_eq_of_schemeMap_eq B S hS 𝒳.val.p rfl rfl ρ j hρ
  let i := S.affineOpenCover.idx (basePoint U (j.base u))
  let iΛ : Spec (.of (S.affineOpenCover.X i : Type u)) ⟶ S := S.affineOpenCover.f i
  have hcov : basePoint U (j.base u) ∈ Set.range iΛ.base := S.affineOpenCover.covers _
  have hres : Spec.map (j.residueFieldMap u) ≫ U.left.fromSpecResidueField (j.base u) =
      U'.left.fromSpecResidueField u ≫ j :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField j u
  have hcomp : U'.left.fromSpecResidueField u ≫ U'.hom =
      Spec.map (j.residueFieldMap u) ≫ (U.left.fromSpecResidueField (j.base u) ≫ U.hom) := by
    rw [← hjU, ← Category.assoc, ← hres, Category.assoc]
  have H : Set.range (U.left.fromSpecResidueField (j.base u) ≫ U.hom).base ⊆
      Set.range iΛ.base := by
    rintro _ ⟨s, rfl⟩
    have hs : s = IsLocalRing.closedPoint (U.left.residueField (j.base u)) :=
      Subsingleton.elim (α := Spec (U.left.residueField (j.base u))) _ _
    rw [hs]
    exact hcov
  have H' : Set.range (U'.left.fromSpecResidueField u ≫ U'.hom).base ⊆ Set.range iΛ.base := by
    rw [hcomp, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (Set.range_comp_subset_range _ _).trans H
  exact isVersalAt_iff_restrict B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids iΛ rfl rfl ρ j hj hρ u
    H H'

/-- **A smooth chart through a versal point.** Let `𝒳` be a category fibred in groupoids over the
big fppf site of a locally Noetherian scheme `S`, satisfying (RS) and openness of versality, limit
preserving, and such that the 1-morphism `y : (Sch/V)_{fppf} ⟶ 𝒳` of every object is representable
by algebraic spaces. Let `x` be an object of `𝒳` over a scheme `U` locally of finite type over `S`,
versal at a finite type point `u₀`, and let `a : x₀ ⟶ x` be an arrow lying over a morphism whose
image is `u₀`. Then there is an object `y` of `𝒳` over a scheme of finite type over `S` such that
`y : (Sch/V)_{fppf} ⟶ 𝒳` is smooth, together with an arrow `x₀ ⟶ y`. -/
theorem exists_isRelativelySmooth_of_isVersalAt [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hrep : ∀ (V : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber V),
      Stack.IsRepresentableByAlgebraicSpaces B S hS (Stack.objectMorphism B S hS 𝒳 y).hom)
    (hlimit : IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hopen : ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : 𝒳.val.obj) (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ → IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧ ∀ u : U.left, u ∈ W.1 → IsFiniteTypePoint u →
          IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u x hx)
    (x : 𝒳.val.obj) (hU : LocallyOfFiniteType ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom)
    (u₀ : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left) (hu₀ : IsFiniteTypePoint u₀)
    (hversal : IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x)
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x rfl)
    {x₀ : 𝒳.val.obj} (a : x₀ ⟶ x)
    (ha : ∀ w, ((𝒳.val.p ⋙ Over.post B.inclusion).map a).left w = u₀) :
    ∃ (V : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber V),
      LocallyOfFiniteType (B.inclusion.map V.hom) ∧ QuasiCompact (B.inclusion.map V.hom) ∧
      Stack.IsRelativelySmooth B S hS (Stack.objectMorphism B S hS 𝒳 y) ∧
      Nonempty (x₀ ⟶ y.1) := by
  let p := 𝒳.val.p
  have hp : p.IsFiberedInGroupoids := 𝒳.isFiberedInGroupoids
  let q := p ⋙ Over.post B.inclusion
  obtain ⟨W, hu₀W, hW⟩ := hopen (q.obj x) hU x rfl u₀ hu₀ hversal
  obtain ⟨W', hW'aff, hu₀W', hW'W⟩ := exists_isAffineOpen_mem_and_subset (U := W) hu₀W
  let T := p.obj x
  let g := BigFppfOver.openSubHom B S hS T W'
  let c := Functor.TwoYoneda.choiceOfPullbacks p hp
  let xf : p.Fiber T := Functor.Fiber.mk (a := x) rfl
  let y := c.obj g xf
  let ρ : y.1 ⟶ x := c.map g xf
  have hρ : p.IsHomLift g ρ := (c.isStronglyCartesian g xf).toIsHomLift
  have hy : (B.inclusion.obj (p.obj y.1).left) =
      (B.inclusion.obj (BigFppfOver.openSubObj B S hS T W').left) :=
    congrArg (fun T : BigFppfOver B S hS => B.inclusion.obj T.left) y.2
  have hmap : B.inclusion.map (p.map ρ).left = eqToHom hy ≫ W'.ι := by
    rw [IsHomLift.fac' p g ρ]
    simp [Over.comp_left, Over.eqToHom_left, g]
  let j := B.inclusion.map (p.map ρ).left
  have hj : IsOpenImmersion j := by
    change IsOpenImmersion (B.inclusion.map (p.map ρ).left)
    rw [hmap]
    exact @IsOpenImmersion.comp _ _ _ (eqToHom hy) W'.ι (IsOpenImmersion.of_isIso _)
      W'.instIsOpenImmersionι
  have hj_apply : ∀ u, j u = W'.ι ((eqToHom hy) u) := by
    intro u
    change (B.inclusion.map (p.map ρ).left) u = _
    rw [hmap]
    rfl
  have hrange : Set.range j.base = W'.1 := by
    ext t
    constructor
    · rintro ⟨u, rfl⟩
      change j u ∈ W'
      rw [hj_apply]
      exact Subtype.property ((eqToHom hy) u)
    · intro ht
      refine ⟨(eqToHom hy.symm) ⟨t, ht⟩, ?_⟩
      rw [hj_apply]
      have := eqToHom_apply_eqToHom_symm hy ⟨t, ht⟩
      exact congrArg Subtype.val this
  have hρj : schemeMap q rfl rfl ρ = j := by
    simp only [schemeMap, eqToHom_refl, Category.id_comp]
    exact Category.comp_id _
  have hjU : j ≫ (q.obj x).hom = (q.obj y.1).hom :=
    comp_hom_eq_of_schemeMap_eq B S hS p rfl rfl ρ j hρj
  have hU' : LocallyOfFiniteType (q.obj y.1).hom := by
    rw [← hjU]
    exact @locallyOfFiniteType_comp _ _ _ j (q.obj x).hom
      (@locallyOfFiniteType_of_isOpenImmersion _ _ j hj) hU
  have hversal' : ∀ u : (q.obj y.1).left, IsFiniteTypePoint u →
      IsVersalAt (q.obj y.1) q u y.1 rfl := by
    intro u hu
    refine (isVersalAt_iff_of_isOpenImmersion_map B S hS 𝒳 ρ hj u).mpr (hW (j u) (hW'W ?_)
      (isFiniteTypePoint_map_of_isOpenImmersion j u hu))
    rw [← hrange]
    exact ⟨u, rfl⟩
  have : LocallyOfFiniteType (B.inclusion.map (p.obj y.1).hom) := hU'
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) := ‹IsLocallyNoetherian S›
  have hsm := Stack.isRelativelySmooth_of_isSmoothOnPredeformationCategories B S hS
    (Stack.objectMorphism B S hS 𝒳 (Functor.Fiber.mk (a := y.1) rfl)) (hrep _ _)
    (Stack.isLimitPreservingOnObjects_toTerminalCFG_schemeFibredCategory B S hS (p.obj y.1)
      inferInstance) hlimit
    (AlgebraicGeometry.Stack.isSmoothOnPredeformationCategories_objectMorphism_of_isVersalAt
      B S hS 𝒳 y.1 hU' hversal' hRS)
  have : IsAffine (B.inclusion.obj (BigFppfOver.openSubObj B S hS T W').left) := hW'aff
  have : IsAffine (B.inclusion.obj (p.obj y.1).left) := IsAffine.of_isIso (eqToHom hy)
  refine ⟨p.obj y.1, Functor.Fiber.mk rfl, hU', inferInstance, hsm, ?_⟩
  let f₀ := B.inclusion.map (p.map a).left
  have hsub : Set.range f₀.base ⊆ Set.range j.base := by
    rintro _ ⟨w, rfl⟩
    rw [hrange]
    have : f₀ w = u₀ := ha w
    rw [this]
    exact hu₀W'
  let l := IsOpenImmersion.lift j f₀ hsub
  have hl : l ≫ j = f₀ := IsOpenImmersion.lift_fac j f₀ hsub
  let h : p.obj x₀ ⟶ p.obj y.1 := Over.homMk (B.inclusion.preimage l) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    have e1 : B.inclusion.map (p.obj y.1).hom = j ≫ B.inclusion.map (p.obj x).hom := hjU.symm
    rw [e1, ← Category.assoc, hl, ← Functor.map_comp]
    exact congrArg B.inclusion.map (Over.w (p.map a)))
  have hfac : p.map a = h ≫ p.map ρ := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    rw [Over.comp_left, Functor.map_comp]
    change f₀ = B.inclusion.map (B.inclusion.preimage l) ≫ j
    rw [Functor.map_preimage, hl]
  have : p.IsStronglyCartesian (p.map ρ) ρ := hp.isStronglyCartesian_homLift (p.map ρ) ρ
  exact ⟨Functor.IsStronglyCartesian.map p (p.map ρ) ρ hfac a⟩

/-- **A field-valued point of finite type has a finite affine chart** (Section 07T2): an affine
open `U` of `S` through which `Spec k ⟶ S` factors, as the spectrum of a finite ring map
`Γ(S, U) ⟶ k`. -/
theorem exists_finite_affineChart_of_fieldPoint {k : Type u} [Field k] (i₀ : Spec (.of k) ⟶ S)
    (hlft : LocallyOfFiniteType i₀) :
    ∃ (U : S.affineOpens) (hU : (⊤ : (Spec (.of k)).Opens) ≤ i₀ ⁻¹ᵁ U.1),
      ((i₀.appLE U ⊤ hU) ≫ (Scheme.ΓSpecIso (.of k)).hom).hom.Finite ∧
      Spec.map ((i₀.appLE U ⊤ hU) ≫ (Scheme.ΓSpecIso (.of k)).hom) ≫ U.2.fromSpec = i₀ := by
  obtain ⟨U, hU, hfin⟩ := ((finiteType_specField_tfae i₀).out 2 3).mp hlft
  refine ⟨U, hU, hfin, ?_⟩
  rw [Spec.map_comp, Category.assoc, U.2.SpecMap_appLE_fromSpec i₀ (isAffineOpen_top _),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
  simp

/-- **A smooth chart through a field-valued point (the core of Stacks 07XY).** Let `𝒳` be a
category fibred in groupoids over the big fppf site of a locally Noetherian scheme `S` such that
the 1-morphism `y : (Sch/V)_{fppf} ⟶ 𝒳` of every object is representable by algebraic spaces,
which is limit preserving, satisfies (RS), has finite dimensional tangent spaces, effective formal
objects and openness of versality. Let `x₀` be an object of `𝒳` over `Spec k`, with `Spec k ⟶ S`
of finite type and with image `s` such that `𝒪_{S,s}` is a G-ring. Then there are an object `y`
of `𝒳` over a scheme of finite type over `S` with `y : (Sch/V)_{fppf} ⟶ 𝒳` smooth and an arrow
`x₀ ⟶ y`. -/
theorem exists_isRelativelySmooth_objectMorphism_of_fieldPoint [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hrep : ∀ (V : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber V),
      Stack.IsRepresentableByAlgebraicSpaces B S hS (Stack.objectMorphism B S hS 𝒳 y).hom)
    (hlimit : IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (htangent : ∀ {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
      (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ] (x₀ : 𝒳.val.obj)
      (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      letI := (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀).category
      ∀ hD : IsDeformationCategory
          (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection,
        letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
            (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀
              hx₀).projection).p) := ⟨hD.predeformation⟩
        letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
            (BasedCategory.ofFunctor
              (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
            hD.predeformation.cofibered))) := ⟨tangentConditionS2 hD⟩
        FiniteDimensional k (tangentSpaceArtinian Λ k (isomorphismClasses
          (BasedCategory.ofFunctor
            (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
          hD.predeformation.cofibered)))
    (heff : ∀ ξ : FormalObject B S hS 𝒳.val.p,
      FormalObject.IsEffective B S hS 𝒳.val.p 𝒳.property ξ)
    (hopen : ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : 𝒳.val.obj) (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ → IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧ ∀ u : U.left, u ∈ W.1 → IsFiniteTypePoint u →
          IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u x hx)
    {k : Type u} [Field k] (i₀ : Spec (.of k) ⟶ S) (x₀ : 𝒳.val.obj)
    (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀)
    (hlft : LocallyOfFiniteType i₀) (hqc : QuasiCompact i₀)
    (hG : IsGRing (S.presheaf.stalk (i₀ (closedPoint k)))) :
    ∃ (V : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber V),
      LocallyOfFiniteType (B.inclusion.map V.hom) ∧ QuasiCompact (B.inclusion.map V.hom) ∧
      Stack.IsRelativelySmooth B S hS (Stack.objectMorphism B S hS 𝒳 y) ∧
      Nonempty (x₀ ⟶ y.1) := by
  obtain ⟨U, hU, hfin, hfac⟩ := exists_finite_affineChart_of_fieldPoint S i₀ hlft
  let φ := (i₀.appLE U ⊤ hU) ≫ (Scheme.ΓSpecIso (.of k)).hom
  let : Algebra Γ(S, U.1) k := φ.hom.toAlgebra
  have : Module.Finite Γ(S, U.1) k := hfin
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) k)) ≫ U.2.fromSpec = i₀ := hfac
  have hx₀' : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) k)) ≫ U.2.fromSpec) := by
    rw [hφ]; exact hx₀
  have hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) k)) ≫
      U.2.fromSpec) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) k)) ≫ U.2.fromSpec) := by
    rw [hφ]; exact ⟨hlft, hqc⟩
  obtain ⟨U', u₀, V, -, x, hx, hlft', -, hu₀, hversal, a, ha⟩ :=
    exists_isVersalAt_of_affineChart B S hS 𝒳 hRS U.2.fromSpec x₀ hx₀' hfinite
      (htangent U.2.fromSpec x₀ hx₀' hfinite.1 hfinite.2) heff (hφ ▸ hG)
      (Stack.isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving B S hS 𝒳 hlimit)
  subst hx
  exact exists_isRelativelySmooth_of_isVersalAt B S hS 𝒳 hrep hlimit hRS hopen x.1 hlft' u₀ hu₀
    hversal a (fun w => ha w)

end Deformation.Artin

end
