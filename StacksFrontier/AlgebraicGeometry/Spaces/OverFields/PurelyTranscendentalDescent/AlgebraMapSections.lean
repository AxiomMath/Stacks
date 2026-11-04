module

public import Mathlib
public import StacksCore.FieldTheory.PurelyTranscendental
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteEnlargement
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Jacobson
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonFiniteTypePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SmallApproximationOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationInduction
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.MapToFiniteType
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.AlgClosureFGSubalgebraDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
import StacksFrontier.AlgebraicGeometry.Spaces.Flat
import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFromEtaleCover
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Base change along algebra maps for purely transcendental descent

Representability of a presheaf after restriction along `Spec k ⟶ Spec A` from a section given
by a `k`-algebra map `A → k`; finite type subalgebras of a purely transcendental extension as
localizations of polynomial algebras and their `k`-points or points over finite extensions of a
finite field (the infinite field case of Stacks 0B85); finite Galois base change with
`κ ⊗_k k'` a field; representability of products with representables, and quasi-separatedness of
subfunctors.

This is part of `StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace PurelyTranscendentalDescent

private theorem isRepresentable_relocalizeRestrict
    {C : Type v} [Category.{u} C] {S T : C} (f : S ⟶ T)
    [HasPullbacksAlong f] (F : (Over T)ᵒᵖ ⥤ Type u) [F.IsRepresentable] :
    ((OverShriek.relocalizeRestrict f).obj F).IsRepresentable :=
  Functor.IsRepresentable.mk'
    (((Over.mapPullbackAdj f).compYonedaIso.app F.reprX) ≪≫
      (OverShriek.relocalizeRestrict f).mapIso F.reprW)

private noncomputable def relocalizeRestrictCompIso
    {C : Type v} [Category.{u} C] {S T U : C} (f : S ⟶ T) (g : T ⟶ U)
    (F : (Over U)ᵒᵖ ⥤ Type u) :
    (OverShriek.relocalizeRestrict f).obj ((OverShriek.relocalizeRestrict g).obj F) ≅
      (OverShriek.relocalizeRestrict (f ≫ g)).obj F :=
  (Functor.associator (Over.map f).op (Over.map g).op F).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.opComp (Over.map f) (Over.map g)).symm ≪≫
        NatIso.op (Over.mapComp f g)) F

private theorem isRepresentable_of_relocalizeRestrict_of_section
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {S T : C} (f : S ⟶ T) (s : T ⟶ S) (hs : s ≫ f = 𝟙 T)
    (F : (Over T)ᵒᵖ ⥤ Type u)
    (hF : ((OverShriek.relocalizeRestrict f).obj F).IsRepresentable) :
    F.IsRepresentable := by
  have := isRepresentable_relocalizeRestrict s
    ((OverShriek.relocalizeRestrict f).obj F)
  have h := isRepresentable_of_natIso _ (relocalizeRestrictCompIso s f F)
  rw [hs] at h
  change ((Over.map (𝟙 T)).op ⋙ F).IsRepresentable at h
  exact isRepresentable_of_natIso _
    (Functor.isoWhiskerRight (NatIso.op (Over.mapId T).symm) F ≪≫ Functor.leftUnitor F)

/-- Composing `Spec` of a `k`-algebra map `A → L` with `Spec` of `k → A` gives `Spec` of `k → L`. -/
private theorem spec_map_algHom_comp_algebraMap
    {k A L : Type u} [CommRing k] [CommRing A] [CommRing L] [Algebra k A] [Algebra k L]
    (φ : A →ₐ[k] L) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact φ.commutes x

private theorem isRepresentable_of_baseChange_of_algHom
    (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) (hA : B.Contains (Spec (.of A)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :
        B.obj hA ⟶ B.obj hk)).obj F).IsRepresentable)
    (φ : A →ₐ[k] k) : F.IsRepresentable := by
  let f : B.obj hA ⟶ B.obj hk :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let s : B.obj hk ⟶ B.obj hA :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom))
  refine isRepresentable_of_relocalizeRestrict_of_section f s ?_ F hbase
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _
  rw [spec_map_algHom_comp_algebraMap, ← Spec.map_id]
  rfl

private theorem isRepresentable_baseChange_of_algHom
    (k A L : Type u) [CommRing k] [CommRing A] [CommRing L]
    [Algebra k A] [Algebra k L]
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) (hA : B.Contains (Spec (.of A)))
    (hL : B.Contains (Spec (.of L)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :
        B.obj hA ⟶ B.obj hk)).obj F).IsRepresentable)
    (φ : A →ₐ[k] L) :
    ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k L))) :
        B.obj hL ⟶ B.obj hk)).obj F).IsRepresentable := by
  let f : B.obj hA ⟶ B.obj hk :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let g : B.obj hL ⟶ B.obj hA :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom))
  have := isRepresentable_relocalizeRestrict g ((OverShriek.relocalizeRestrict f).obj F)
  have h := isRepresentable_of_natIso _ (relocalizeRestrictCompIso g f F)
  have hgf : g ≫ f = ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    apply ObjectProperty.hom_ext
    exact (spec_map_algHom_comp_algebraMap φ)
  rwa [hgf] at h

/-- For a morphism `α : W ⟶ Over.mk f` in `Over Z`, the isomorphism `Over.mk (α.left ≫ f) ≅ W`
whose underlying morphism is the identity. -/
noncomputable def overMkIsoOfFactorization
    {C : Type (u + 1)} [Category.{u} C] {Y Z : C} (f : Y ⟶ Z)
    {W : Over Z} (α : W ⟶ Over.mk f) : Over.mk (α.left ≫ f) ≅ W :=
  Over.isoMk (Iso.refl _) (by simpa using (Over.w α).symm)

private theorem mapIso_inv_hom_apply
    {C : Type (u + 1)} [Category.{u} C] (F : Cᵒᵖ ⥤ Type u)
    {X Y : C} (e : X ≅ Y) (x : F.obj (Opposite.op X)) :
    F.map e.hom.op (F.map e.inv.op x) = x := by
  rw [← F.map_comp_apply, ← op_comp]
  simp

/-- For `f : S ⟶ S'` and a presheaf `F'` on `Over S'`, relocalizing the restriction of `F'` to
`Over S` back to `Over S'` is isomorphic to the product `yoneda.obj (Over.mk f) ⨯ F'`. -/
noncomputable def relocalizeRestrictIsoProduct
    {C : Type (u + 1)} [Category.{u} C] {S S' : C} (f : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) :
    (OverShriek.relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ F') ≅
      yoneda.obj (Over.mk f) ⨯ F' := by
  classical
  let H := yoneda.obj (Over.mk f)
  let P := FunctorToTypes.prod H F'
  let e : (OverShriek.relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ F') ≅ P := by
    refine NatIso.ofComponents (fun W => ?_) ?_
    · let eW :
          ((OverShriek.relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ F')).obj W ≃
            P.obj W :=
        Equiv.mk (fun p =>
            let ψ := p.val.1
            let s : F'.obj (Opposite.op (Over.mk (ψ ≫ f))) := p.val.2
            let α : W.unop ⟶ Over.mk f := Over.homMk ψ p.property
            (α, F'.map (overMkIsoOfFactorization f α).inv.op s))
          (fun p =>
            let α := p.1
            let s := p.2
            let β : W.unop ⟶ Over.mk f := Over.homMk α.left (Over.w α)
            ⟨⟨β.left, F'.map (overMkIsoOfFactorization f β).hom.op s⟩, Over.w β⟩)
          (by
            intro p
            rcases p with ⟨⟨ψ, s⟩, hψ⟩
            change ψ ≫ f = W.unop.hom at hψ
            change F'.obj (Opposite.op (Over.mk (ψ ≫ f))) at s
            apply Subtype.ext
            apply Sigma.ext (by rfl)
            dsimp
            let α : W.unop ⟶ Over.mk f := Over.homMk ψ hψ
            let β : W.unop ⟶ Over.mk f := Over.homMk α.left (Over.w α)
            have hβα : β = α := Over.OverMorphism.ext rfl
            subst β
            change F'.obj (Opposite.op (Over.mk (α.left ≫ f))) at s
            exact heq_of_eq (mapIso_inv_hom_apply F' (overMkIsoOfFactorization f α) s))
          (by
            intro p
            change H.obj W × F'.obj W at p
            rcases p with ⟨α, s⟩
            apply Prod.ext
            · exact Over.OverMorphism.ext rfl
            · dsimp
              let β : W.unop ⟶ Over.mk f := Over.homMk α.left (Over.w α)
              exact mapIso_inv_hom_apply F' (overMkIsoOfFactorization f β).symm s)
      exact eW.toIso
    · intro W W' g
      ext x
      · rcases x with ⟨⟨_, _⟩, _⟩
        exact Over.OverMorphism.ext rfl
      · rcases x with ⟨⟨ψ, s⟩, hψ⟩
        change ψ ≫ f = W.unop.hom at hψ
        let β : W'.unop ⟶ W.unop := g.unop
        let α : W.unop ⟶ Over.mk f := Over.homMk ψ hψ
        let t : Over.mk (β.left ≫ ψ) ⟶ Over.mk ψ := Over.homMk β.left rfl
        let k : Over.mk (ψ ≫ f) ≅ W.unop := overMkIsoOfFactorization f α
        let k' : Over.mk ((β.left ≫ ψ) ≫ f) ≅ W'.unop :=
          Over.isoMk (Iso.refl _) (by
            simp only [Iso.refl_hom, Category.id_comp]
            calc
              W'.unop.hom = β.left ≫ W.unop.hom := (Over.w β).symm
              _ = β.left ≫ (ψ ≫ f) := by rw [hψ]
              _ = (β.left ≫ ψ) ≫ f := (Category.assoc _ _ _).symm)
        let q := (Over.map f).map t
        change F'.map k'.inv.op (F'.map q.op s) =
          F'.map β.op (F'.map k.inv.op s)
        rw [← F'.map_comp_apply, ← op_comp, ← F'.map_comp_apply, ← op_comp]
        have hcomp : k'.inv ≫ q = β ≫ k.inv := by
          apply Over.OverMorphism.ext
          simp [k', k, q, t, overMkIsoOfFactorization, Over.comp_left]
        rw [hcomp]
  exact e ≪≫ (FunctorToTypes.binaryProductIso H F').symm

private noncomputable def algHomOfSubalgebraThroughLocalization
    {k K L R : Type*} [CommSemiring k] [CommRing K] [CommRing L] [CommRing R]
    [Algebra k K] [Algebra k L] [Algebra k R]
    (A : Subalgebra k K) (φ : R →ₐ[k] K) (hφ : Function.Injective φ)
    (hA : A ≤ φ.range) (ψ : R →ₐ[k] L) : A →ₐ[k] L :=
  ψ.comp ((AlgEquiv.ofInjective φ hφ).symm.toAlgHom.comp (Subalgebra.inclusion hA))

private lemma exists_away_range_of_fg
    {k R : Type u} [CommRing k] [CommRing R] [IsDomain R] [Algebra k R]
    (A : Subalgebra k (FractionRing R)) (hA : A.FG) :
    ∃ (r : R) (_ : r ≠ 0) (φ : Localization.Away r →ₐ[k] FractionRing R),
      Function.Injective φ ∧ A ≤ φ.range := by
  classical
  obtain ⟨s, hs⟩ := hA
  obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors R) s
  have hr0 : (r : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp r.property
  have hr' : algebraMap R (FractionRing R) r ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.property
  let φ : Localization.Away (r : R) →ₐ[k] FractionRing R :=
    IsLocalization.Away.liftAlgHom (r : R)
      (f := IsScalarTower.toAlgHom k R (FractionRing R))
      (isUnit_iff_ne_zero.mpr hr')
  have hφ (a : R) : φ (algebraMap R (Localization.Away (r : R)) a) =
      algebraMap R (FractionRing R) a := by
    simp [φ, IsLocalization.Away.liftAlgHom_apply]
  refine ⟨r, hr0, φ, ?_, ?_⟩
  · apply IsLocalization.injective_of_map_algebraMap_zero
      (M := Submonoid.powers (r : R)) (S := Localization.Away (r : R)) φ.toRingHom
    intro a ha
    have ha' : algebraMap R (FractionRing R) a = 0 := by simpa [hφ] using ha
    have : a = 0 := (IsFractionRing.injective R (FractionRing R)) (by simpa using ha')
    simp [this]
  · rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    obtain ⟨a, ha⟩ := hr x hx
    let r' : Submonoid.powers (r : R) := ⟨r, 1, by simp⟩
    let y := IsLocalization.mk' (Localization.Away (r : R)) a r'
    refine ⟨y, ?_⟩
    apply mul_right_cancel₀ hr'
    have hy := congrArg φ (IsLocalization.mk'_spec (Localization.Away (r : R)) a r')
    have ha' : algebraMap R (FractionRing R) a =
        algebraMap R (FractionRing R) r * x := by
      simpa [Algebra.smul_def] using ha
    calc
      φ y * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) a := by
        simpa only [map_mul, hφ] using hy
      _ = x * algebraMap R (FractionRing R) r := ha'.trans (mul_comm _ _)

private lemma exists_polynomialLocalization_of_fg_subalgebra
    {k K : Type u} [Field k] [Field K] [Algebra k K] [PurelyTranscendental k K]
    (A : Subalgebra k K) (hA : A.FG) :
    ∃ (σ : Type u) (P : MvPolynomial σ k) (_ : P ≠ 0)
      (φ : Localization.Away P →ₐ[k] K), Function.Injective φ ∧ A ≤ φ.range := by
  obtain ⟨σ, ⟨e⟩⟩ := PurelyTranscendental.exists_algEquiv_mvRatFunc k K
  obtain ⟨P, hP, φ, hφ, hle⟩ := exists_away_range_of_fg
    (A.map e.symm.toAlgHom) (hA.map e.symm.toAlgHom)
  refine ⟨σ, P, hP, e.toAlgHom.comp φ, e.injective.comp hφ, ?_⟩
  intro x hx
  have hx' : e.symm x ∈ A.map e.symm.toAlgHom := ⟨x, hx, rfl⟩
  obtain ⟨y, hy⟩ := hle hx'
  exact ⟨y, by simpa using congrArg e hy⟩

private lemma exists_eval_ne_zero_of_ne_zero
    {k σ : Type u} [Field k] [Infinite k]
    (P : MvPolynomial σ k) (hP : P ≠ 0) :
    ∃ x : σ → k, MvPolynomial.eval x P ≠ 0 := by
  by_contra h
  push Not at h
  exact hP (MvPolynomial.funext fun x => by simp [h x])

private theorem exists_eval_ne_zero_of_totalDegree_lt_card
    {L : Type u} [Field L] [Finite L] (n : ℕ)
    (P : MvPolynomial (Fin n) L) (hP : P ≠ 0)
    (hdeg : P.totalDegree < Cardinal.mk L) :
    ∃ x : Fin n → L, MvPolynomial.eval x P ≠ 0 := by
  induction n with
  | zero =>
      have hrepr : P = MvPolynomial.C (MvPolynomial.coeff 0 P) := by
        ext d
        obtain rfl : d = 0 := Subsingleton.elim _ _
        simp
      have hcoeff : MvPolynomial.coeff 0 P ≠ 0 := by
        intro hc
        apply hP
        rw [hrepr, hc]
        simp
      refine ⟨Fin.elim0, ?_⟩
      rw [hrepr]
      simpa using hcoeff
  | succ n ih =>
      let p := MvPolynomial.finSuccEquiv L n P
      have hp : p ≠ 0 := fun hp0 =>
        hP ((MvPolynomial.finSuccEquiv L n).injective (by simpa [p] using hp0))
      obtain ⟨i, hi⟩ : ∃ i, p.coeff i ≠ 0 := by
        by_contra h
        push Not at h
        apply hp
        ext i m
        simp [h i]
      let c := p.coeff i
      have hcd : c.totalDegree < Cardinal.mk L := by
        have hle : c.totalDegree + i ≤ P.totalDegree := by
          simpa [c, p] using MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P i hi
        exact lt_of_le_of_lt (by exact_mod_cast (Nat.le_add_right _ _).trans hle) hdeg
      obtain ⟨s, hs⟩ := ih c hi hcd
      let q : Polynomial L := Polynomial.map (MvPolynomial.eval s) p
      have hqcoeff : q.coeff i ≠ 0 := by
        simpa [q, c] using hs
      have hq : q ≠ 0 := fun h => hqcoeff (by rw [h, Polynomial.coeff_zero])
      have hmap : q.natDegree ≤ p.natDegree := by
        simpa [q] using (Polynomial.natDegree_map_le (p := p) (f := MvPolynomial.eval s))
      have hpdeg : p.natDegree ≤ P.totalDegree := by
        rw [show p = MvPolynomial.finSuccEquiv L n P by rfl,
          MvPolynomial.natDegree_finSuccEquiv]
        exact MvPolynomial.degreeOf_le_totalDegree P 0
      have hqdeg : q.natDegree < Cardinal.mk L :=
        lt_of_le_of_lt (by exact_mod_cast hmap.trans hpdeg) hdeg
      obtain ⟨a, ha⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card q hq hqdeg
      refine ⟨Fin.cons a s, ?_⟩
      rw [MvPolynomial.eval_eq_eval_mv_eval' s a P]
      simpa [q, p] using ha

private noncomputable def localizationAway_map_of_eval_ne_zero
    {k : Type u} {L : Type v} {σ : Type w} [Field k] [Field L] [Algebra k L]
    (P : MvPolynomial σ k) (x : σ → L)
    (hP : MvPolynomial.eval₂Hom (algebraMap k L) x P ≠ 0) :
    Localization.Away P →ₐ[k] L :=
  IsLocalization.Away.liftAlgHom P
    (f := MvPolynomial.aeval x)
    (isUnit_iff_ne_zero.mpr (by simpa [MvPolynomial.aeval_def] using hP))

private lemma localizationAway_map_of_eval_ne_zero_apply
    {k : Type u} {L : Type v} {σ : Type w} [Field k] [Field L] [Algebra k L]
    (P : MvPolynomial σ k) (x : σ → L)
    (hP : MvPolynomial.eval₂Hom (algebraMap k L) x P ≠ 0)
    (Q : MvPolynomial σ k) :
    localizationAway_map_of_eval_ne_zero P x hP (algebraMap _ _ Q) =
      MvPolynomial.eval₂Hom (algebraMap k L) x Q := by
  unfold localizationAway_map_of_eval_ne_zero
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

@[sga "6 X 7.18.2" "case b"]
private lemma exists_localizationAway_algHom_of_infinite
    {k σ : Type u} [Field k] [Infinite k]
    (P : MvPolynomial σ k) (hP : P ≠ 0) :
    Nonempty (Localization.Away P →ₐ[k] k) := by
  obtain ⟨x, hx⟩ := exists_eval_ne_zero_of_ne_zero P hP
  exact ⟨localizationAway_map_of_eval_ne_zero P x (by simpa using hx)⟩

private lemma exists_localizationAway_algHom_of_finite
    {k : Type u} [Field k] [Finite k] (r : ℕ)
    (P : MvPolynomial (Fin r) k) (hP : P ≠ 0) (d : ℕ) (hd : 0 < d) :
    ∃ (L : Type 0) (_ : Field L) (_ : Finite L) (_ : Algebra k L)
      (_ : IsGalois k L),
      Module.finrank k L ≠ 0 ∧ Nat.Coprime (Module.finrank k L) d ∧
        Nonempty (Localization.Away P →ₐ[k] L) := by
  classical
  obtain ⟨p, hpchar⟩ := CharP.exists k
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let m := d * (P.totalDegree + 1) + 1
  have hm : 0 < m := Nat.succ_pos _
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let L := FiniteField.Extension k p m
  let : Field L := inferInstance
  let : Finite L := inferInstance
  let : Algebra k L := inferInstance
  have hfinrank : Module.finrank k L = m := by
    simpa [L, m] using FiniteField.finrank_extension k p m
  have hcoprime : Nat.Coprime m d := by
    dsimp [m]
    rw [Nat.coprime_mul_left_add_left]
    exact Nat.coprime_one_left d
  have hsize : P.totalDegree < Nat.card L := by
    have hq : 2 ≤ Nat.card k := Finite.one_lt_card
    have hpow : P.totalDegree < 2 ^ (P.totalDegree + 1) :=
      (Nat.lt_succ_self _).trans (Nat.lt_pow_self (by omega))
    have hleExp : P.totalDegree + 1 ≤ m :=
      (Nat.le_mul_of_pos_left _ hd).trans (Nat.le_succ _)
    have hbase : 2 ^ (P.totalDegree + 1) ≤ Nat.card k ^ (P.totalDegree + 1) :=
      Nat.pow_le_pow_left hq _
    have hexp : Nat.card k ^ (P.totalDegree + 1) ≤ Nat.card k ^ m :=
      Nat.pow_le_pow_right (by omega) hleExp
    have hsize' : P.totalDegree < Nat.card (FiniteField.Extension k p m) := by
      rw [FiniteField.natCard_extension k p m]
      exact lt_of_lt_of_le hpow (hbase.trans hexp)
    simpa [L] using hsize'
  let : Fintype L := Fintype.ofFinite L
  have hcard : P.totalDegree < Cardinal.mk L := by
    rw [Cardinal.mk_fintype]
    exact_mod_cast
      (by simpa [Nat.card_eq_fintype_card] using hsize : P.totalDegree < Fintype.card L)
  let PL : MvPolynomial (Fin r) L := P.map (algebraMap k L)
  have hPL : PL ≠ 0 := fun hzero =>
    hP (MvPolynomial.map_injective (algebraMap k L)
      (FaithfulSMul.algebraMap_injective k L) (by simpa [PL] using hzero))
  have hPLdeg : PL.totalDegree < Cardinal.mk L := by
    have hsupp : PL.support = P.support := by
      simpa [PL] using MvPolynomial.support_map_of_injective P
        (FaithfulSMul.algebraMap_injective k L)
    have hdegNat : PL.totalDegree = P.totalDegree := by
      unfold MvPolynomial.totalDegree
      rw [hsupp]
    rwa [hdegNat]
  obtain ⟨x, hx⟩ := exists_eval_ne_zero_of_totalDegree_lt_card (n := r) PL hPL hPLdeg
  have hEval : MvPolynomial.eval₂Hom (algebraMap k L) x P = MvPolynomial.eval x PL := by
    change MvPolynomial.eval₂ (algebraMap k L) x P = _
    rw [MvPolynomial.eval₂_eq_eval_map]
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hfinrank ▸ hm.ne',
    hfinrank ▸ hcoprime, ⟨localizationAway_map_of_eval_ne_zero P x (hEval ▸ hx)⟩⟩

@[sga "6 X 7.18.2" "case b", sga "6 X 7.18.3" "special case"]
private lemma exists_algHom_fg_subalgebra_of_infinite
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [PurelyTranscendental k K] [Infinite k]
    (A : Subalgebra k K) (hA : A.FG) : Nonempty (A →ₐ[k] k) := by
  obtain ⟨σ, P, hP, φ, hφ, hle⟩ :=
    exists_polynomialLocalization_of_fg_subalgebra A hA
  obtain ⟨ψ⟩ := exists_localizationAway_algHom_of_infinite P hP
  exact ⟨algHomOfSubalgebraThroughLocalization A φ hφ hle ψ⟩

/-- Let `K` be a purely transcendental extension of an infinite field `k` and `A` a finitely
generated `k`-subalgebra of `K`. If the base change of a presheaf `F` over `Spec k` to `Spec A` is
representable, then `F` is representable. -/
theorem isRepresentable_of_fg_baseChange_of_infinite
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [PurelyTranscendental k K] [Infinite k]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (A : Subalgebra k K) (hA : A.FG) (hAspec : B.Contains (Spec (.of A)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :
        B.obj hAspec ⟶ B.obj hk)).obj F).IsRepresentable) : F.IsRepresentable := by
  obtain ⟨φ⟩ := exists_algHom_fg_subalgebra_of_infinite A hA
  exact isRepresentable_of_baseChange_of_algHom k A B hk hAspec F hbase φ

private lemma exists_localizationAway_algHom_of_finite_variables
    {k σ : Type u} [Field k] [Finite k]
    (P : MvPolynomial σ k) (hP : P ≠ 0) (d : ℕ) (hd : 0 < d) :
    ∃ (L : Type 0) (_ : Field L) (_ : Finite L) (_ : Algebra k L)
      (_ : IsGalois k L),
      Module.finrank k L ≠ 0 ∧ Nat.Coprime (Module.finrank k L) d ∧
        Nonempty (Localization.Away P →ₐ[k] L) := by
  classical
  obtain ⟨n, f, hf, Q, hQ⟩ := MvPolynomial.exists_fin_rename P
  have hQ0 : Q ≠ 0 := fun h => hP (by simpa [h] using hQ)
  obtain ⟨L, hL, hLf, hLa, hLg, hdim, hcop, ⟨ψ⟩⟩ :=
    exists_localizationAway_algHom_of_finite n Q hQ0 d hd
  let x : Fin n → L := fun i =>
    ψ (algebraMap (MvPolynomial (Fin n) k) (Localization.Away Q) (MvPolynomial.X i))
  have hψ : ψ.comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k)
      (Localization.Away Q)) = MvPolynomial.aeval x := by
    ext i
    simp [x]
  have hxQ : MvPolynomial.aeval x Q ≠ 0 := by
    have hu := (IsLocalization.Away.algebraMap_isUnit Q (S := Localization.Away Q)).map
      ψ.toMonoidHom
    have he : MvPolynomial.aeval x Q = ψ (algebraMap _ _ Q) := by
      simpa using (AlgHom.congr_fun hψ Q).symm
    rw [he]
    exact hu.ne_zero
  let y : σ → L := Function.extend f x (fun _ => 0)
  have hy : y ∘ f = x := Function.extend_comp hf x _
  have hyP : MvPolynomial.aeval y P ≠ 0 := by
    rw [hQ, MvPolynomial.aeval_rename, hy]
    exact hxQ
  exact ⟨L, hL, hLf, hLa, hLg, hdim, hcop, ⟨localizationAway_map_of_eval_ne_zero P y (by
    simpa only [MvPolynomial.aeval_eq_eval₂Hom] using hyP)⟩⟩

private lemma exists_algHom_fg_subalgebra_of_finite
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [PurelyTranscendental k K] [Finite k]
    (A : Subalgebra k K) (hA : A.FG) (d : ℕ) (hd : 0 < d) :
    ∃ (L : Type 0) (_ : Field L) (_ : Finite L) (_ : Algebra k L)
      (_ : IsGalois k L),
      Module.finrank k L ≠ 0 ∧ Nat.Coprime (Module.finrank k L) d ∧
        Nonempty (A →ₐ[k] L) := by
  obtain ⟨σ, P, hP, φ, hφ, hle⟩ :=
    exists_polynomialLocalization_of_fg_subalgebra A hA
  obtain ⟨L, hL, hLf, hLa, hLg, hdim, hcop, ⟨ψ⟩⟩ :=
    exists_localizationAway_algHom_of_finite_variables P hP d hd
  exact ⟨L, hL, hLf, hLa, hLg, hdim, hcop,
    ⟨algHomOfSubalgebraThroughLocalization A φ hφ hle ψ⟩⟩

private lemma isField_tensorProduct_of_finrank_coprime
    (k : Type u) (L : Type v) (M : Type w)
    [Field k] [Field L] [Field M] [Algebra k L] [Algebra k M]
    (h : Nat.Coprime (Module.finrank k L) (Module.finrank k M)) :
    IsField (TensorProduct k L M) := by
  apply IntermediateField.LinearDisjoint.isField_of_forall k
  intro E _ _ f g
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  have hf : Module.finrank k L = Module.finrank k f.fieldRange :=
    (AlgEquiv.ofInjectiveField f).toLinearEquiv.finrank_eq
  have hg : Module.finrank k M = Module.finrank k g.fieldRange :=
    (AlgEquiv.ofInjectiveField g).toLinearEquiv.finrank_eq
  rwa [← hf, ← hg]

private theorem exists_finiteGalois_baseChange_of_fg_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [PurelyTranscendental k K] [Finite k]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (A : Subalgebra k K) (hA : A.FG) (hAspec : B.Contains (Spec (.of A)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :
        B.obj hAspec ⟶ B.obj hk)).obj F).IsRepresentable)
    (d : ℕ) (hd : 0 < d) :
    ∃ (L : Type u) (_ : Field L) (_ : Finite L) (_ : Algebra k L)
      (_ : IsGalois k L) (hL : B.Contains (Spec (.of L))),
      Module.finrank k L ≠ 0 ∧ Nat.Coprime (Module.finrank k L) d ∧
      ((OverShriek.relocalizeRestrict
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k L))) :
          B.obj hL ⟶ B.obj hk)).obj F).IsRepresentable := by
  obtain ⟨L, hL, hLf, hLa, hLg, hdim, hcop, ⟨φ⟩⟩ :=
    exists_algHom_fg_subalgebra_of_finite A hA d hd
  let L' := ULift.{u} L
  let e : L' ≃ₐ[k] L := ULift.algEquiv
  have hL'spec : B.Contains (Spec (.of L')) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      k L' hk
  exact ⟨L', inferInstance, inferInstance, inferInstance, inferInstance, hL'spec,
    by rwa [e.toLinearEquiv.finrank_eq], by rwa [e.toLinearEquiv.finrank_eq],
    isRepresentable_baseChange_of_algHom k A L' B hk hAspec hL'spec
      F hbase (e.symm.toAlgHom.comp φ)⟩

/-- Let `K` be a purely transcendental extension of a finite field `k`, `κ` a finite extension of
`k`, and `A` a finitely generated `k`-subalgebra of `K`. If the base change of a presheaf `F` over
`Spec k` to `Spec A` is representable, then there is a finite Galois extension `L` of `k` such that
`κ ⊗[k] L` is a field and the base change of `F` to `Spec L` is representable. -/
theorem exists_finiteGalois_baseChange_with_isField_tensorProduct
    (k K κ : Type u) [Field k] [Field K] [Field κ]
    [Algebra k K] [Algebra k κ] [FiniteDimensional k κ]
    [PurelyTranscendental k K] [Finite k]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (A : Subalgebra k K) (hA : A.FG) (hAspec : B.Contains (Spec (.of A)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :
        B.obj hAspec ⟶ B.obj hk)).obj F).IsRepresentable) :
    ∃ (L : Type u) (_ : Field L) (_ : Finite L) (_ : Algebra k L)
      (_ : IsGalois k L) (hL : B.Contains (Spec (.of L))),
      IsField (TensorProduct k κ L) ∧
      ((OverShriek.relocalizeRestrict
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k L))) :
          B.obj hL ⟶ B.obj hk)).obj F).IsRepresentable := by
  obtain ⟨L, hL, hLf, hLa, hLg, hLspec, hdim, hcop, hrep⟩ :=
    exists_finiteGalois_baseChange_of_fg_baseChange k K B hk A hA hAspec F hbase
      (Module.finrank k κ) (Module.finrank_pos)
  exact ⟨L, hL, hLf, hLa, hLg, hLspec,
    isField_tensorProduct_of_finrank_coprime k κ L hcop.symm, hrep⟩

private lemma over_hom_heq_of_left_eq
    {C : Type v} [Category.{u} C] {S X : C} {U : Over S}
    {s t : X ⟶ S} (hst : s = t) (a : Over.mk s ⟶ U) (b : Over.mk t ⟶ U)
    (hab : a.left = b.left) : HEq a b := by
  subst t
  exact heq_of_eq (Over.OverMorphism.ext hab)

private noncomputable def relocalizedYonedaRepresentableBy
    {C : Type v} [Category.{u} C] {S S' : C}
    (g : S ⟶ S') (U : Over S) :
    ((OverShriek.relocalizePresheafFunctor g).obj (yoneda.obj U)).RepresentableBy
      (Over.mk (U.hom ≫ g)) := by
  refine ⟨?_, ?_⟩
  · intro W
    refine
      { toFun := fun k => ⟨⟨k.left ≫ U.hom, Over.homMk k.left rfl⟩, by
          change (k.left ≫ U.hom) ≫ g = W.hom
          simpa [Category.assoc] using k.w⟩
        invFun := fun x => Over.homMk x.1.2.left (by
          change x.1.2.left ≫ (U.hom ≫ g) = W.hom
          rw [← Category.assoc, x.1.2.w]
          exact x.2)
        left_inv := fun k => by ext; rfl
        right_inv := by
          rintro ⟨⟨ψ, k⟩, hψ⟩
          let kHom : Over.mk ψ ⟶ U := k
          apply Subtype.ext
          apply Sigma.ext
          · simp
          · dsimp
            let kInv : Over.mk ψ ⟶ U := Over.homMk kHom.left kHom.w
            let kL' : (Over.mk ψ).left ⟶ U.left := Over.Hom.left kInv
            let k' : Over.mk (kL' ≫ U.hom) ⟶ U := Over.homMk kL' rfl
            have hidx : kL' ≫ U.hom = ψ := by simp [kL']
            have hObj : Over.mk (kL' ≫ U.hom) = Over.mk ψ := congrArg Over.mk hidx
            have hleft : (eqToHom hObj.symm).left = 𝟙 ((Over.mk ψ).left) := by
              rw [Over.eqToHom_left]
              rfl
            have hk : eqToHom hObj.symm ≫ k' = kHom := by
              apply Over.OverMorphism.ext
              rw [Over.comp_left, hleft, Category.id_comp]
              change kL' = Over.Hom.left kHom
              rfl
            simpa [Over.homMk, k', kL', kInv, kHom] using
              (eqToHom_comp_heq k' hObj.symm).symm.trans (heq_of_eq hk) }
  · intro W W' f k
    exact Subtype.ext (Sigma.ext (Category.assoc _ _ _)
      (over_hom_heq_of_left_eq (Category.assoc _ _ _) _ _ rfl))

private theorem isRepresentable_relocalizePresheafFunctor
    {C : Type v} [Category.{u} C] {S T : C} (f : S ⟶ T)
    (F : (Over S)ᵒᵖ ⥤ Type u) (hF : F.IsRepresentable) :
    ((OverShriek.relocalizePresheafFunctor f).obj F).IsRepresentable :=
  Functor.IsRepresentable.mk'
    ((Functor.representableByEquiv (relocalizedYonedaRepresentableBy f F.reprX)) ≪≫
      (OverShriek.relocalizePresheafFunctor f).mapIso F.reprW)

/-- If the restriction of a presheaf `F` on `Over T` along `f : S ⟶ T` is representable, then
`F ⨯ yoneda.obj (Over.mk f)` is representable. -/
theorem isRepresentable_prod_of_relocalizeRestrict
    {C : Type (u + 1)} [Category.{u} C] {S T : C} (f : S ⟶ T)
    (F : (Over T)ᵒᵖ ⥤ Type u)
    (hF : ((OverShriek.relocalizeRestrict f).obj F).IsRepresentable) :
    (F ⨯ yoneda.obj (Over.mk f)).IsRepresentable := by
  have : ((OverShriek.relocalizePresheafFunctor f).obj
      ((Over.map f).op ⋙ F)).IsRepresentable :=
    isRepresentable_relocalizePresheafFunctor f _ hF
  exact isRepresentable_of_natIso _
    (relocalizeRestrictIsoProduct f F ≪≫ prod.braiding _ _)

private theorem relativelyRepresentable_of_representable
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {F G : Cᵒᵖ ⥤ Type u} [F.IsRepresentable] [G.IsRepresentable] (f : F ⟶ G) :
    yoneda.relativelyRepresentable f := by
  let p := yoneda.preimage (F.reprW.hom ≫ f ≫ G.reprW.inv)
  let e : Arrow.mk (yoneda.map p) ≅ Arrow.mk f :=
    Arrow.isoMk F.reprW G.reprW (by simp [p])
  exact (yoneda.relativelyRepresentable.arrow_mk_iso_iff e).mp
    (Functor.relativelyRepresentable.map yoneda p)

private theorem isRepresentable_of_prod_of_section
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    (F G : Cᵒᵖ ⥤ Type u) [G.IsRepresentable] [(F ⨯ G).IsRepresentable]
    (T : C) (ht : IsTerminal (yoneda.obj T)) (s : yoneda.obj T ⟶ G) :
    F.IsRepresentable := by
  let j : F ⟶ F ⨯ G := prod.lift (𝟙 F) (ht.from F ≫ s)
  have hb : IsPullback j (ht.from F) prod.snd s := by
    apply IsPullback.mk'
    · simp [j]
    · intro W a b ha hb
      simpa [j] using congrArg (fun t => t ≫ prod.fst) ha
    · intro W a b h
      refine ⟨a ≫ prod.fst, ?_, ht.hom_ext _ _⟩
      apply prod.hom_ext
      · simp [j]
      · simp only [j, Category.assoc, prod.lift_snd]
        rw [← Category.assoc, ← Category.assoc,
          ht.hom_ext ((a ≫ prod.fst) ≫ ht.from F) b]
        exact h.symm
  exact Functor.IsRepresentable.mk'
    (((relativelyRepresentable_of_representable (prod.snd : F ⨯ G ⟶ G)).isPullback s).isoIsPullback
      _ _ hb)

/-- If `F ⨯ yoneda.obj (Over.mk f)` is representable for a presheaf `F` on `Over T` and
`f : S ⟶ T`, then the restriction of `F` along `f` is representable. -/
theorem isRepresentable_relocalizeRestrict_of_prod
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    {S T : C} (f : S ⟶ T) (F : (Over T)ᵒᵖ ⥤ Type u)
    (h : (F ⨯ yoneda.obj (Over.mk f)).IsRepresentable) :
    ((OverShriek.relocalizeRestrict f).obj F).IsRepresentable := by
  let R := OverShriek.relocalizeRestrict f
  let G := R.obj (yoneda.obj (Over.mk f))
  let U : Over S := Over.mk (𝟙 S)
  let s : yoneda.obj U ⟶ G := yonedaEquiv.symm
    (Over.homMk (𝟙 S) (by simp [U]))
  have := isRepresentable_relocalizeRestrict f (yoneda.obj (Over.mk f))
  have := isRepresentable_relocalizeRestrict f (F ⨯ yoneda.obj (Over.mk f))
  have : (R.obj F ⨯ G).IsRepresentable :=
    isRepresentable_of_natIso _ (asIso (prodComparison R F (yoneda.obj (Over.mk f))))
  exact isRepresentable_of_prod_of_section (R.obj F) G U
    (IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal) s

attribute [local instance] uliftCategory in
private theorem subfunctor_diagonal_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : Subfunctor F) :
    IsPullback U.ι (Limits.diag U.toFunctor)
      (Limits.diag F) (Limits.prod.map U.ι U.ι) := by
  apply IsPullback.mk'
  · apply Limits.prod.hom_ext <;> simp
  · exact fun T φ ψ hdiag _ => (cancel_mono U.ι).mp hdiag
  · intro T a b hab
    let x := b ≫ Limits.prod.fst
    let y := b ≫ Limits.prod.snd
    have hx : x ≫ U.ι = a := by
      simpa [x, Category.assoc] using (congrArg (fun f => f ≫ Limits.prod.fst) hab).symm
    have hy : y ≫ U.ι = a := by
      simpa [y, Category.assoc] using (congrArg (fun f => f ≫ Limits.prod.snd) hab).symm
    have hxy : x = y := (cancel_mono U.ι).mp (hx.trans hy.symm)
    refine ⟨x, hx, ?_⟩
    apply Limits.prod.hom_ext
    · simp [x]
    · simpa [y] using hxy

/-- A subfunctor of a presheaf on the big fppf site over `S` that is quasi-separated over `S` is
itself quasi-separated over `S`. -/
theorem isQuasiSeparated_subfunctor_of_isQuasiSeparated
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : Subfunctor F)
    (hF : AlgebraicGeometry.Space.IsQuasiSeparatedOver B S hS F) :
    AlgebraicGeometry.Space.IsQuasiSeparatedOver B S hS U.toFunctor := by
  let P : MorphismProperty (AlgebraicGeometry.BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have : (P.presheaf).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  change P.presheaf (Limits.diag U.toFunctor)
  exact MorphismProperty.of_isPullback
    (subfunctor_diagonal_isPullback B S hS U)
    (show P.presheaf (Limits.diag F) from hF)

end PurelyTranscendentalDescent

end AlgebraicGeometry

end
