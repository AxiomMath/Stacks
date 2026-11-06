module

public import Mathlib.Algebra.Algebra.Shrink
public import StacksFrontier.Deformation.Smooth.CompleteLocalAlgebra.LocalizedBase
import StacksFrontier.Deformation.Predeformation.PointsFromBase
import all StacksFrontier.Deformation.Smooth.CompleteLocalAlgebra.LocalizedBase

/-!
# Smooth complete local algebras: the lifting criterion (Stacks 0DYL, (1)–(4))

Smoothness of `restrictedCoyonedaProjection R` is reduced to lifting along small extensions
of Artinian local algebras and compared with adic formal smoothness of `Λ → R`; together
with the flatness and special-fibre conditions this gives
`Deformation.smooth_formallySmooth_flat_specialFibre_tfae`, conditions (1)–(4) of Stacks 0DYL.
-/

@[expose] public section

open CategoryTheory
open IsLocalRing
open scoped TensorProduct

universe u v w

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Lifting along `f` after applying `artinianToComplete` gives the lifting datum of the
restricted coyoneda projection. -/
private theorem restrictedCoyonedaProjection_lift_of_lift
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) {B A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : B ⟶ A)
    (hlift : ∀ x : R ⟶ artinianToComplete.obj A,
      ∃ y : R ⟶ artinianToComplete.obj B, y ≫ artinianToComplete.map f = x)
    (y : (BasedCategory.ofFunctor (𝟭 (ArtinianLocalAlgCat.{u, v, w} Λ k))).obj)
    (x : (restrictedRepresentable R).obj)
    (g : y ⟶ (restrictedCoyonedaProjection R).obj x)
    (hg : (BasedCategory.ofFunctor (𝟭 (ArtinianLocalAlgCat.{u, v, w} Λ k))).p.IsHomLift f g) :
    ∃ (x' : (restrictedRepresentable R).obj) (lift : x' ⟶ x)
      (a : (restrictedCoyonedaProjection R).obj x' ⟶ y),
      (restrictedRepresentable R).p.IsHomLift f lift ∧
        (BasedCategory.ofFunctor (𝟭 (ArtinianLocalAlgCat.{u, v, w} Λ k))).p.IsHomLift (𝟙 B) a ∧
          (restrictedCoyonedaProjection R).map lift = a ≫ g := by
  let := hg
  have hy : y = B := by
    cases hg
    rfl
  have hx : (restrictedCoyonedaProjection R).toFunctor.obj x = A := by
    cases hg
    rfl
  rcases x with @⟨A', x⟩
  change A' = A at hx
  subst A'
  subst y
  have hgf : g = f := by
    cases hg
    rfl
  obtain ⟨xB, hxB⟩ := hlift x
  let xB' : (restrictedCoyoneda R).Elements := (restrictedCoyoneda R).elementsMk B xB
  let hB : xB' ⟶ (restrictedCoyoneda R).elementsMk A x := Functor.Elements.homMk f (by
      apply CompleteLocalAlgCat.Hom.ext
      have hxB' := congrArg CompleteLocalAlgCat.Hom.hom hxB
      simpa [restrictedCoyoneda, restrictedCoyoneda_map_hom] using hxB')
  refine ⟨xB', hB, 𝟙 B, ?_, ?_, ?_⟩
  · exact IsHomLift.of_fac (p := (restrictedRepresentable R).p) f hB rfl rfl (by rfl)
  · exact IsHomLift.map
      (p := (BasedCategory.ofFunctor (𝟭 (ArtinianLocalAlgCat.{u, v, w} Λ k))).p) (𝟙 B)
  · show f = (𝟙 B) ≫ g
    rw [← hgf]
    exact (Category.id_comp g).symm

variable [IsNoetherianRing Λ] [Module.Finite Λ k]

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
private theorem restrictedCoyonedaProjection_lifts
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    IsSmooth (restrictedCoyonedaProjection R) ↔
      ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A),
        Function.Surjective f.hom →
          ∀ (x : R ⟶ artinianToComplete.obj A),
            ∃ y : R ⟶ artinianToComplete.obj B,
              y ≫ artinianToComplete.map f = x := by
  constructor
  · intro hs B A f hf x
    let F := restrictedCoyoneda R
    let xE : F.Elements := F.elementsMk A x
    let g : B ⟶ A := f
    have hg : (BasedCategory.ofFunctor (𝟭
        (ArtinianLocalAlgCat.{u, v, w} Λ k))).p.IsHomLift f g :=
      IsHomLift.map
        (p := (BasedCategory.ofFunctor (𝟭 (ArtinianLocalAlgCat.{u, v, w} Λ k))).p) g
    obtain ⟨xE', h, a, hh, ha, htriangle⟩ := hs f hf B xE g hg
    rcases xE' with @⟨B', y⟩
    have hB : B' = B := IsHomLift.domain_eq
      (p := (restrictedRepresentable R).p) f h
    subst B'
    have ha' : a = 𝟙 B := by
      cases ha
      rfl
    have hval : h.hom = f := by
      change h.hom = a ≫ f at htriangle
      rw [ha'] at htriangle
      exact htriangle.trans (Category.id_comp f)
    refine ⟨y, ?_⟩
    apply CompleteLocalAlgCat.Hom.ext
    have hprop := congrArg CompleteLocalAlgCat.Hom.hom h.map_val
    simpa [F, restrictedCoyoneda, restrictedCoyoneda_map_hom, hval] using hprop
  · intro h B A f hf y x g hg
    exact restrictedCoyonedaProjection_lift_of_lift R f (h f hf) y x g hg

private theorem identity_isFiberedInGroupoids (C : Type*) [Category C] :
    (𝟭 C).IsFiberedInGroupoids := by
  refine ⟨?_, ?_⟩
  · intro V U f x hx
    subst U
    exact ⟨V, f, IsHomLift.map (p := 𝟭 C) f⟩
  · intro x y z φ ψ f hf
    refine ⟨f, ⟨rfl, ?_⟩, ?_⟩
    · simpa using hf
    · exact fun χ hχ => hχ.1

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
private theorem restrictedCoyonedaProjection_smallLifts
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    IsSmooth (restrictedCoyonedaProjection R) ↔
      ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A),
        InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom f.hom.toRingHom) →
          ∀ (x : R ⟶ artinianToComplete.obj A),
            ∃ y : R ⟶ artinianToComplete.obj B,
              y ≫ artinianToComplete.map f = x := by
  constructor
  · rintro hs B A f ⟨_, _, _, _, hf, _⟩ x
    exact (restrictedCoyonedaProjection_lifts R).mp hs f hf x
  · intro hlift
    have hG : IsCofiberedInGroupoids
        (𝟭 (ArtinianLocalAlgCat.{u, v, w} Λ k)) := by
      dsimp [IsCofiberedInGroupoids]
      exact identity_isFiberedInGroupoids _
    apply isSmooth_of_lifts_smallExtensions
      (𝓖 := BasedCategory.ofFunctor (𝟭 (ArtinianLocalAlgCat.{u, v, w} Λ k)))
      (φ := restrictedCoyonedaProjection R)
    · show IsCofiberedInGroupoids
        (Functor.Elements.π (restrictedCoyoneda R))
      show Functor.IsFiberedInGroupoids
        (Functor.Elements.π (restrictedCoyoneda R)).op
      constructor
      · intro V U f x hx
        rcases V with ⟨V⟩
        rcases U with ⟨U⟩
        rcases x with ⟨x⟩
        change Opposite.op ((Functor.Elements.π (restrictedCoyoneda R)).obj x) =
          Opposite.op U at hx
        cases hx
        let y := (restrictedCoyoneda R).elementsMk V
          ((restrictedCoyoneda R).map f.unop x.val)
        let g : x ⟶ y := Functor.Elements.homMk f.unop rfl
        refine ⟨Opposite.op y, g.op, ?_⟩
        have hmap : (Functor.Elements.π (restrictedCoyoneda R)).op.map g.op = f := by
          apply Quiver.Hom.opEquiv.injective
          simp [g, Functor.Elements.π]
        rw [← hmap]
        exact inferInstance
      · intro x y z φ ψ f hf
        rcases x with ⟨x⟩
        rcases y with ⟨y⟩
        rcases z with ⟨z⟩
        have hbase : φ.unop.hom ≫ f.unop = ψ.unop.hom := by
          simpa using congrArg Quiver.Hom.unop hf
        let g : y ⟶ z := Functor.Elements.homMk f.unop (by
          calc
            (restrictedCoyoneda R).map f.unop y.val =
                (restrictedCoyoneda R).map f.unop
                  ((restrictedCoyoneda R).map φ.unop.hom x.val) := by
                    rw [Functor.Elements.Hom.map_val]
            _ = (restrictedCoyoneda R).map (φ.unop.hom ≫ f.unop) x.val := by
                  rw [Functor.map_comp_apply]
            _ = (restrictedCoyoneda R).map ψ.unop.hom x.val := by rw [hbase]
            _ = z.val := Functor.Elements.Hom.map_val ψ.unop)
        refine ⟨g.op, ⟨?_, ?_⟩, ?_⟩
        · have hmap : (Functor.Elements.π (restrictedCoyoneda R)).op.map g.op = f := by
            apply Quiver.Hom.opEquiv.injective
            simp [g, Functor.Elements.π]
          exact hmap
        · apply Quiver.Hom.opEquiv.symm.injective
          apply Functor.Elements.hom_ext
          exact hbase
        · intro χ hχ
          apply Quiver.Hom.opEquiv.symm.injective
          apply Functor.Elements.hom_ext
          have hh := congrArg Quiver.Hom.unop hχ.1
          change χ.unop.hom = f.unop at hh
          exact hh
    · exact hG
    · intro B A f hsmall y x g hg
      exact restrictedCoyonedaProjection_lift_of_lift R f (hlift f hsmall) y x g hg

-- The lifted Artinian square involves quotient maps and universe transports.
omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
private theorem formallySmoothNAdic_smallLifts
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (h : RingHom.FormallySmoothNAdic.{max u v} (algebraMap Λ R)
      (maximalIdeal R)) :
    ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A),
      InfinitesimalLifting.IsSmallExtension
        (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ (x : R ⟶ artinianToComplete.obj A),
        ∃ y : R ⟶ artinianToComplete.obj B,
          y ≫ artinianToComplete.map f = x := by
  intro B A f hsmall x
  let E := ULift.{max u v} B
  let F := ULift.{max u v} A
  let upB : B →+* E := ULift.ringEquiv.symm.toRingHom
  let upA : A →+* F := ULift.ringEquiv.symm.toRingHom
  let : RingHomSurjective (upB : B →+* E) := ⟨ULift.ringEquiv.symm.surjective⟩
  let fLift : E →+* F := RingHom.ulift.{max u v, max u v} f.hom.toRingHom
  let J : Ideal E := RingHom.ker fLift
  have hsq0 : (RingHom.ker f.hom.toRingHom) ^ 2 = ⊥ :=
    (InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection
      (CommRingCat.ofHom f.hom.toRingHom) hsmall).2.2.2
  have hker : J = Ideal.map upB (RingHom.ker f.hom.toRingHom) := by
    ext z
    show fLift z = 0 ↔ z ∈ Ideal.map upB (RingHom.ker f.hom.toRingHom)
    constructor
    · intro hz
      have hzdown : f.hom.toRingHom z.down = 0 := by
        have hz' := congrArg ULift.down hz
        dsimp [fLift, RingHom.ulift] at hz'
        change f.hom.toRingHom z.down = 0 at hz'
        exact hz'
      show upB z.down ∈ Ideal.map upB (RingHom.ker f.hom.toRingHom)
      exact Ideal.mem_map_of_mem upB hzdown
    · intro hz
      obtain ⟨b, hb, hzb⟩ :=
        (Ideal.mem_map_iff_of_surjective upB upB.surjective).mp hz
      rw [← hzb]
      show ULift.up (f.hom.toRingHom b) = 0
      rw [hb]
      rfl
  have hsq : J ^ 2 = ⊥ := by
    rw [hker, ← Ideal.map_pow, hsq0, Ideal.map_bot]
  have hf : Function.Surjective f.hom.toRingHom := by
    rcases hsmall with ⟨_, _, _, _, hf, _⟩
    exact hf
  have hfLift : Function.Surjective fLift := by
    intro a
    obtain ⟨b, hb⟩ := hf a.down
    exact ⟨ULift.up b, ULift.ext hb⟩
  let e : (E ⧸ J) ≃+* F :=
    RingHom.quotientKerEquivOfSurjective (f := fLift) hfLift
  let ψ : R →+* E ⧸ J := e.symm.toRingHom.comp (upA.comp x.hom.toRingHom)
  have hcomm : ψ.comp (algebraMap Λ R) =
      (Ideal.Quotient.mk J).comp (upB.comp (algebraMap Λ B)) := by
    ext a
    apply e.injective
    calc
      e (ψ (algebraMap Λ R a)) = upA (x.hom (algebraMap Λ R a)) := by simp [ψ]
      _ = upA (algebraMap Λ A a) := by
        congr 1
        simp [artinianToComplete]
      _ = fLift (upB (algebraMap Λ B a)) := congrArg ULift.up (f.hom.commutes a).symm
      _ = e (Ideal.Quotient.mk J (upB (algebraMap Λ B a))) := by
        symm
        exact RingHom.quotientKerEquivOfSurjective_apply_mk hfLift
          (upB (algebraMap Λ B a))
  obtain ⟨n, hn⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  have hn' : maximalIdeal A ^ (n + 1) = ⊥ := by
    simp [pow_succ, hn]
  have hpow : ∃ n : ℕ, 1 ≤ n ∧ (maximalIdeal R) ^ n ≤ RingHom.ker ψ := by
    refine ⟨n + 1, by omega, ?_⟩
    · intro r hr
      let : IsLocalHom x.hom.toRingHom := x.isLocal
      have hmap0 : Ideal.map x.hom.toRingHom (maximalIdeal R) ≤ maximalIdeal A := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        exact map_nonunit x.hom.toRingHom a ha
      have hmap :
          Ideal.map x.hom.toRingHom (maximalIdeal R ^ (n + 1)) ≤
            maximalIdeal A ^ (n + 1) := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono hmap0 _
      have hxpow : x.hom r ∈ maximalIdeal A ^ (n + 1) :=
        hmap (Ideal.mem_map_of_mem x.hom.toRingHom hr)
      have hzero : x.hom r = 0 := by simpa [hn'] using hxpow
      show ψ r = 0
      simp [ψ, hzero]
  let fbase : Λ →+* E := upB.comp (algebraMap Λ B)
  obtain ⟨g, hgquot, hgbase⟩ := h E J hsq fbase ψ hcomm hpow
  let gdown : R →+* B := ULift.ringEquiv.toRingHom.comp g
  have hfg : f.hom.toRingHom.comp gdown = x.hom.toRingHom := by
    ext r
    have heq : fLift (g r) = upA (x.hom r) := by
      calc
        fLift (g r) = e (Ideal.Quotient.mk J (g r)) := by
          symm
          exact RingHom.quotientKerEquivOfSurjective_apply_mk hfLift (g r)
        _ = e (ψ r) := congrArg e (RingHom.congr_fun hgquot r)
        _ = upA (x.hom r) := by simp [ψ]
    have hdown := congrArg ULift.down heq
    change f.hom.toRingHom (ULift.ringEquiv (g r)) = x.hom r at hdown
    simpa [gdown] using hdown
  let ghom : R →ₐ[Λ] B :=
    { toRingHom := gdown
      commutes' := fun a => by
        have hb'' : gdown.comp (algebraMap Λ R) = algebraMap Λ B := by
          calc
            gdown.comp (algebraMap Λ R) =
                ULift.ringEquiv.toRingHom.comp
                  (g.comp (algebraMap Λ R)) := by
                    simp [gdown, RingHom.comp_assoc]
            _ = ULift.ringEquiv.toRingHom.comp fbase :=
              congrArg (fun q : Λ →+* E => ULift.ringEquiv.toRingHom.comp q) hgbase
            _ = algebraMap Λ B := by
              ext a
              rfl
        exact RingHom.congr_fun hb'' a }
  have hlocal : IsLocalHom ghom.toRingHom := by
    refine ⟨fun r hunit => ?_⟩
    have hxunit : IsUnit (x.hom.toRingHom r) := by
      rw [← RingHom.congr_fun hfg r]
      exact hunit.map f.hom.toRingHom
    exact x.isLocal.map_nonunit r hxunit
  let y : R ⟶ artinianToComplete.obj B :=
    { hom := ghom
      isLocal := hlocal
      residue_comm := fun r => by
        calc
          B.residueEquiv (residue B (gdown r)) =
              A.residueEquiv (residue A (f.hom (gdown r))) :=
                (f.residue_comm (gdown r)).symm
          _ = A.residueEquiv (residue A (x.hom r)) :=
              congrArg (fun z : A => A.residueEquiv (residue A z))
                (RingHom.congr_fun hfg r)
          _ = R.residueEquiv (residue R r) := x.residue_comm r }
  refine ⟨y, ?_⟩
  apply CompleteLocalAlgCat.Hom.ext
  ext r
  exact RingHom.congr_fun hfg r

-- The fibre comparisons elaborate the algebra structures for both tensor factors.
private theorem formallySmooth_flat_specialFibre_tfae
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    let p := RingHom.ker (algebraMap Λ k)
    letI : p.IsMaximal := Algebra.ker_algebraMap_isMaximal_of_isIntegral Λ k
    let k' := Λ ⧸ p
    letI : Field k' := Ideal.Quotient.field p
    let Bbar := R ⊗[Λ] k'
    letI : Algebra k' Bbar := Algebra.TensorProduct.rightAlgebra
    List.TFAE [
      RingHom.FormallySmoothNAdic.{max u v} (algebraMap Λ R) (maximalIdeal R),
      Module.Flat Λ R ∧ Algebra.IsGeometricallyRegular k' Bbar,
      Module.Flat Λ R ∧
        RingHom.FormallySmoothNAdic.{max u v} (algebraMap k' Bbar)
          ((maximalIdeal R).map Algebra.TensorProduct.includeLeftRingHom)] := by
  let p := RingHom.ker (algebraMap Λ k)
  let : p.IsMaximal := Algebra.ker_algebraMap_isMaximal_of_isIntegral Λ k
  let k' := Λ ⧸ p
  let : Field k' := Ideal.Quotient.field p
  let T := Localization.AtPrime p
  let : Algebra T R := (localizedStructureMap R rfl).toAlgebra
  let F := R ⊗[T] ResidueField T
  let : Algebra (ResidueField T) F := Algebra.TensorProduct.rightAlgebra
  let G := ResidueField T ⊗[T] R
  let : Algebra (ResidueField T) G := Algebra.TensorProduct.leftAlgebra
  let eK : k' ≃+* ResidueField T := (IsLocalization.AtPrime.equivQuotMaximalIdeal p T).toRingEquiv
  let : Algebra k' F := ((algebraMap (ResidueField T) F).comp eK.toRingHom).toAlgebra
  let Bbar := R ⊗[Λ] k'
  let : Algebra k' Bbar := Algebra.TensorProduct.rightAlgebra
  let e := localizedSpecialFibre_algEquiv R rfl
  let eFG : F ≃ₐ[ResidueField T] G :=
    { toRingEquiv := (Algebra.TensorProduct.comm T R (ResidueField T)).toRingEquiv
      commutes' := by
        intro a
        show (Algebra.TensorProduct.comm T R (ResidueField T)).toRingEquiv
            ((1 : R) ⊗ₜ[T] a) = a ⊗ₜ[T] (1 : R)
        exact Algebra.TensorProduct.comm_tmul T (1 : R) a }
  obtain ⟨htriv, hlocal, hnoeth⟩ := specialFibre_isLocalNoetherian R p rfl
  let : Nontrivial Bbar := htriv
  let : IsLocalRing Bbar := hlocal
  let : IsNoetherianRing Bbar := hnoeth
  let : Nontrivial F := Function.Injective.nontrivial e.symm.injective
  let : IsLocalRing F := IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  let : IsNoetherianRing F := isNoetherianRing_of_ringEquiv Bbar e.symm
  let : Nontrivial G := Function.Injective.nontrivial eFG.injective
  let : IsLocalRing G := IsLocalRing.of_surjective' eFG.toRingHom eFG.surjective
  let : IsNoetherianRing G := isNoetherianRing_of_ringEquiv F eFG
  have hepre : Ideal.comap e.toRingEquiv (maximalIdeal Bbar) = maximalIdeal F := by
    let : IsLocalHom (e.toRingEquiv : F →+* Bbar) := IsLocalHom.of_surjective _ e.surjective
    exact IsLocalRing.maximalIdeal_comap (e.toRingEquiv : F →+* Bbar)
  have hcodomain :
      RingHom.FormallySmoothNAdic.{max u v} (algebraMap k' F) (maximalIdeal F) ↔
        RingHom.FormallySmoothNAdic.{max u v} (algebraMap k' Bbar)
          (maximalIdeal Bbar) := by
    have h := formallySmoothNAdic_iff_comp_codomainRingEquiv
      (algebraMap k' F) e.toRingEquiv (maximalIdeal Bbar)
    rw [hepre] at h
    have hc : e.toRingHom.comp (algebraMap k' F) = algebraMap k' Bbar := by
      ext a
      exact e.commutes a
    rwa [hc] at h
  have hsource :
      RingHom.FormallySmoothNAdic.{max u v}
          (algebraMap (ResidueField T) F) (maximalIdeal F) ↔
        RingHom.FormallySmoothNAdic.{max u v} (algebraMap k' F) (maximalIdeal F) := by
    have h := formallySmoothNAdic_iff_comp_ringEquiv
      (algebraMap (ResidueField T) F) eK (maximalIdeal F)
    have hc : (algebraMap (ResidueField T) F).comp eK.toRingHom =
        algebraMap k' F := rfl
    rwa [hc] at h
  have hgeomFG : Algebra.IsGeometricallyRegular (ResidueField T) F ↔
      Algebra.IsGeometricallyRegular (ResidueField T) G := by
    constructor
    · intro h
      refine ⟨fun K _ _ _ => ?_⟩
      have hreg := h.isRegularRing_tensorProduct K
      exact IsRegularRing.of_ringEquiv
        (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[ResidueField T] K)
          eFG).toRingEquiv
    · intro h
      refine ⟨fun K _ _ _ => ?_⟩
      have hreg := h.isRegularRing_tensorProduct K
      exact IsRegularRing.of_ringEquiv
        (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[ResidueField T] K)
          eFG.symm).toRingEquiv
  have hbar :
      Algebra.IsGeometricallyRegular k' Bbar ↔
        RingHom.FormallySmoothNAdic.{max u v} (algebraMap k' Bbar)
          ((maximalIdeal R).map Algebra.TensorProduct.includeLeftRingHom) := by
    simpa [Bbar] using specialFibre_geometricallyRegular_iff_formallySmooth R p rfl
  have hbarmax :
      (maximalIdeal R).map Algebra.TensorProduct.includeLeftRingHom = maximalIdeal Bbar :=
    IsLocalRing.map_maximalIdeal_of_surjective _ (specialFibre_includeLeft_surjective R p)
  have hflat : Module.Flat Λ R ↔ Module.Flat T R :=
    flat_iff_flat_localizedStructureMap R rfl
  have hbase :
      RingHom.FormallySmoothNAdic.{max u v} (algebraMap Λ R) (maximalIdeal R) ↔
        RingHom.FormallySmoothNAdic.{max u v} (localizedStructureMap R rfl)
          (maximalIdeal R) :=
    formallySmoothNAdic_iff_localizationBase
      (M := p.primeCompl) (T := T) (algebraMap Λ R) (maximalIdeal R)
      (localizedStructureMap R rfl) (localizedStructureMap_comp R rfl) fun s =>
        structureMap_isUnit_of_not_mem_residueKernel R.residueEquiv s.1
          (fun hz => s.2 (RingHom.mem_ker.mpr hz))
  let : IsLocalHom (localizedStructureMap R rfl) :=
    localizedStructureMap_isLocalHom R rfl
  have h07 := flat_geometricallyRegular_specialFiber_formallySmooth_tfae
    (localizedStructureMap R rfl)
  have hloc13G :
      (Module.Flat T R ∧ Algebra.IsGeometricallyRegular (ResidueField T) G) ↔
        RingHom.FormallySmoothNAdic.{max u v} (localizedStructureMap R rfl)
          (maximalIdeal R) :=
    h07.out 1 3 (by simp [p, T, G]) (by simp)
  have hloc13 :
      (Module.Flat T R ∧ Algebra.IsGeometricallyRegular (ResidueField T) F) ↔
        RingHom.FormallySmoothNAdic.{max u v} (localizedStructureMap R rfl)
          (maximalIdeal R) :=
    (and_congr Iff.rfl hgeomFG).trans hloc13G
  have hflatbar :
      (Module.Flat Λ R ∧ Algebra.IsGeometricallyRegular k' Bbar) ↔
        (Module.Flat T R ∧ Algebra.IsGeometricallyRegular (ResidueField T) F) := by
    rw [hbarmax] at hbar
    exact and_congr hflat (hbar.trans (hcodomain.symm.trans (hsource.symm.trans
      (geometricallyRegular_iff_formallySmoothNAdic (K := ResidueField T) (C := F)).symm)))
  tfae_have 1 ↔ 2 := hbase.trans (hloc13.symm.trans hflatbar.symm)
  tfae_have 1 ↔ 3 :=
    hbase.trans (hloc13.symm.trans (hflatbar.symm.trans (and_congr Iff.rfl hbar)))
  tfae_finish

private theorem residueField_map_bijective_of_surjective
    {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Bijective (IsLocalRing.ResidueField.map f) := by
  constructor
  · exact (IsLocalRing.ResidueField.map f).injective
  · intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨IsLocalRing.residue A a, IsLocalRing.ResidueField.map_residue f a⟩

private theorem small_of_finiteLength
    {A : Type u} [CommRing A] [IsLocalRing A] [Small.{v} (ResidueField A)]
    {M : Type w} [AddCommGroup M] [Module A M] (h : IsFiniteLength A M) :
    Small.{v} M := by
  classical
  induction h with
  | of_subsingleton => infer_instance
  | @of_simple_quotient M _ _ N _ h ih =>
    obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := A) (M := M ⧸ N)).mp
      inferInstance
    have hI' := IsLocalRing.eq_maximalIdeal hI
    subst I
    have : Small.{v} (A ⧸ maximalIdeal A) := ‹Small.{v} (ResidueField A)›
    have : Small.{v} (M ⧸ N) := small_of_injective e.injective
    have : Small.{v} N := ih
    let s : M ⧸ N → M := Function.surjInv (Submodule.Quotient.mk_surjective N)
    have hs : ∀ q, N.mkQ (s q) = q := Function.surjInv_eq _
    apply small_of_surjective (f := fun p : N × (M ⧸ N) => (p.1 : M) + s p.2)
    intro m
    have hm : m - s (N.mkQ m) ∈ N := by
      apply (Submodule.Quotient.mk_eq_zero N).mp
      show N.mkQ (m - s (N.mkQ m)) = 0
      rw [map_sub, hs, sub_self]
    exact ⟨(⟨m - s (N.mkQ m), hm⟩, N.mkQ m), sub_add_cancel _ _⟩

private theorem small_artinianLocalRing
    (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [Small.{v} (ResidueField A)] : Small.{v} A :=
  small_of_finiteLength ((isArtinianRing_iff_isFiniteLength A).mp inferInstance)

-- Shrinking the Artinian lifting square requires several compatible algebra structures.
omit [IsNoetherianRing Λ] in
private theorem restrictedCoyoneda_lifts_implies_local_formallySmooth
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (hlift : ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A),
      Function.Surjective f.hom →
      ∀ (x : R ⟶ artinianToComplete.obj A),
        ∃ y : R ⟶ artinianToComplete.obj B,
          y ≫ artinianToComplete.map f = x) :
    let p := RingHom.ker (algebraMap Λ k)
    letI : p.IsMaximal := Algebra.ker_algebraMap_isMaximal_of_isIntegral Λ k
    RingHom.FormallySmoothNAdic.{max u v} (localizedStructureMap R rfl)
      (maximalIdeal R) := by
  let p := RingHom.ker (algebraMap Λ k)
  let : p.IsMaximal := Algebra.ker_algebraMap_isMaximal_of_isIntegral Λ k
  let T := Localization.AtPrime p
  let φ := localizedStructureMap R rfl
  let : IsLocalHom φ := localizedStructureMap_isLocalHom R rfl
  have hiff := (formallySmooth_adic_iff_lifts_local_squareZero.{max u v, u, v}
    (R := T) (S := R) φ).2 R.completeLocal.isNoetherian
  have hlocalLifts :
      ∀ (A : Type (max u v)) [CommRing A] [IsLocalRing A] (J : Ideal A)
        [IsLocalRing (A ⧸ J)], J ^ 2 = ⊥ →
        (∃ n : ℕ, 0 < n ∧ maximalIdeal A ^ n = ⊥) →
        InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom (Ideal.Quotient.mk J)) →
        ∀ (f : T →+* A)
          [IsLocalHom f] (gbar : R →+* A ⧸ J) [IsLocalHom gbar],
          gbar.comp φ = (Ideal.Quotient.mk J).comp f →
          Function.Bijective (IsLocalRing.ResidueField.map gbar) →
          ∃ g : R →+* A, IsLocalHom g ∧ g.comp φ = f ∧
            (Ideal.Quotient.mk J).comp g = gbar := by
    intro A _ _ J _ hJ hnil hsmall f hf gbar hgbar hcomm hbij
    rcases hsmall with ⟨hAlocal, hQlocal, hAartin, hQartin, hsurj, _⟩
    let q : A →+* A ⧸ J := Ideal.Quotient.mk J
    let fΛ : Λ →+* A := f.comp (algebraMap Λ T)
    let : Algebra Λ A := fΛ.toAlgebra
    let : Algebra Λ (A ⧸ J) := (q.comp fΛ).toAlgebra
    let : IsLocalHom q := IsLocalHom.of_surjective q hsurj
    let qAlg : A →ₐ[Λ] A ⧸ J :=
      { toRingHom := q
        commutes' := fun a => rfl }
    let : IsLocalHom qAlg := ⟨fun a ha =>
      (IsLocalHom.of_surjective q hsurj).map_nonunit a ha⟩
    let gbarAlg : R →ₐ[Λ] A ⧸ J :=
      { toRingHom := gbar
        commutes' := by
          intro a
          calc
            gbar (algebraMap Λ R a) = gbar (φ (algebraMap Λ T a)) :=
              congrArg gbar (RingHom.congr_fun (localizedStructureMap_comp R rfl) a).symm
            _ = q (f (algebraMap Λ T a)) := RingHom.congr_fun hcomm (algebraMap Λ T a)
            _ = algebraMap Λ (A ⧸ J) a := rfl }
    let : IsLocalHom gbarAlg := ⟨fun a ha => hgbar.map_nonunit a ha⟩
    let qres : IsLocalRing.ResidueField A →ₐ[Λ] IsLocalRing.ResidueField (A ⧸ J) :=
      IsLocalRing.ResidueField.mapAlgHom qAlg
    have hqres : Function.Bijective qres.toRingHom := by
      show Function.Bijective (IsLocalRing.ResidueField.map q)
      exact residueField_map_bijective_of_surjective q hsurj
    let qresEquiv : IsLocalRing.ResidueField A ≃ₐ[Λ]
        IsLocalRing.ResidueField (A ⧸ J) := AlgEquiv.ofBijective qres hqres
    let gres : IsLocalRing.ResidueField R →ₐ[Λ]
        IsLocalRing.ResidueField (A ⧸ J) := IsLocalRing.ResidueField.mapAlgHom gbarAlg
    let gresEquiv : IsLocalRing.ResidueField R ≃ₐ[Λ]
        IsLocalRing.ResidueField (A ⧸ J) :=
      AlgEquiv.ofBijective gres (by
        show Function.Bijective (IsLocalRing.ResidueField.map gbar)
        exact hbij)
    let eQ : IsLocalRing.ResidueField (A ⧸ J) ≃ₐ[Λ] k :=
      gresEquiv.symm.trans R.residueEquiv
    let eA : IsLocalRing.ResidueField A ≃ₐ[Λ] k := qresEquiv.trans eQ
    have : Small.{v} (ResidueField (A ⧸ J)) :=
      small_of_surjective gresEquiv.surjective
    have : Small.{v} (ResidueField A) := small_of_injective qresEquiv.injective
    have : Small.{v} A := small_artinianLocalRing A
    have : Small.{v} (A ⧸ J) := small_artinianLocalRing (A ⧸ J)
    let aE : Shrink.{v} A ≃ₐ[Λ] A := Shrink.algEquiv Λ A
    let qE : Shrink.{v} (A ⧸ J) ≃ₐ[Λ] (A ⧸ J) := Shrink.algEquiv Λ (A ⧸ J)
    let : IsLocalRing (Shrink.{v} A) :=
      IsLocalRing.of_surjective' aE.symm.toRingHom aE.symm.surjective
    let : IsLocalRing (Shrink.{v} (A ⧸ J)) :=
      IsLocalRing.of_surjective' qE.symm.toRingHom qE.symm.surjective
    let : IsArtinianRing (Shrink.{v} A) :=
      aE.symm.surjective.isArtinianRing
    let : IsArtinianRing (Shrink.{v} (A ⧸ J)) :=
      qE.symm.surjective.isArtinianRing
    let Aobj : ArtinianLocalAlgCat.{u, v, w} Λ k :=
      { carrier := Shrink.{v} A
        residueEquiv := (ResidueField.mapAlgEquiv aE).trans eA }
    let Qobj : ArtinianLocalAlgCat.{u, v, w} Λ k :=
      { carrier := Shrink.{v} (A ⧸ J)
        residueEquiv := (ResidueField.mapAlgEquiv qE).trans eQ }
    let fAlg : Aobj →ₐ[Λ] Qobj :=
      qE.symm.toAlgHom.comp (qAlg.comp aE.toAlgHom)
    have hfAlg : Function.Surjective fAlg :=
      qE.symm.surjective.comp (hsurj.comp aE.surjective)
    let fcat : ArtinianLocalAlgCat.Hom Aobj Qobj :=
      { hom := fAlg
        isLocal := IsLocalHom.of_surjective fAlg.toRingHom hfAlg
        residue_comm := by
          intro a
          show eQ (ResidueField.mapAlgEquiv qE (residue _ (fAlg a))) =
            eA (ResidueField.mapAlgEquiv aE (residue _ a))
          simp only [ResidueField.mapAlgEquiv_residue]
          show eQ (residue _ (qE (qE.symm (qAlg (aE a))))) = _
          rw [AlgEquiv.apply_symm_apply, ← ResidueField.mapAlgHom_residue qAlg]
          rfl }
    let : IsLocalHom qE.symm.toRingHom :=
      isLocalHom_of_leftInverse qE.toRingHom qE.apply_symm_apply
    let x : R ⟶ artinianToComplete.obj Qobj :=
      { hom := qE.symm.toAlgHom.comp gbarAlg
        isLocal := RingHom.isLocalHom_comp qE.symm.toRingHom gbar
        residue_comm := by
          intro r
          show eQ (ResidueField.mapAlgEquiv qE
            (residue _ (qE.symm (gbarAlg r)))) = R.residueEquiv (residue R r)
          rw [ResidueField.mapAlgEquiv_residue, AlgEquiv.apply_symm_apply,
            ← ResidueField.mapAlgHom_residue gbarAlg]
          show R.residueEquiv (gresEquiv.symm (gresEquiv (residue R r))) = _
          rw [AlgEquiv.symm_apply_apply] }
    obtain ⟨y', hy⟩ := hlift fcat hfAlg x
    let y := aE.toAlgHom.comp y'.hom
    have hqg : q.comp y.toRingHom = gbar := by
      ext r
      have hh := congrArg (fun h : CompleteLocalAlgCat.Hom _ _ =>
        qE (h.hom r)) hy
      change qE (qE.symm (q (aE (y'.hom r)))) = qE (qE.symm (gbar r)) at hh
      show q (aE (y'.hom r)) = gbar r
      simpa only [AlgEquiv.apply_symm_apply] using hh
    have hbase : (y.toRingHom.comp φ).comp (algebraMap Λ T) =
          f.comp (algebraMap Λ T) := by
      ext a
      calc
        y.toRingHom (φ (algebraMap Λ T a)) =
            y.toRingHom (algebraMap Λ R a) :=
          congrArg y.toRingHom (RingHom.congr_fun (localizedStructureMap_comp R rfl) a)
        _ = algebraMap Λ A a := y.commutes a
        _ = f (algebraMap Λ T a) := rfl
    have hgf : y.toRingHom.comp φ = f :=
      IsLocalization.ringHom_ext p.primeCompl hbase
    refine ⟨y.toRingHom, ⟨fun r hr => hgbar.map_nonunit r ?_⟩, hgf, hqg⟩
    rw [← RingHom.congr_fun hqg r]
    exact hr.map q
  exact formallySmoothNAdic_of_isFormallySmooth_adic φ (hiff.mpr hlocalLifts)

/-- **Stacks 0DYL.** Smoothness of the restricted representable category of `R`, formal
smoothness of `Λ → R` in the `m_R`-adic topology, and the two conditions combining flatness
with regularity of the special fibre over `k' = Λ / ker(Λ → k)`, are equivalent. -/
@[stacks 0DYL "conditions (1)--(4)",
  ega "0 19.7.1" "complete local case",
  ega "0 19.6.5" "complete, K=k: (2)⇔(3)", sga "7 VI 1.14" "Prorepresentable case"]
public theorem smooth_formallySmooth_flat_specialFibre_tfae
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    let k' := Λ ⧸ RingHom.ker (algebraMap Λ k)
    letI : (RingHom.ker (algebraMap Λ k)).IsMaximal :=
      Algebra.ker_algebraMap_isMaximal_of_isIntegral Λ k
    letI : Field k' := Ideal.Quotient.field _
    let Bbar := R ⊗[Λ] k'
    letI : Algebra k' Bbar := Algebra.TensorProduct.rightAlgebra
    List.TFAE [
      IsSmooth (restrictedCoyonedaProjection R),
      RingHom.FormallySmoothNAdic.{max u v} (algebraMap Λ R) (maximalIdeal R),
      Module.Flat Λ R ∧ Algebra.IsGeometricallyRegular k' Bbar,
      Module.Flat Λ R ∧
        RingHom.FormallySmoothNAdic.{max u v} (algebraMap k' Bbar)
          ((maximalIdeal R).map Algebra.TensorProduct.includeLeftRingHom)] := by
  dsimp only
  have h := formallySmooth_flat_specialFibre_tfae R
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hs
      let p := RingHom.ker (algebraMap Λ k)
      let : p.IsMaximal := Algebra.ker_algebraMap_isMaximal_of_isIntegral Λ k
      have hlocal := restrictedCoyoneda_lifts_implies_local_formallySmooth R
        ((restrictedCoyonedaProjection_lifts R).mp hs)
      exact (formallySmoothNAdic_iff_localizationBase p.primeCompl
        (algebraMap Λ R) (maximalIdeal R) (localizedStructureMap R rfl)
        (localizedStructureMap_comp R rfl) fun s =>
          structureMap_isUnit_of_not_mem_residueKernel R.residueEquiv s s.2).mpr hlocal
    · intro hf
      exact (restrictedCoyonedaProjection_smallLifts R).mpr
        (formallySmoothNAdic_smallLifts R hf)
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 2 ↔ 4 := h.out 1 3
  tfae_finish

end Deformation

end
