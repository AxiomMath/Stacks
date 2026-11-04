module

public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal

/-!
# The lifting property defining versality, reduced to small extensions

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`, and let `x` be an object
of `𝒳` over a scheme `U`. Versality of `x` at a point (Stacks 07XF) is the lifting property
`Deformation.Artin.LiftsAtResiduePoint` against all surjections `B ⟶ A` of Artinian local
algebras. This file shows that it suffices to test it against small extensions (Stacks 06GD),
because every surjection factors as a composite of small extensions (Stacks 06GE).

## Main results

* `Deformation.Artin.liftsAtResiduePoint_of_isSmallExtension`: the reduction.

## Implementation notes

The lifting property against a composite `B ⟶ C ⟶ A` follows from the lifting properties against
`B ⟶ C` and against `C ⟶ A`: a lifting problem over `B ⟶ A` is factored through the restriction
of its object over `Spec B` to `Spec C`, which is formed by a cartesian arrow of `𝒳` over the
morphism of the site `Spec C ⟶ Spec B`; that `Spec C` belongs to the site follows from the
surjectivity of `B ⟶ C`. Against an isomorphism the lifting property holds because an arrow of a
category fibred in groupoids lying over an isomorphism is an isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

namespace Deformation.Artin

universe u v w

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (U : Over S) (x : F) (hx : (p ⋙ Over.post B.inclusion).obj x = U)
  (κ : Spec (.of k) ⟶ U.left)

/-- The lifting property of `x` at `κ` against one morphism of Artinian local algebras. -/
abbrev LiftsAlong {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A' ⟶ A) : Prop :=
  ∀ (y z : F)
    (hy : (p ⋙ Over.post B.inclusion).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (hz : (p ⋙ Over.post B.inclusion).obj z =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ))
    (i : y ⟶ z), schemeMap (p ⋙ Over.post B.inclusion) hy hz i =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) →
    ∀ a : y ⟶ x,
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
        schemeMap (p ⋙ Over.post B.inclusion) hy hx a = κ →
      ∃ b : z ⟶ x, i ≫ b = a

include hp in
/-- The lifting property against an isomorphism. -/
theorem liftsAlong_of_isIso {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A' ⟶ A) [IsIso f] : LiftsAlong B S hS p iΛ U x hx κ f := by
  intro y z hy hz i hi a _
  have hiso : IsIso (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) := by
    have : IsIso (CommRingCat.ofHom f.hom.toRingHom) := by
      refine ⟨⟨CommRingCat.ofHom (inv f).hom.toRingHom, ?_, ?_⟩⟩
      · ext a
        exact congrArg (fun g : A' ⟶ A' => g.hom a) (IsIso.hom_inv_id f)
      · ext a
        exact congrArg (fun g : A ⟶ A => g.hom a) (IsIso.inv_hom_id f)
    infer_instance
  have hqi : IsIso ((p ⋙ Over.post B.inclusion).map i).left := by
    have : ((p ⋙ Over.post B.inclusion).map i).left =
        eqToHom (congrArg Over.left hy) ≫ Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
          eqToHom (congrArg Over.left hz).symm := by
      rw [← hi]
      simp only [schemeMap, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
        eqToHom_trans_assoc, Category.id_comp]
    rw [this]
    infer_instance
  have hpi : IsIso (p.map i) := by
    have : IsIso ((Over.post B.inclusion).map (p.map i)) := by
      have : IsIso ((Over.forget S).map ((Over.post B.inclusion).map (p.map i))) := hqi
      exact isIso_of_reflects_iso _ (Over.forget S)
    exact isIso_of_reflects_iso _ (Over.post B.inclusion)
  have := hp.isStronglyCartesian_homLift (p.map i) i
  have : IsIso i := IsStronglyCartesian.isIso_of_base_isIso p (p.map i) i
  exact ⟨inv i ≫ a, by simp⟩

/-- The spectrum of a quotient of a ring whose spectrum lies in the site lies in the site. -/
theorem contains_spec_of_surjective {R R' : Type u} [CommRing R] [CommRing R']
    (g : R →+* R') (hg : Function.Surjective g) (hR : B.Contains (Spec (.of R))) :
    B.Contains (Spec (.of R')) := by
  refine lt_of_le_of_lt ?_ hR
  rw [Scheme.size_Spec, Scheme.size_Spec]
  exact max_le_max le_rfl (Cardinal.mk_le_of_surjective hg)

/-- The scheme map underlying an arrow of `𝒳` lying over a morphism of the site. -/
theorem schemeMap_of_isHomLift {y z : F} {Y Z : Over S}
    (hy : (p ⋙ Over.post B.inclusion).obj y = Y) (hz : (p ⋙ Over.post B.inclusion).obj z = Z)
    (m : p.obj y ⟶ p.obj z) (φ : y ⟶ z) (hφ : p.map φ = m) :
    schemeMap (p ⋙ Over.post B.inclusion) hy hz φ =
      eqToHom (congrArg Over.left hy).symm ≫ B.inclusion.map m.left ≫
        eqToHom (congrArg Over.left hz) := by
  subst hφ
  rfl

/-- The scheme map underlying an arrow of `𝒳` lying over a morphism of the site out of the
base of its source. -/
theorem schemeMap_of_isHomLift' {y z : F} {T : AlgebraicGeometry.BigFppfOver B S hS}
    {Y Z : Over S} (hyT : p.obj y = T) (hTY : (Over.post B.inclusion).obj T = Y)
    (hz : (p ⋙ Over.post B.inclusion).obj z = Z) (m : T ⟶ p.obj z) (φ : y ⟶ z)
    [p.IsHomLift m φ] (hy : (p ⋙ Over.post B.inclusion).obj y = Y) :
    schemeMap (p ⋙ Over.post B.inclusion) hy hz φ =
      eqToHom (congrArg Over.left hTY).symm ≫ B.inclusion.map m.left ≫
        eqToHom (congrArg Over.left hz) := by
  subst hyT hTY
  have h := IsHomLift.fac' p m φ
  simp only [schemeMap, Functor.comp_map, h, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

include hp in
/-- **Lifting along a composite.** If `g : A'' ⟶ C` is surjective, the lifting property against
`g ≫ h` follows from the lifting properties against `g` and against `h`. -/
theorem liftsAlong_comp {A A'' C : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (g : A'' ⟶ C) (h : C ⟶ A) (hg : Function.Surjective g.hom)
    (Hg : LiftsAlong B S hS p iΛ U x hx κ g)
    (Hh : ∀ κ' : Spec (.of k) ⟶ U.left, κ' = κ → LiftsAlong B S hS p iΛ U x hx κ' h) :
    LiftsAlong B S hS p iΛ U x hx κ (g ≫ h) := by
  intro y z hy hz i hi a ha
  let : p.IsFibered := hp.isFibered
  let q := p ⋙ Over.post B.inclusion
  -- the object over `Spec C`
  have hzl : B.inclusion.obj (p.obj z).left = Spec (.of A'') := congrArg Over.left hz
  have hzB : B.Contains (Spec (.of A'')) := hzl ▸ (p.obj z).left.2
  have hC : B.Contains (Spec (.of C)) :=
    contains_spec_of_surjective B g.hom.toRingHom hg hzB
  let TC : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ) :
      B.obj hC ⟶ B.obj hS)
  let mS : Spec (.of C) ⟶ B.inclusion.obj (p.obj z).left :=
    Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ eqToHom hzl.symm
  have hmS : mS ≫ B.inclusion.map (p.obj z).hom =
      Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ := by
    have hw : eqToHom hzl.symm ≫ B.inclusion.map (p.obj z).hom =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A'')) ≫ iΛ := by
      have key : ∀ {T : Scheme.{u}} {X : Over S} {f : T ⟶ S} (h : X = Over.mk f),
          eqToHom (congrArg Over.left h).symm ≫ X.hom = f := by
        intro T X f h
        subst h
        simp
      exact key hz
    simp only [mS, Category.assoc, hw]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    exact g.hom.commutes c
  let m : TC ⟶ p.obj z := Over.homMk (B.inclusion.preimage mS) (B.inclusion.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage]
    exact hmS))
  obtain ⟨zC, φ, hφ⟩ := hp.exists_lift m z rfl
  have hzCT : p.obj zC = TC := IsHomLift.domain_eq p m φ
  have hzC : q.obj zC = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ) := by
    change (Over.post B.inclusion).obj (p.obj zC) = _
    rw [hzCT]
    rfl
  have hφS : schemeMap q hzC hz φ = Spec.map (CommRingCat.ofHom g.hom.toRingHom) := by
    refine (schemeMap_of_isHomLift' B S hS p hzCT rfl hz m φ hzC).trans ?_
    simp only [m, mS, Over.homMk_left, Functor.map_preimage, eqToHom_refl, Category.id_comp]
    have key : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h1 : Y = Z) (h2 : Z = Y),
        (f ≫ eqToHom h1) ≫ eqToHom h2 = f := by
      intro X Y Z f h1 h2
      subst h1
      simp
    exact key _ _ _
  -- the factorization of `i` through the object over `Spec C`
  have hspec : Spec.map (CommRingCat.ofHom (g ≫ h).hom.toRingHom) =
      Spec.map (CommRingCat.ofHom h.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.hom.toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  have hover : Spec.map (CommRingCat.ofHom h.hom.toRingHom) ≫
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ)).hom =
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)).hom := by
    change _ ≫ Spec.map _ ≫ iΛ = Spec.map _ ≫ iΛ
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    exact h.hom.commutes c
  obtain ⟨iC, ⟨hiC, hiCφ⟩, -⟩ := factor_through_cartesian_schemeMap B S hS p hp hy hzC hz φ i
    (Spec.map (CommRingCat.ofHom h.hom.toRingHom)) hover (by rw [hφS, ← hspec, hi])
  obtain ⟨bC, hbC⟩ := Hh κ rfl y zC hy hzC iC hiC a ha
  have hres : Spec.map (CommRingCat.ofHom (residueMap C)) ≫ schemeMap q hzC hx bC = κ := by
    have hRC : Spec.map (CommRingCat.ofHom (residueMap C)) =
        Spec.map (CommRingCat.ofHom (residueMap A)) ≫
          Spec.map (CommRingCat.ofHom h.hom.toRingHom) := by
      rw [← Spec.map_comp]
      congr 1
      exact congrArg CommRingCat.ofHom (residueMap_comp h).symm
    calc Spec.map (CommRingCat.ofHom (residueMap C)) ≫ schemeMap q hzC hx bC
        = Spec.map (CommRingCat.ofHom (residueMap A)) ≫
            (Spec.map (CommRingCat.ofHom h.hom.toRingHom) ≫ schemeMap q hzC hx bC) := by
          rw [hRC, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (residueMap A)) ≫ schemeMap q hy hx (iC ≫ bC) := by
          rw [schemeMap_comp q hy hzC hx, hiC]
      _ = κ := by rw [hbC]; exact ha
  obtain ⟨b, hb⟩ := Hg zC z hzC hz φ hφS bC hres
  exact ⟨b, by rw [← hiCφ, Category.assoc, hb, hbC]⟩

include hp in
/-- **Versality from small extensions** (Stacks 06GE). If `x` has the lifting property at `κ`
against every small extension of Artinian local algebras, it has it against every surjection. -/
theorem liftsAtResiduePoint_of_isSmallExtension
    (H : ∀ {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A' ⟶ A),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
      LiftsAlong B S hS p iΛ U x hx κ f) :
    LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion) U x hx κ := by
  intro A A' f hf
  obtain ⟨n, Fc, hB, e, hcomp, hsmall⟩ := Deformation.surjective_factors_into_smallExtensions f hf
  have hsurjStep : ∀ (j : ℕ) (hj : j < n), Function.Surjective (Fc.map' j (j + 1)).hom :=
    fun j hj => (hsmall j hj).2.2.2.2.1
  -- the lifting property along every tail of the chain
  have htail : ∀ m (hm : m ≤ n), LiftsAlong B S hS p iΛ U x hx κ (Fc.map' m n) ∧
      Function.Surjective (Fc.map' m n).hom := by
    intro m hm
    induction h : n - m generalizing m with
    | zero =>
      have hmn : m = n := by omega
      subst hmn
      rw [Fc.map'_self m le_rfl]
      exact ⟨liftsAlong_of_isIso B S hS p hp iΛ U x hx κ _, fun a => ⟨a, rfl⟩⟩
    | succ d ih =>
      have hmn : m < n := by omega
      obtain ⟨hrest, hrestS⟩ := ih (m + 1) (by omega) (by omega)
      have hc : Fc.map' m n = Fc.map' m (m + 1) ≫ Fc.map' (m + 1) n := Fc.map'_comp m (m + 1) n
      rw [hc]
      refine ⟨liftsAlong_comp B S hS p hp iΛ U x hx κ _ _ (hsurjStep m hmn)
        (H _ (hsmall m hmn)) (fun κ' hκ' => hκ' ▸ hrest), ?_⟩
      intro a
      obtain ⟨b, rfl⟩ := hrestS a
      obtain ⟨c, rfl⟩ := hsurjStep m hmn b
      exact ⟨c, rfl⟩
  obtain ⟨hall, hallS⟩ := htail 0 (Nat.zero_le n)
  have h1 : LiftsAlong B S hS p iΛ U x hx κ (Fc.hom ≫ e.hom) :=
    liftsAlong_comp B S hS p hp iΛ U x hx κ _ _ hallS hall
      (fun κ' _ => liftsAlong_of_isIso B S hS p hp iΛ U x hx κ' _)
  have h2 : LiftsAlong B S hS p iΛ U x hx κ (eqToHom hB.symm ≫ Fc.hom ≫ e.hom) := by
    refine liftsAlong_comp B S hS p hp iΛ U x hx κ _ _ ?_
      (liftsAlong_of_isIso B S hS p hp iΛ U x hx κ _) (fun κ' hκ' => hκ' ▸ h1)
    intro a
    subst hB
    exact ⟨a, by simp⟩
  rw [hcomp] at h2
  exact h2

end Deformation.Artin
