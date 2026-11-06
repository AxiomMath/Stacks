module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor
import StacksFrontier.Deformation.ArtinCriteria.TangentSpace
public import StacksFrontier.Deformation.Artin.Versality.NonversalThickening.ArtinianObjectsOverPoint
import all StacksFrontier.Deformation.Artin.Versality.NonversalThickening.SmallExtensionStages

/-!
# A first order thickening without local retraction (Stacks 0G2J)

The no-retraction clause over open neighbourhoods of the point, the small extension of Artinian
local algebras along which an arrow to `x` fails to extend when `x` is not versal, the kernel
`κ(u)` of the resulting one-point thickening, and the main result
`Deformation.Artin.exists_firstOrderThickening_without_localRetraction` (**Stacks 0G2J**).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal TopologicalSpace
open Stacks.Thickenings

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
attribute [local instance] Deformation.Artin.residueFieldAlgebra
attribute [local instance_reducible] AlgebraicGeometry.Scheme.residueField
attribute [local implicit_reducible] pullbackStages

private theorem specMap_residueMap_comp
    {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A C : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ C) :
    Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap C)) ≫
        Spec.map (CommRingCat.ofHom f.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact f.residue_comm r

private theorem subsingleton_spec_of_artinianLocal
    (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R] :
    Subsingleton (Spec (.of R)) := by
  constructor
  intro a b
  apply PrimeSpectrum.ext
  exact (IsLocalRing.eq_maximalIdeal
    ((IsArtinianRing.isPrime_iff_isMaximal a.asIdeal).mp a.isPrime)).trans
      (IsLocalRing.eq_maximalIdeal
        ((IsArtinianRing.isPrime_iff_isMaximal b.asIdeal).mp b.isPrime)).symm

open scoped Classical in
private theorem preimage_open_of_subsingleton
    {X Y : Scheme.{u}} [Subsingleton X] (f : X ⟶ Y) (x : X)
    (W : TopologicalSpace.Opens Y.carrier) :
    f ⁻¹ᵁ W = if f x ∈ W then ⊤ else ⊥ := by
  classical
  by_cases hx : f x ∈ W
  · rw [ite_eq_left hx]
    apply top_unique
    intro y _
    show f y ∈ W
    simpa only [Subsingleton.elim y x] using hx
  · rw [ite_eq_right hx]
    apply bot_unique
    intro y hy
    change f y ∈ W at hy
    exact hx (by simpa only [Subsingleton.elim y x] using hy)

/-- The no-retraction clause of **Stacks 0G2J**. If an arrow `aSmall` out of an object `smallY`
does not extend along `smallI`, then an object `yT` over `T` glued from `x` and `smallZ` admits
no retraction to `x` over an open subobject `W ⊆ T` containing the image of `u₀`, because the
second leg of the pushout factors through `W`. -/
private theorem no_localRetraction_of_failed_lift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {U T Z : AlgebraicGeometry.BigFppfOver B S hS} (iT : U ⟶ T) (jT : Z ⟶ T)
    {x smallY smallZ yT : F} (hx : p.obj x = U) (hZ : p.obj smallZ = Z)
    (hyT : p.obj yT = T)
    (smallI : smallY ⟶ smallZ) (aSmall : smallY ⟶ x)
    (hbadSmall : ∀ c : smallZ ⟶ x, smallI ≫ c ≠ aSmall)
    (rT : x ⟶ yT) (sT : smallZ ⟶ yT) (hglue : aSmall ≫ rT = smallI ≫ sT)
    (hrTmap : p.map rT = eqToHom hx ≫ iT ≫ eqToHom hyT.symm)
    (hsTmap : p.map sT = eqToHom hZ ≫ jT ≫ eqToHom hyT.symm)
    (u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U)
    (hjPoint : ∀ bpoint : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Z,
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map jT bpoint =
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iT u₀) :
    let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
    let iS := V.map iT
    ∀ (W : AlgebraicGeometry.BigFppfOver B S hS) (jW : W ⟶ T)
        (w₀ : V.obj W), V.map jW w₀ = iS u₀ → IsOpenImmersion (V.map jW) →
      ∀ (z : F) (hz : p.obj z = W) (s : z ⟶ yT),
        p.map s = eqToHom hz ≫ jW ≫ eqToHom hyT.symm →
        p.IsCartesian (p.map s) s →
        ¬ ∃ (β : z ⟶ x) (x' : F) (a : x' ⟶ x) (b : x' ⟶ z),
          p.IsCartesian (p.map a) a ∧
          p.IsCartesian (p.map b) b ∧
          IsPullback (V.map (p.map a ≫ eqToHom hx))
            (V.map (p.map b ≫ eqToHom hz)) iS (V.map jW) ∧
          a ≫ rT = b ≫ s ∧ b ≫ β = a := by
  intro V iS W jW w₀ hw₀ hjW z hz s hs hsc
  rintro ⟨β, x', ax, bz, hax, hbz, hpb, hcompat, hβ⟩
  have : IsOpenImmersion (V.map jW) := hjW
  have hRange : Set.range (V.map jT) ⊆ Set.range (V.map jW) := by
    rintro _ ⟨t, rfl⟩
    exact ⟨w₀, hw₀.trans (hjPoint t).symm⟩
  let gS := IsOpenImmersion.lift (V.map jW) (V.map jT) hRange
  have hgS : gS ≫ V.map jW = V.map jT := IsOpenImmersion.lift_fac _ _ _
  let gSite : Z ⟶ W :=
    Over.homMk (ObjectProperty.homMk gS) (by
      apply ObjectProperty.hom_ext
      show gS ≫ W.hom.hom = Z.hom.hom
      have hw : V.map jW ≫ T.hom.hom = W.hom.hom :=
        congrArg (fun f => f.hom) (Over.w jW)
      have hj : V.map jT ≫ T.hom.hom = Z.hom.hom :=
        congrArg (fun f => f.hom) (Over.w jT)
      rw [← hw, ← Category.assoc, hgS, hj])
  have hgSite : gSite ≫ jW = jT := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hgS
  let g : p.obj smallZ ⟶ p.obj z := eqToHom hZ ≫ gSite ≫ eqToHom hz.symm
  have hg : g ≫ p.map s = p.map sT := by
    rw [hs, hsTmap]
    dsimp only [g]
    simpa [Category.assoc] using congrArg
      (fun t => eqToHom hZ ≫ t ≫ eqToHom hyT.symm) hgSite
  have : Mono jW := Functor.mono_of_mono_map V (inferInstance : Mono (V.map jW))
  have : Mono (p.map s) := by rw [hs]; infer_instance
  have hpbBase : IsPullback (p.map ax ≫ eqToHom hx)
      (p.map bz ≫ eqToHom hz) iT jW :=
    IsPullback.of_map_of_faithful V hpb
  have hpbActual : IsPullback (p.map ax) (p.map bz) (p.map rT) (p.map s) :=
    hpbBase.of_iso (Iso.refl _) (eqToIso hx.symm) (eqToIso hz.symm)
      (eqToIso hyT.symm) (by simp) (by simp)
      (by simp [hrTmap]) (by simp [hs])
  exact no_retraction_of_failed_lift p hp smallI aSmall hbadSmall
    rT sT hglue s g hg ax bz hpbActual hcompat ⟨β, hβ⟩

/-- Non-versality at a finite type point produces a small extension `B' ⟶ A` of Artinian local
algebras in the deformation category of the point, an arrow of `𝒳` over the induced map of
affine schemes along which a given arrow to `x` does not extend, and the identification of the
residue point of `Spec A` with the point itself. -/
private theorem exists_smallExtension_failed_lift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (x : F) (hx : p.obj x = U)
    (u₀ : ((Over.post B.inclusion).obj U).left)
    (hnot : ¬ Deformation.Artin.IsVersalAt
      ((Over.post B.inclusion).obj U) (p ⋙ Over.post B.inclusion)
      u₀ x (congrArg (Over.post B.inclusion).obj hx)) :
    let U' := (Over.post B.inclusion).obj U
    let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
    let S₀ := B.inclusion.obj (B.obj hS)
    let Λ : Type u := S₀.presheaf.stalk (Deformation.Artin.basePoint U' u₀)
    let k : Type u := IsLocalRing.ResidueField (U'.left.1.presheaf.stalk u₀)
    letI : Field k := inferInstance
    letI : Algebra Λ k := Deformation.Artin.residueFieldAlgebra U' u₀
    let sMap := S₀.fromSpecStalk (Deformation.Artin.basePoint U' u₀)
    ∃ (smallA smallB : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (smallF : smallB ⟶ smallA)
      (_ : InfinitesimalLifting.IsSmallExtension
        (CommRingCat.ofHom smallF.hom.toRingHom))
      (hAs : B.Contains (Spec (.of smallA.carrier)))
      (hBs : B.Contains (Spec (.of smallB.carrier)))
      (smallY smallZ : F)
      (hY : p.obj smallY = @artinianLocalAlgOver.{u} B S hS Λ inferInstance sMap k
        inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) smallA hAs)
      (_ : p.obj smallZ = @artinianLocalAlgOver.{u} B S hS Λ inferInstance sMap k
        inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) smallB hBs)
      (smallI : smallY ⟶ smallZ)
      (_ : p.IsHomLift (@artinianLocalAlgOverMap.{u} B S hS Λ inferInstance sMap k
        inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) smallB smallA
        hBs hAs smallF) smallI)
      (aSmall : smallY ⟶ x),
      (∀ c : smallZ ⟶ x, smallI ≫ c ≠ aSmall) ∧
      Spec.map (CommRingCat.ofHom (@Deformation.Artin.residueMap Λ k inferInstance
          inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) smallA)) ≫
          V.map (eqToHom hY.symm ≫ p.map aSmall ≫ eqToHom hx) =
        U'.left.fromSpecResidueField u₀ := by
  classical
  intro U' V S₀ Λ k sMap
  let : Field k := inferInstance
  let : Algebra Λ k := Deformation.Artin.residueFieldAlgebra U' u₀
  have hUcontains : B.Contains (V.obj U) := U.left.2
  have hk : Cardinal.mk k ≤ (V.obj U).size :=
    AlgebraicGeometry.Space.residueField_size_le (V.obj U) u₀
  let q : F ⥤ Over S := p ⋙ Over.post B.inclusion
  have hbad := exists_failed_artinian_lift
    U' q u₀ x
    (congrArg (Over.post B.inclusion).obj hx) hnot
  rcases hbad with ⟨A, A₁, f, hf, y, z, hy, hz, i, hi, a, ha, hnoLift⟩
  have hAsite := artinianLocalAlg_spec_contains B hUcontains hk A
  have hA₁site := artinianLocalAlg_spec_contains B hUcontains hk A₁
  obtain ⟨n, chain, hleft, e, hfactor, hsmall⟩ :=
    Deformation.surjective_factors_into_smallExtensions f hf
  let : Category.{u, u + 1} (Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :=
    inferInstance
  have hchainSite : ∀ (j : ℕ) (hj : j ≤ n),
      let : Algebra Λ k := Deformation.Artin.residueFieldAlgebra U' u₀
      let Cj := chain.obj' j hj
      let : CommRing Cj.carrier := Cj.commRing
      B.Contains (Spec (.of Cj.carrier)) := by
    intro j hj
    let Cj := chain.obj' j hj
    let : CommRing Cj.carrier := Cj.commRing
    exact artinianLocalAlg_spec_contains B hUcontains hk Cj
  let : CommRing A.carrier := A.commRing
  let : CommRing A₁.carrier := A₁.commRing
  let : Algebra Λ A.carrier := A.algebra
  let : Algebra Λ A₁.carrier := A₁.algebra
  let ySite := @artinianLocalAlgOver.{u} B S hS Λ inferInstance sMap k
    inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) A hAsite
  let zSite := @artinianLocalAlgOver.{u} B S hS Λ inferInstance sMap k
    inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) A₁ hA₁site
  have hyPost : q.obj y = (Over.post (X := B.obj hS) B.inclusion).obj ySite :=
    hy.trans (@artinianLocalAlgOver_post.{u} B S hS Λ inferInstance sMap k
      inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) A hAsite).symm
  have hzPost : q.obj z = (Over.post (X := B.obj hS) B.inclusion).obj zSite :=
    hz.trans (@artinianLocalAlgOver_post.{u} B S hS Λ inferInstance sMap k
      inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) A₁ hA₁site).symm
  have hyA : p.obj y = ySite := bigFppfOver_post_injective B S hS hyPost
  have hzB : p.obj z = zSite := bigFppfOver_post_injective B S hS hzPost
  let yA := y
  let zB := z
  let iA := i
  let aA := a
  have hnoLiftA : ∀ b : zB ⟶ x, iA ≫ b ≠ aA := hnoLift
  let : p.IsFibered := hp.isFibered
  let stage : ∀ (j : ℕ) (hj : j ≤ n), AlgebraicGeometry.BigFppfOver B S hS :=
    fun j hj =>
      let : Algebra Λ k := Deformation.Artin.residueFieldAlgebra U' u₀
      let : Category.{u, u + 1} (Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) := inferInstance
      let Cj := chain.obj' j hj
      let : CommRing Cj.carrier := Cj.commRing
      let : Algebra Λ Cj.carrier := Cj.algebra
      @artinianLocalAlgOver.{u} B S hS Λ inferInstance sMap k
        inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) Cj (hchainSite j hj)
  let stageMap : ∀ (j : ℕ) (hj : j < n),
      stage (j + 1) (Nat.succ_le_of_lt hj) ⟶ stage j (Nat.le_of_lt hj) :=
    fun j hj =>
      let : Algebra Λ k := Deformation.Artin.residueFieldAlgebra U' u₀
      let : Category.{u, u + 1} (Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) := inferInstance
      let Cj := chain.obj' j (Nat.le_of_lt hj)
      let Cj1 := chain.obj' (j + 1) (Nat.succ_le_of_lt hj)
      let : CommRing Cj.carrier := Cj.commRing
      let : Algebra Λ Cj.carrier := Cj.algebra
      let : CommRing Cj1.carrier := Cj1.commRing
      let : Algebra Λ Cj1.carrier := Cj1.algebra
      @artinianLocalAlgOverMap.{u} B S hS Λ inferInstance sMap k
        inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) Cj Cj1
        (hchainSite j (Nat.le_of_lt hj))
        (hchainSite (j + 1) (Nat.succ_le_of_lt hj)) (chain.map' j (j + 1))
  let : CommRing chain.left.carrier := chain.left.commRing
  let : Algebra Λ chain.left.carrier := chain.left.algebra
  let stage0Iso := @artinianLocalAlgOverIsoOfEq.{u} B S hS Λ inferInstance sMap k
    inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) chain.left A₁
    (hchainSite 0 (Nat.zero_le n)) hA₁site hleft
  obtain ⟨z0, hz0, m0, hm0, hIso0⟩ :=
    exists_cartesian_iso_lift p stage0Iso.symm zB hzB
  let stages := pullbackStages p stage stageMap ⟨z0, hz0⟩
  let stagesDesc := pullbackStagesDesc p stage stageMap ⟨z0, hz0⟩
  have hcart_m0 : p.IsCartesian (p.map m0) m0 :=
    every_arrow_cartesian_of_isFiberedInGroupoids p hp m0
  let : CommRing chain.right.carrier := chain.right.commRing
  let : Algebra Λ chain.right.carrier := chain.right.algebra
  let stageNIso := @artinianLocalAlgOverIso.{u} B S hS Λ inferInstance sMap k
    inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) chain.right A
    (hchainSite n le_rfl) hAsite e
  let gstage : ∀ (j : ℕ) (hj : j ≤ n), stage n le_rfl ⟶ stage j hj :=
    fun j hj => @artinianLocalAlgOverMap.{u} B S hS Λ inferInstance sMap k
      inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) (chain.obj' j hj) chain.right
      (hchainSite j hj) (hchainSite n le_rfl) (chain.map' j n)
  have hgn : gstage n le_rfl = 𝟙 _ := by
    dsimp only [gstage]
    rw [chain.map'_self n]
    exact @artinianLocalAlgOverMap_id.{u} B S hS Λ inferInstance sMap k inferInstance
      (Deformation.Artin.residueFieldAlgebra U' u₀) chain.right (hchainSite n le_rfl)
  have hgs (j : ℕ) (hj : j < n) :
      gstage j (Nat.le_of_lt hj) =
        gstage (j + 1) (Nat.succ_le_of_lt hj) ≫ stageMap j hj := by
    have h := @artinianLocalAlgOverMap_comp.{u} B S hS Λ inferInstance sMap k inferInstance
      (Deformation.Artin.residueFieldAlgebra U' u₀) _ _ _
      (hchainSite j (Nat.le_of_lt hj)) (hchainSite (j + 1) (Nat.succ_le_of_lt hj))
      (hchainSite n le_rfl) (chain.map' j (j + 1)) (chain.map' (j + 1) n)
    have hc : chain.map' j (j + 1) ≫ chain.map' (j + 1) n = chain.map' j n :=
      (chain.map'_comp j (j + 1) n).symm
    rw [hc] at h
    exact h.symm
  have hdesc (j : ℕ) (hj : j ≤ n) :
      p.map (stagesDesc j hj) =
        eqToHom (stages n le_rfl).2 ≫ gstage j hj ≫ eqToHom (stages j hj).2.symm :=
    pullbackStagesDesc_map p stage stageMap ⟨z0, hz0⟩ gstage hgn hgs j hj
  let fSite := @artinianLocalAlgOverMap.{u} B S hS Λ inferInstance sMap k
    inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) A₁ A hA₁site hAsite f
  have hiSite' : eqToHom hyA.symm ≫ p.map i ≫ eqToHom hzB = fSite := by
    apply V.map_injective
    simp only [Functor.map_comp, eqToHom_map]
    exact hi
  have hiSite : p.map i = eqToHom hyA ≫ fSite ≫ eqToHom hzB.symm := by
    rw [← hiSite']
    simp
  have htotal : stageNIso.hom ≫ fSite = gstage 0 (Nat.zero_le n) ≫ stage0Iso.hom := by
    have hfe : f ≫ e.inv = eqToHom hleft.symm ≫ chain.hom := by
      rw [← hfactor, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]
    have h1 := @artinianLocalAlgOverMap_comp.{u} B S hS Λ inferInstance sMap k inferInstance
      (Deformation.Artin.residueFieldAlgebra U' u₀) _ _ _ hA₁site hAsite
      (hchainSite n le_rfl) f e.inv
    have h2 := @artinianLocalAlgOverMap_comp.{u} B S hS Λ inferInstance sMap k inferInstance
      (Deformation.Artin.residueFieldAlgebra U' u₀) _ _ _ hA₁site
      (hchainSite 0 (Nat.zero_le n)) (hchainSite n le_rfl)
      (eqToHom hleft.symm) chain.hom
    rw [← hfe] at h2
    have h3 : stage0Iso.hom = @artinianLocalAlgOverMap.{u} B S hS Λ inferInstance sMap k
        inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) _ _ hA₁site
        (hchainSite 0 (Nat.zero_le n)) (eqToHom hleft.symm) :=
      @artinianLocalAlgOverIsoOfEq_hom.{u} B S hS Λ inferInstance sMap k inferInstance
        (Deformation.Artin.residueFieldAlgebra U' u₀) _ _
        (hchainSite 0 (Nat.zero_le n)) hA₁site hleft
    rw [h3]
    exact h1.trans h2.symm
  have hm0map : p.map m0 = eqToHom hz0 ≫ stage0Iso.hom ≫ eqToHom hzB.symm := by
    let : p.IsHomLift stage0Iso.hom m0 := hm0
    exact IsHomLift.fac' p stage0Iso.hom m0
  let gn : p.obj (stages n le_rfl).1 ⟶ p.obj y :=
    eqToHom (stages n le_rfl).2 ≫ stageNIso.hom ≫ eqToHom hyA.symm
  have hnbase : gn ≫ p.map i = p.map (stagesDesc 0 (Nat.zero_le n) ≫ m0) := by
    rw [p.map_comp, hdesc, hm0map, hiSite]
    dsimp only [gn]
    simpa [Category.assoc] using congrArg
      (fun t => eqToHom (stages n le_rfl).2 ≫ t ≫ eqToHom hzB.symm) htotal
  obtain ⟨mN, ⟨hmNmap, hmNcomp⟩, _⟩ := hp.unique_lift i
    (stagesDesc 0 (Nat.zero_le n) ≫ m0) gn hnbase
  have : IsIso (p.map mN) := by rw [hmNmap]; dsimp only [gn]; infer_instance
  have : p.IsStronglyCartesian (p.map mN) mN :=
    Functor.IsFiberedInGroupoids.everyStronglyCartesian_of_fiberGroupoid hp.fiber_isGroupoid mN
  have : IsIso mN := Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map mN) mN
  have : IsIso m0 := hIso0
  let aN := mN ≫ a
  have hbad0 : ¬ ∃ b : (stages 0 (Nat.zero_le n)).1 ⟶ x,
      stagesDesc 0 (Nat.zero_le n) ≫ b = aN := by
    rintro ⟨b, hb⟩
    apply hnoLift (inv m0 ≫ b)
    apply (cancel_epi mN).mp
    rw [← Category.assoc, hmNcomp]
    simpa [Category.assoc, aN] using hb
  obtain ⟨j, hj, aSmall, haSmall, hbadSmall⟩ :=
    exists_failed_pullbackStage p stage stageMap ⟨z0, hz0⟩ aN hbad0
  let smallA := chain.obj' (j + 1) (Nat.succ_le_of_lt hj)
  let smallB := chain.obj' j (Nat.le_of_lt hj)
  let : CommRing smallA.carrier := smallA.commRing
  let : CommRing smallB.carrier := smallB.commRing
  let : Algebra Λ smallA.carrier := smallA.algebra
  let : Algebra Λ smallB.carrier := smallB.algebra
  let smallF : smallB ⟶ smallA := chain.map' j (j + 1)
  have hsmallF : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom smallF.hom.toRingHom) := hsmall j hj
  let smallY := (stages (j + 1) (Nat.succ_le_of_lt hj)).1
  let smallZ := (stages j (Nat.le_of_lt hj)).1
  let smallI : smallY ⟶ smallZ := pullbackStageArrow p stage stageMap ⟨z0, hz0⟩ j hj
  have hsmallI : p.IsHomLift (stageMap j hj) smallI :=
    pullbackStageArrow_isHomLift p stage stageMap ⟨z0, hz0⟩ j hj
  let smallASite := stage (j + 1) (Nat.succ_le_of_lt hj)
  let smallBSite := stage j (Nat.le_of_lt hj)
  let aSite : smallASite ⟶ U :=
    eqToHom (stages (j + 1) (Nat.succ_le_of_lt hj)).2.symm ≫ p.map aSmall ≫ eqToHom hx
  let φ : Spec (.of smallA.carrier) ⟶ V.obj U := V.map aSite
  let ψ : Spec (.of A.carrier) ⟶ V.obj U :=
    V.map (eqToHom hyA.symm ≫ p.map a ≫ eqToHom hx)
  have hnorm : gstage (j + 1) (Nat.succ_le_of_lt hj) ≫ aSite =
      stageNIso.hom ≫ eqToHom hyA.symm ≫ p.map a ≫ eqToHom hx := by
    have hh := congrArg (fun t => eqToHom (stages n le_rfl).2.symm ≫
      p.map t ≫ eqToHom hx) haSmall
    dsimp only [aN] at hh
    rw [p.map_comp, hdesc, p.map_comp, hmNmap] at hh
    simpa [aSite, gn, Category.assoc] using hh
  have hresidueA :
      Spec.map (CommRingCat.ofHom
        (@Deformation.Artin.residueMap Λ k inferInstance inferInstance
          (Deformation.Artin.residueFieldAlgebra U' u₀) smallA)) ≫ φ =
        U'.left.fromSpecResidueField u₀ := by
    have hψ : Spec.map (CommRingCat.ofHom
        (@Deformation.Artin.residueMap Λ k inferInstance inferInstance
          (Deformation.Artin.residueFieldAlgebra U' u₀) A)) ≫ ψ =
        U'.left.fromSpecResidueField u₀ := by
      rw [show ψ = _ from toScheme_map_eqToHom_comp B S hS p hyA hx a]
      exact ha
    have hnormBase :
        Spec.map (CommRingCat.ofHom (chain.map' (j + 1) n).hom.toRingHom) ≫ φ =
          Spec.map (CommRingCat.ofHom e.inv.hom.toRingHom) ≫ ψ := congrArg V.map hnorm
    have hh := congrArg (fun t =>
      Spec.map (CommRingCat.ofHom
        (@Deformation.Artin.residueMap Λ k inferInstance inferInstance
          (Deformation.Artin.residueFieldAlgebra U' u₀) chain.right)) ≫ t) hnormBase
    rw [← Category.assoc, @specMap_residueMap_comp.{u} Λ k inferInstance inferInstance
        (Deformation.Artin.residueFieldAlgebra U' u₀) _ _ (chain.map' (j + 1) n),
      ← Category.assoc, @specMap_residueMap_comp.{u} Λ k inferInstance inferInstance
        (Deformation.Artin.residueFieldAlgebra U' u₀) _ _ e.inv] at hh
    exact hh.trans hψ
  exact ⟨smallA, smallB, smallF, hsmallF, hchainSite (j + 1) (Nat.succ_le_of_lt hj),
    hchainSite j (Nat.le_of_lt hj), smallY, smallZ,
    (stages (j + 1) (Nat.succ_le_of_lt hj)).2, (stages j (Nat.le_of_lt hj)).2,
    smallI, hsmallI, aSmall, hbadSmall, hresidueA⟩

/-- The map `W ⟶ Spec (Γ(W, ⊤) ×_A B')` induced by a small extension `B' ⟶ A` is a first order
thickening. -/
private theorem isFirstOrderThickening_isoSpec_comp_pullbackCone_fst
    {W : Scheme.{u}} [IsAffine W] {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {smallB smallA : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (φRing : Γ(W, ⊤) ⟶ CommRingCat.of smallA.carrier) (smallF : smallB ⟶ smallA)
    (hsmallF : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom smallF.hom.toRingHom)) :
    Stacks.Thickenings.IsFirstOrderThickening (W.isoSpec.hom ≫ Spec.map
      (CommRingCat.pullbackCone φRing (CommRingCat.ofHom smallF.hom.toRingHom)).fst) := by
  have hi := specMap_pullbackCone_fst_isFirstOrderThickening_of_smallExtension
    φRing smallF hsmallF
  have := hi.1
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.Hom.ker_comp_of_isIso]
  exact hi.2

/-- Let `B' ⟶ A` be a small extension of Artinian local algebras whose residue field is that of
an affine scheme `W` at a point `u₀`, and let `Γ(W, ⊤) ⟶ A` be a map whose spectrum sends the
residue point to `u₀`. The spectrum of the fibre product `Γ(W, ⊤) ×_A B'` is a first order
thickening of `W`, and the kernel of its structure sheaf map is the direct image of the
structure sheaf of `Spec κ(u₀)` along the canonical inclusion of the point. -/
private theorem nonversalThickeningKernel
    {W : Scheme.{u}} [IsAffine W] (u₀ : W) {Λ : Type u} [CommRing Λ]
    [Algebra Λ ↥(W.residueField u₀)]
    {smallB smallA : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ ↥(W.residueField u₀)}
    (smallF : smallB ⟶ smallA)
    (hsmallF : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom smallF.hom.toRingHom))
    (φRing : Γ(W, ⊤) ⟶ CommRingCat.of smallA.carrier)
    (hres : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap smallA)) ≫
      Spec.map φRing ≫ W.isoSpec.inv = W.fromSpecResidueField u₀) :
    let P := CommRingCat.pullbackCone φRing (CommRingCat.ofHom smallF.hom.toRingHom)
    let iS : W ⟶ Spec P.pt := W.isoSpec.hom ≫ Spec.map P.fst
    Nonempty (kernel (SheafOfModules.unitToPushforwardObjUnit iS.toRingCatSheafHom) ≅
      (Scheme.Modules.pushforward ((Spec P.pt).fromSpecResidueField (iS u₀))).obj
        (SheafOfModules.unit
          (Spec ((Spec P.pt).residueField (iS u₀))).ringCatSheaf)) := by
  classical
  intro P iS
  let k : Type u := ↥(W.residueField u₀)
  let fRing : CommRingCat.of smallB.carrier ⟶ CommRingCat.of smallA.carrier :=
    CommRingCat.ofHom smallF.hom.toRingHom
  let φ : Spec (.of smallA.carrier) ⟶ W := Spec.map φRing ≫ W.isoSpec.inv
  let jS : Spec (.of smallB.carrier) ⟶ Spec P.pt := Spec.map P.snd
  have hpush : IsPushout (Spec.map fRing) φ jS iS :=
    affineSpec_pullbackCone_isPushout φRing fRing hsmallF.2.2.2.2.1 φ rfl
  have hthick : Stacks.Thickenings.IsFirstOrderThickening iS :=
    isFirstOrderThickening_isoSpec_comp_pullbackCone_fst φRing smallF hsmallF
  have hresidueIso : IsIso (iS.residueFieldMap u₀) := by
    let : IsClosedImmersion iS := hthick.1
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · exact RingHom.injective _
    · intro z
      obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective z
      obtain ⟨a, ha⟩ := iS.stalkMap_surjective u₀ b
      refine ⟨IsLocalRing.residue _ a, ?_⟩
      show IsLocalRing.ResidueField.map (iS.stalkMap u₀).hom
        (IsLocalRing.residue _ a) = _
      rw [IsLocalRing.ResidueField.map_residue, ha, hb]
  let residueP : P.pt ⟶ CommRingCat.of k :=
    CommRingCat.ofHom ((Deformation.Artin.residueMap smallB).comp P.snd.hom)
  have : IsClosedImmersion iS := hthick.1
  have : QuasiCompact iS := inferInstance
  have hqcKer : (kernel (SheafOfModules.unitToPushforwardObjUnit
      iS.toRingCatSheafHom)).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_kernel_unitToPushforwardObjUnit iS
  have : IsIso (Scheme.Modules.fromTildeΓ (R := P.pt)
      (kernel (SheafOfModules.unitToPushforwardObjUnit iS.toRingCatSheafHom))) :=
    (AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ _).mp hqcKer
  let η := SheafOfModules.unitToPushforwardObjUnit iS.toRingCatSheafHom
  let G := moduleSpecΓFunctor (R := P.pt)
  have : G.PreservesZeroMorphisms := ⟨by intro M N; rfl⟩
  have : G.IsRightAdjoint := (tilde.adjunction (R := P.pt)).isRightAdjoint
  let eΓ : G.obj (kernel η) ≅ kernel (G.map η) := PreservesKernel.iso G η
  let eP : ModuleCat.of P.pt P.pt ≅
      G.obj (SheafOfModules.unit (Spec P.pt).ringCatSheaf) :=
    (tilde.toTildeΓNatIso (R := P.pt)).app (ModuleCat.of P.pt P.pt) ≪≫
      G.mapIso (tildeSelf (R := P.pt))
  have heP (a : P.pt) : eP.hom.hom a = (Scheme.ΓSpecIso P.pt).inv.hom a := by
    rfl
  have hη (a : P.pt) :
      (G.map η).hom (eP.hom.hom a) =
        iS.appTop.hom ((Scheme.ΓSpecIso P.pt).inv.hom a) := by
    rw [heP]
    rfl
  have hηker (a : P.pt) :
      (G.map η).hom (eP.hom.hom a) = 0 ↔ P.fst.hom a = 0 := by
    rw [hη]
    show ((Spec.map P.fst).appTop ≫ W.isoSpec.hom.appTop).hom
      ((Scheme.ΓSpecIso P.pt).inv.hom a) = 0 ↔ _
    rw [CommRingCat.comp_apply]
    have : IsIso W.isoSpec.hom.appTop :=
      inferInstanceAs (IsIso (W.isoSpec.hom.app ⊤))
    have hfirst :
        (ConcreteCategory.hom (Spec.map P.fst).appTop
          ((Scheme.ΓSpecIso P.pt).inv.hom a) = 0) ↔
        P.fst.hom a = 0 := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rw [CommRingCat.comp_apply]
      show (ConcreteCategory.hom (Scheme.ΓSpecIso Γ(W, ⊤)).inv
        (P.fst.hom a) = 0) ↔ P.fst.hom a = 0
      constructor
      · intro h
        exact (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso Γ(W, ⊤)).inv).1 (by simpa using h)
      · intro h
        rw [h, map_zero]
    constructor
    · intro h
      apply hfirst.mp
      apply (ConcreteCategory.bijective_of_isIso W.isoSpec.hom.appTop).1
      simpa only [map_zero] using h
    · intro h
      rw [hfirst.mpr h, map_zero]
  let eJ : (G.map η).hom.ker ≃ₗ[P.pt] RingHom.ker P.fst.hom := by
    let fJ : (G.map η).hom.ker →ₗ[P.pt] RingHom.ker P.fst.hom := {
      toFun := fun z => ⟨eP.inv.hom z.1, by
        apply (hηker (eP.inv.hom z.1)).mp
        simp⟩
      map_add' := by
        intro z z'
        apply Subtype.ext
        exact map_add eP.inv.hom z.1 z'.1
      map_smul' := by
        intro c z
        apply Subtype.ext
        exact map_smul eP.inv.hom c z.1 }
    apply LinearEquiv.ofBijective fJ
    constructor
    · intro z z' h
      apply Subtype.ext
      apply (ConcreteCategory.bijective_of_isIso eP.inv).1
      exact congrArg Subtype.val h
    · intro z
      refine ⟨⟨eP.hom.hom z.1, ?_⟩, ?_⟩
      · exact (hηker z.1).mpr z.2
      · apply Subtype.ext
        exact eP.hom_inv_id_apply z.1
  let eK : G.obj (kernel η) ≅
      ModuleCat.of P.pt (RingHom.ker P.fst.hom) :=
    eΓ ≪≫ ModuleCat.kernelIsoKer (G.map η) ≪≫ eJ.toModuleIso
  let eSheaf : kernel η ≅
      tilde (ModuleCat.of P.pt (RingHom.ker P.fst.hom)) :=
    (asIso (Scheme.Modules.fromTildeΓ (R := P.pt) (kernel η))).symm ≪≫
      (tilde.functor P.pt).mapIso eK
  let : Module P.pt k :=
    Module.compHom k ((Deformation.Artin.residueMap smallB).comp P.snd.hom)
  let eKk := pullbackCone_smallExtension_kernel_linearEquiv_residueField
    φRing smallF hsmallF
  let eTilde : kernel η ≅ tilde (ModuleCat.of P.pt k) :=
    eSheaf ≪≫ (tilde.functor P.pt).mapIso eKk.toModuleIso
  let ePush : tilde (ModuleCat.of P.pt k) ≅
      (Scheme.Modules.pushforward (Spec.map residueP)).obj
        (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf) :=
    ((AlgebraicGeometry.pushforwardTildeIso
      P.pt (CommRingCat.of k) residueP).app (ModuleCat.of (CommRingCat.of k) k)).symm ≪≫
      (Scheme.Modules.pushforward (Spec.map residueP)).mapIso
        (tildeSelf (R := CommRingCat.of k))
  have hresidueMorphism :
      Spec.map residueP = W.fromSpecResidueField u₀ ≫ iS := by
    have h1 : Spec.map residueP =
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap smallB)) ≫ jS := by
      dsimp only [residueP, jS]
      rw [← Spec.map_comp]
      rfl
    have h2 : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap smallB)) ≫ jS =
        (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap smallA)) ≫
          Spec.map fRing) ≫ jS := by
      rw [specMap_residueMap_comp smallF]
    have h3 : (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap smallA)) ≫
          Spec.map fRing) ≫ jS =
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap smallA)) ≫ (φ ≫ iS) := by
      rw [Category.assoc, hpush.w]
    have h4 : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap smallA)) ≫ (φ ≫ iS) =
        W.fromSpecResidueField u₀ ≫ iS := by
      rw [← Category.assoc]
      exact congrArg (fun t => t ≫ iS) hres
    exact h1.trans (h2.trans (h3.trans h4))
  let : IsIso (iS.residueFieldMap u₀) := hresidueIso
  let fκ := Spec.map (iS.residueFieldMap u₀)
  let point := (Spec P.pt).fromSpecResidueField (iS u₀)
  have hfκ : Spec.map residueP = fκ ≫ point :=
    hresidueMorphism.trans (iS.SpecMap_residueFieldMap_fromSpecResidueField u₀).symm
  exact ⟨eTilde ≪≫ ePush ≪≫
    (Scheme.Modules.pushforwardCongr hfκ).app _ ≪≫
    (Scheme.Modules.pushforwardComp fκ point).symm.app _ ≪≫
    (Scheme.Modules.pushforward point).mapIso (AlgebraicGeometry.pushforwardUnitIso fκ)⟩

/-- **Stacks 0G2J.** If an object `x` of a category fibred in groupoids with (RS*) over the big
fppf site of a locally Noetherian scheme is not versal at a finite type point `u` of an affine
scheme `U` of finite type, then `x` extends to an object `y` over a first order thickening
`U ⟶ T` with ideal `κ(u)` which has no retraction to `x` over any open neighbourhood of `u`. -/
@[stacks 0G2J]
public theorem exists_firstOrderThickening_without_localRetraction
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hRS : Deformation.Artin.SatisfiesRSStar B S hS p hp)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (x : F)
    (hx : p.obj x = U)
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U)]
    [IsLocallyNoetherian S]
    [LocallyOfFiniteType ((Over.post B.inclusion).obj U).hom]
    (u₀ : ((Over.post B.inclusion).obj U).left)
    (_hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hnot : ¬ Deformation.Artin.IsVersalAt
      ((Over.post B.inclusion).obj U) (p ⋙ Over.post B.inclusion)
      u₀ x (congrArg (Over.post B.inclusion).obj hx)) :
    ∃ (T : AlgebraicGeometry.BigFppfOver B S hS) (i : U ⟶ T)
      (y : F) (hy : p.obj y = T) (r : x ⟶ y),
      let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
      let iS := V.map i
      (p.map r = eqToHom hx ≫ i ≫ eqToHom hy.symm) ∧
      Stacks.Thickenings.IsFirstOrderThickening iS ∧
      Epi (SheafOfModules.unitToPushforwardObjUnit iS.toRingCatSheafHom) ∧
      Nonempty (kernel (SheafOfModules.unitToPushforwardObjUnit
        iS.toRingCatSheafHom) ≅
        (Scheme.Modules.pushforward ((V.obj T).fromSpecResidueField (iS u₀))).obj
          (SheafOfModules.unit
            (Spec ((V.obj T).residueField (iS u₀))).ringCatSheaf)) ∧
      (∀ (W : AlgebraicGeometry.BigFppfOver B S hS) (j : W ⟶ T)
          (w₀ : V.obj W) (_ : V.map j w₀ = iS u₀)
          (_ : IsOpenImmersion (V.map j))
          (z : F) (hz : p.obj z = W) (s : z ⟶ y)
          (_ : p.map s = eqToHom hz ≫ j ≫ eqToHom hy.symm)
          (_ : p.IsCartesian (p.map s) s),
        ¬ ∃ (β : z ⟶ x) (x' : F) (a : x' ⟶ x) (b : x' ⟶ z),
          p.IsCartesian (p.map a) a ∧
          p.IsCartesian (p.map b) b ∧
          IsPullback
            (V.map (p.map a ≫ eqToHom hx))
            (V.map (p.map b ≫ eqToHom hz)) iS (V.map j) ∧
          a ≫ r = b ≫ s ∧ b ≫ β = a) := by
  classical
  let U' := (Over.post B.inclusion).obj U
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let S₀ := B.inclusion.obj (B.obj hS)
  let Λ : Type u := S₀.presheaf.stalk (Deformation.Artin.basePoint U' u₀)
  let k : Type u := IsLocalRing.ResidueField (U'.left.1.presheaf.stalk u₀)
  let : Field k := inferInstance
  let : Algebra Λ k := Deformation.Artin.residueFieldAlgebra U' u₀
  let sMap := S₀.fromSpecStalk (Deformation.Artin.basePoint U' u₀)
  have hUcontains : B.Contains (V.obj U) := U.left.2
  let : p.IsFibered := hp.isFibered
  obtain ⟨smallA, smallB, smallF, hsmallF, hAs, hBs, smallY, smallZ, hY, hZ,
    smallI, hsmallI, aSmall, hbadSmall, hresidueA⟩ :=
    exists_smallExtension_failed_lift B S hS p hp U x hx u₀ hnot
  let : CommRing smallA.carrier := smallA.commRing
  let : CommRing smallB.carrier := smallB.commRing
  let : Algebra Λ smallA.carrier := smallA.algebra
  let : Algebra Λ smallB.carrier := smallB.algebra
  let smallASite := @artinianLocalAlgOver.{u} B S hS Λ inferInstance sMap k
    inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) smallA hAs
  let smallBSite := @artinianLocalAlgOver.{u} B S hS Λ inferInstance sMap k
    inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) smallB hBs
  let fArrow : smallASite ⟶ smallBSite :=
    @artinianLocalAlgOverMap.{u} B S hS Λ inferInstance sMap k
      inferInstance (Deformation.Artin.residueFieldAlgebra U' u₀) smallB smallA hBs hAs smallF
  let aSite : smallASite ⟶ U := eqToHom hY.symm ≫ p.map aSmall ≫ eqToHom hx
  let φ : Spec (.of smallA.carrier) ⟶ V.obj U := V.map aSite
  let φRing : Γ(V.obj U, ⊤) ⟶ CommRingCat.of smallA.carrier :=
    Spec.preimage (φ ≫ (V.obj U).isoSpec.hom)
  have hφ : Spec.map φRing ≫ (V.obj U).isoSpec.inv = φ := by
    dsimp only [φRing]
    rw [Spec.map_preimage]
    simp
  let fRing : CommRingCat.of smallB.carrier ⟶ CommRingCat.of smallA.carrier :=
    CommRingCat.ofHom smallF.hom.toRingHom
  let P := CommRingCat.pullbackCone φRing fRing
  let TS := Spec P.pt
  have hTsite : B.Contains TS :=
    pullbackCone_spec_contains B hUcontains φRing fRing hBs
  let iS : V.obj U ⟶ TS := (V.obj U).isoSpec.hom ≫ Spec.map P.fst
  let jS : Spec (.of smallB.carrier) ⟶ TS := Spec.map P.snd
  have hpush : IsPushout (Spec.map fRing) φ jS iS :=
    affineSpec_pullbackCone_isPushout φRing fRing hsmallF.2.2.2.2.1 φ hφ
  have hcommBase : φ ≫ U.hom.hom = Spec.map fRing ≫ smallBSite.hom.hom := by
    show (aSite.left.hom ≫ U.hom.hom) =
      fArrow.left.hom ≫ smallBSite.hom.hom
    show (aSite.left ≫ U.hom).hom = (fArrow.left ≫ smallBSite.hom).hom
    rw [Over.w aSite, Over.w fArrow]
  let tS : TS ⟶ S := hpush.desc smallBSite.hom.hom U.hom.hom hcommBase.symm
  have hjS : jS ≫ tS = smallBSite.hom.hom :=
    hpush.inl_desc _ _ hcommBase.symm
  have hiS : iS ≫ tS = U.hom.hom := hpush.inr_desc _ _ hcommBase.symm
  let T : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (X := B.obj hTsite) (Y := B.obj hS) tS)
  let iT : U ⟶ T := Over.homMk (ObjectProperty.homMk iS)
    (by apply ObjectProperty.hom_ext; exact hiS)
  let jT : smallBSite ⟶ T := Over.homMk (ObjectProperty.homMk jS)
    (by apply ObjectProperty.hom_ext; exact hjS)
  have hthick : Stacks.Thickenings.IsFirstOrderThickening (V.map iT) :=
    isFirstOrderThickening_isoSpec_comp_pullbackCone_fst φRing smallF hsmallF
  have hsq : aSite ≫ iT = fArrow ≫ jT := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hpush.w.symm
  let AA : AlgebraicGeometry.BigAffineFppf B S hS :=
    ⟨smallASite, inferInstanceAs (IsAffine (Spec (.of smallA.carrier)))⟩
  let BB : AlgebraicGeometry.BigAffineFppf B S hS :=
    ⟨smallBSite, inferInstanceAs (IsAffine (Spec (.of smallB.carrier)))⟩
  let UU : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U, inferInstance⟩
  let TT : AlgebraicGeometry.BigAffineFppf B S hS := ⟨T, inferInstanceAs (IsAffine TS)⟩
  have hΓ : IsPullback (V.map iT).appTop (V.map jT).appTop
      (V.map aSite).appTop (V.map fArrow).appTop :=
    hpush.op.map Scheme.Γ
  have hsmallThick : Stacks.Thickenings.IsFirstOrderThickening (V.map fArrow) :=
    specMap_isFirstOrderThickening fRing hsmallF.2.2.2.2.1
      (smallExtension_kernel_sq_zero smallF hsmallF)
  have : IsClosedImmersion (V.map fArrow) := hsmallThick.1
  have : IsAffine (V.obj (smallBSite)) :=
    inferInstanceAs (IsAffine (Spec (.of smallB.carrier)))
  have hfΓ : Function.Surjective (V.map fArrow).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (V.map fArrow)).2
  have hkΓ : RingHom.ker (V.map fArrow).appTop.hom ^ 2 = ⊥ :=
    specMap_appTop_ker_sq fRing (smallExtension_kernel_sq_zero smallF hsmallF)
  have hcomp : (Deformation.Artin.fiberSquareComparison p (Functor.chosenPullbacks p)
      aSite fArrow iT jT hsq).IsEquivalence :=
    hRS AA UU BB TT (ObjectProperty.homMk aSite) (ObjectProperty.homMk fArrow)
      (ObjectProperty.homMk iT) (ObjectProperty.homMk jT)
      (by apply ObjectProperty.hom_ext; exact hsq) hΓ hfΓ hkΓ
  have : p.IsHomLift aSite aSmall := by
    apply IsHomLift.of_fac p aSite aSmall
      hY hx
    simp [aSite]
  have : p.IsHomLift fArrow smallI := hsmallI
  obtain ⟨yT, rT, sT, hrT, hsT, hglue⟩ :=
    exists_glued_object_of_fiberSquareComparison p hp (Functor.chosenPullbacks p)
      aSite fArrow iT jT hsq hcomp
      ⟨smallY, hY⟩ ⟨x, hx⟩
      ⟨smallZ, hZ⟩ aSmall smallI
  let kpoint := IsLocalRing.closedPoint k
  let pointA : Spec (.of smallA.carrier) :=
    Spec.map (CommRingCat.ofHom
      (@Deformation.Artin.residueMap Λ k inferInstance inferInstance
        (Deformation.Artin.residueFieldAlgebra U' u₀) smallA)) kpoint
  have hpointA : φ pointA = u₀ := by
    have hv := congrArg (fun t => t kpoint) hresidueA
    exact hv.trans (Scheme.fromSpecResidueField_apply (X := U'.left) u₀ kpoint)
  have : IsArtinianRing smallB.carrier := smallB.isArtinianRing
  have : IsLocalRing smallB.carrier := smallB.isLocalRing
  have : Subsingleton (Spec (.of smallB.carrier)) :=
    subsingleton_spec_of_artinianLocal smallB.carrier
  have hjPoint (bpoint : Spec (.of smallB.carrier)) : jS bpoint = iS u₀ := by
    rw [Subsingleton.elim bpoint (Spec.map fRing pointA)]
    have hh := congrArg (fun t => t pointA) hpush.w
    simpa only [Scheme.Hom.comp_apply, hpointA] using hh
  have : p.IsHomLift iT rT := hrT
  have : p.IsHomLift jT sT := hsT
  have hrTmap : p.map rT = eqToHom hx ≫ iT ≫ eqToHom yT.2.symm :=
    IsHomLift.fac' p iT rT
  have hsTmap : p.map sT = eqToHom hZ ≫
      jT ≫ eqToHom yT.2.symm := IsHomLift.fac' p jT sT
  have hnoRet := no_localRetraction_of_failed_lift B S hS p hp iT jT hx
    hZ yT.2 smallI aSmall hbadSmall rT sT hglue
    hrTmap hsTmap u₀ hjPoint
  have hEpi : Epi (SheafOfModules.unitToPushforwardObjUnit (V.map iT).toRingCatSheafHom) := by
    have hc := ((Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae
      (V.map iT)).out 1 4).mp hthick.1
    exact hc.2
  refine ⟨T, iT, yT.1, yT.2, rT, hrTmap, hthick, hEpi, ?_, hnoRet⟩
  exact @nonversalThickeningKernel.{u} (V.obj U) inferInstance u₀ Λ inferInstance
    (Deformation.Artin.residueFieldAlgebra U' u₀) smallB smallA smallF hsmallF φRing
    (by rw [hφ]; exact hresidueA)

end Deformation.Artin

end
