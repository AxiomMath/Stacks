module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.VanKampen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.UnderlyingSpace

/-!
# Products with spectra obtained from finite products of a field

Let `A` be a filtered colimit of finite products of copies of a field `k`.  For every
`k`-scheme `X`, the underlying topological space of `Spec A ×_k X` is the product of the
underlying spaces of `Spec A` and `X`.  At a finite stage `Fin n → k` the fibre product is the
`n`-fold disjoint union of `X`, hence already such a product, and both sides commute with the
cofiltered limit over the stages.

## Main definitions

* `AlgebraicGeometry.IsFilteredColimitOfFiniteProducts` says that a `k`-algebra is a filtered
  colimit of finite products of copies of `k`.

## Main results

* `AlgebraicGeometry.isHomeomorph_pullback_to_product` states that the canonical map from the
  underlying space of the fibre product to the product of the underlying spaces is a
  homeomorphism.

## Implementation notes

The equality of topological spaces in the source is expressed intrinsically: the canonical map
whose components are the two pullback projections is a homeomorphism.  A finite product of
copies of `k` is represented as the function algebra `Fin n → k`.

## References

* [Stacks Project, Tag 0B7T](https://stacks.math.columbia.edu/tag/0B7T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

namespace AlgebraicGeometry

universe u

/-- A `k`-algebra is a filtered colimit of finite products of copies of `k`. -/
def IsFilteredColimitOfFiniteProducts
    (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] : Prop :=
  ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
    (F : Functor I (CommAlgCat.{u} k)) (c : Cocone F),
    Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ CommAlgCat.of k A) ∧
      ∀ i, ∃ n : ℕ, Nonempty (F.obj i ≅ CommAlgCat.of k (Fin n → k))

/-- The fibre product of `X` with the spectrum of a finite product of copies of `k` is the
disjoint union of copies of `X`. -/
private noncomputable def finiteProdPullbackIso (k : CommRingCat.{u}) {J : Type u} [Finite J]
    [Small.{u} J]
    (X : Scheme.{u}) (f : X ⟶ Spec k) :
    (pullback (Spec.map (CommRingCat.ofHom (algebraMap k (J → (k : Type u))))) f) ≅
      (∐ fun _ : J => X) := by
  let S : Scheme.{u} := Spec k
  let α : J → Scheme.{u} := fun _ => S
  let β : J → Scheme.{u} := fun _ => X
  let a : Cofan α := Cofan.mk (∐ α) (Sigma.ι α)
  let ha : IsColimit a := coproductIsCoproduct α
  let e : (∐ fun _ : J => S) ≅ Spec (CommRingCat.of (J → (k : Type u))) :=
    asIso (sigmaSpec (fun _ : J => k))
  let v : Spec (CommRingCat.of (J → (k : Type u))) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap k (J → (k : Type u))))
  let w : S ⟶ S := 𝟙 S
  let u0 : a.pt ⟶ S := Sigma.desc (fun _ => w)
  have heu : e.hom ≫ v = u0 := by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι α i ≫ sigmaSpec (fun _ : J => k) ≫ v =
      Sigma.ι α i ≫ Sigma.desc (fun _ : J => w)
    rw [← Category.assoc, ι_sigmaSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hr : (Pi.evalRingHom (fun _ : J => (k : Type u)) i).comp
        (algebraMap k (J → (k : Type u))) = RingHom.id k := by
      ext x
      rfl
    rw [hr]
    simp [w, S]
  have hvk : IsUniversalColimit a :=
    (FinitaryExtensive.isVanKampen_finiteCoproducts ha).isUniversal
  let hcomp : ∀ i : J, IsPullback f (𝟙 X) (𝟙 S) f := fun _ => IsPullback.of_id_snd
  let d : Cofan β := Cofan.mk (∐ β) (Sigma.ι β)
  let hd : IsColimit d := coproductIsCoproduct β
  have hpull : IsPullback (Cofan.IsColimit.desc hd (fun i => f ≫ a.inj i))
      (Cofan.IsColimit.desc hd (fun _ => 𝟙 X)) u0 f :=
    hvk.isPullback_of_isColimit_right (a := a) (f := fun _ : J => 𝟙 S)
      (u := u0) (v := f) (q₁ := fun _ : J => f) (q₂ := fun _ : J => 𝟙 X)
      (hP := hcomp) (d := d) hd
  have hpull' : IsPullback
      (Cofan.IsColimit.desc hd (fun i => f ≫ a.inj i) ≫ e.hom)
      (Cofan.IsColimit.desc hd (fun _ => 𝟙 X)) v f :=
    hpull.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp [heu]) (by simp)
  exact hpull'.isoPullback.symm

/-- The projection to `X` of the finite-stage fibre product is the fold of the identity. -/
private theorem finiteProdPullbackIso_snd (k : CommRingCat.{u}) {J : Type u} [Finite J]
    (X : Scheme.{u}) (f : X ⟶ Spec k) :
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (J → (k : Type u))))) f =
      (finiteProdPullbackIso k (J := J) X f).hom ≫
        Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : J => X)) (fun _ => 𝟙 X) := by
  simp [finiteProdPullbackIso]

/-- The projection to the finite-product spectrum sends the `i`-th copy of `X` to the `i`-th
summand. -/
private theorem finiteProdPullbackIso_fst (k : CommRingCat.{u}) {J : Type u} [Finite J]
    (X : Scheme.{u}) (f : X ⟶ Spec k) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k (J → (k : Type u))))) f =
      (finiteProdPullbackIso k (J := J) X f).hom ≫
        (Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : J => X))
          (fun i => f ≫ Sigma.ι (fun _ : J => Spec k) i)) ≫
            (asIso (sigmaSpec (fun _ : J => k))).hom := by
  simp [finiteProdPullbackIso]

/-- A disjoint union of copies of a space indexed by a finite discrete space is the product
with that index space. -/
private noncomputable def sigmaProdHomeo (J : Type u) [Finite J] [TopologicalSpace J]
    [DiscreteTopology J] (Y : Type u) [TopologicalSpace Y] :
    Sigma (fun _ : J => Y) ≃ₜ J × Y := by
  let e : Sigma (fun _ : J => Y) ≃ J × Y := {
    toFun := fun x => (x.1, x.2)
    invFun := fun p => @Sigma.mk J (fun _ => Y) p.1 p.2
    left_inv := by intro x; cases x; rfl
    right_inv := by intro p; cases p; rfl }
  refine Homeomorph.mk e ?_ ?_
  · exact continuous_sigma (fun _ => continuous_const.prodMk continuous_id)
  · apply continuous_prod_of_discrete_left.mpr
    intro j
    change Continuous (fun y : Y => @Sigma.mk J (fun _ : J => Y) j y)
    exact @continuous_sigmaMk J (fun _ : J => Y) _ j

/-- The spectrum of a finite product of copies of a field is the finite discrete index
space. -/
private noncomputable def baseFiniteHomeo (k : Type u) [Field k] {J : Type u} [Finite J]
    [Small.{u} J] [TopologicalSpace J] [DiscreteTopology J] :
    J ≃ₜ PrimeSpectrum (J → k) := by
  let α : J → Scheme.{u} := fun _ => Spec (.of k)
  let e : J ≃ Σ i : J, Spec (.of k) := {
    toFun := fun i => ⟨i, default⟩
    invFun := fun x => x.1
    left_inv := fun _ => rfl
    right_inv := fun x => by
      rcases x with ⟨i, x⟩
      have hs : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
      exact congrArg (Sigma.mk i) (hs.elim _ _) }
  let h₁ := AlgebraicGeometry.sigmaMk α
  let eSpec : (∐ α) ≅ Spec (.of (J → k)) := asIso (sigmaSpec (fun _ : J => CommRingCat.of k))
  let h₂ : (∐ α : Scheme) ≃ₜ Spec (.of (J → k)) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso eSpec)
  exact (Homeomorph.mk e continuous_of_discreteTopology
    (continuous_sigma fun _ => continuous_const)).trans (h₁.trans h₂)

/-- The identification of the index space with the finite-product spectrum sends `j` to the
image of the `j`-th summand. -/
private theorem baseFiniteHomeo_apply (k : Type u) [Field k] {J : Type u} [Finite J]
    [Small.{u} J] [TopologicalSpace J] [DiscreteTopology J] (j : J) :
    baseFiniteHomeo k j =
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
        (asIso (sigmaSpec (fun _ : J => CommRingCat.of k)))))
        ((Sigma.ι (fun _ : J => Spec (.of k)) j) default) := by
  change (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
      (asIso (sigmaSpec (fun _ : J => CommRingCat.of k)))))
      (AlgebraicGeometry.sigmaMk (fun _ : J => Spec (.of k)) ⟨j, default⟩) = _
  exact congrArg _ (AlgebraicGeometry.sigmaMk_mk (fun _ : J => Spec (.of k)) j default)

/-- At a finite stage the canonical map from the fibre product to the product of underlying
spaces is a homeomorphism. -/
private theorem finiteProductPullback_isHomeomorph
    (k : Type u) [Field k] {J : Type u} [Finite J] [Small.{u} J]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    IsHomeomorph (fun x :
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k (J → k)))) f : Scheme.{u}) =>
      ((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k (J → k)))) f).base x,
       (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (J → k)))) f).base x)) := by
  let β : J → Scheme.{u} := fun _ => X
  let h₀ : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k (J → k)))) f : Scheme.{u}) ≃ₜ
      (∐ β : Scheme) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
      (finiteProdPullbackIso (CommRingCat.of k) (J := J) X f))
  let h₁ : (∐ β : Scheme) ≃ₜ Sigma (fun _ : J => (X : Type u)) :=
    (AlgebraicGeometry.sigmaMk β).symm
  let : TopologicalSpace J := ⊥
  let : DiscreteTopology J := ⟨rfl⟩
  let h₂ : Sigma (fun _ : J => (X : Type u)) ≃ₜ J × X := sigmaProdHomeo J (X : Type u)
  let h₃ : J × X ≃ₜ PrimeSpectrum (J → k) × X :=
    (baseFiniteHomeo k).prodCongr (Homeomorph.refl X)
  let h : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k (J → k)))) f : Scheme.{u}) ≃ₜ
      PrimeSpectrum (J → k) × X := h₀.trans (h₁.trans (h₂.trans h₃))
  have hEq : h.toFun = fun x =>
      ((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k (J → k)))) f).base x,
       (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (J → k)))) f).base x) := by
    funext x
    let z := h₁ (h₀ x)
    have hx : h₀ x = Sigma.ι β z.1 z.2 := by
      apply (AlgebraicGeometry.sigmaMk β).symm.injective
      change z = (AlgebraicGeometry.sigmaMk β).symm (Sigma.ι β z.1 z.2)
      rw [← AlgebraicGeometry.sigmaMk_mk β z.1 z.2]
      exact (AlgebraicGeometry.sigmaMk β).symm_apply_apply z |>.symm
    have hx' : ((finiteProdPullbackIso (CommRingCat.of k) X f).hom).base x =
        Sigma.ι β z.1 z.2 := hx
    apply Prod.ext
    · change baseFiniteHomeo k (h₁ (h₀ x)).1 =
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k (J → k)))) f).base x
      rw [baseFiniteHomeo_apply]
      have hSpec : f.base z.2 = (default : Spec (.of k)) := Subsingleton.elim _ _
      have hι :
          Sigma.ι β z.1 ≫
            Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : J => X))
            (fun i => f ≫ Sigma.ι (fun _ : J => Spec (.of k)) i) ≫
              (asIso (sigmaSpec (fun _ : J => CommRingCat.of k))).hom =
          (f ≫ Sigma.ι (fun _ : J => Spec (.of k)) z.1 ≫
            (asIso (sigmaSpec (fun _ : J => CommRingCat.of k))).hom) := by
        have hfac := Cofan.IsColimit.fac
          (hc := coproductIsCoproduct (fun _ : J => X))
          (f := fun i => f ≫ Sigma.ι (fun _ : J => Spec (.of k)) i) z.1
        have hfac' : Sigma.ι β z.1 ≫
            Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : J => X))
              (fun i => f ≫ Sigma.ι (fun _ : J => Spec (.of k)) i) =
            f ≫ Sigma.ι (fun _ : J => Spec (.of k)) z.1 := by
          simpa only [Cofan.inj, Cofan.mk, Discrete.natTrans_app,
            Discrete.functor_obj] using hfac
        exact congrArg
          (fun q => q ≫ (asIso (sigmaSpec (fun _ : J => CommRingCat.of k))).hom) hfac'
      have hp := congrArg (fun g : Scheme.Hom _ _ => g.base x)
        (finiteProdPullbackIso_fst (CommRingCat.of k) X f)
      simp only [Scheme.Hom.comp_base, CategoryTheory.comp_apply] at hp
      rw [hx'] at hp
      have hcomp := congrArg (fun g : Scheme.Hom _ _ => g.base z.2) hι
      simp only [Scheme.Hom.comp_base, CategoryTheory.comp_apply] at hcomp
      change (sigmaSpec (fun _ : J => CommRingCat.of k)).base
          (Sigma.ι (fun _ : J => Spec (.of k)) z.1 default) = _
      have hpoint := congrArg (fun p : Spec (.of k) =>
        (sigmaSpec (fun _ : J => CommRingCat.of k)).base
          (Sigma.ι (fun _ : J => Spec (.of k)) z.1 p)) hSpec
      calc
        _ = (sigmaSpec (fun _ : J => CommRingCat.of k)).base
              (Sigma.ι (fun _ : J => Spec (.of k)) z.1 (f.base z.2)) := hpoint.symm
        _ = (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k (J → k)))) f).base x :=
          hcomp.symm.trans hp.symm
    · change (h₁ (h₀ x)).2 =
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (J → k)))) f).base x
      have hz : h₁ (Sigma.ι β z.1 z.2) = z := by
        dsimp [h₁]
        rw [← AlgebraicGeometry.sigmaMk_mk β z.1 z.2]
        exact (AlgebraicGeometry.sigmaMk β).symm_apply_apply z
      have hp := congrArg (fun g : Scheme.Hom _ _ => g.base x)
        (finiteProdPullbackIso_snd (CommRingCat.of k) X f)
      rw [Scheme.Hom.comp_base] at hp
      rw [hx, hz]
      have hdesc :
          (Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : J => X))
            (fun _ : J => 𝟙 X)).base
              ((finiteProdPullbackIso (CommRingCat.of k) X f).hom.base x) = z.2 := by
        rw [hx']
        change ((Sigma.ι (fun _ : J => X) z.1 ≫
          Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : J => X))
            (fun _ : J => 𝟙 X)).base) z.2 = z.2
        have hfac : Sigma.ι β z.1 ≫
            Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : J => X))
              (fun _ : J => 𝟙 X) = 𝟙 X :=
          Cofan.IsColimit.fac (hc := coproductIsCoproduct (fun _ : J => X))
            (f := fun _ : J => 𝟙 X) z.1
        rw [hfac]
        rfl
      rw [hp]
      simpa only [ConcreteCategory.comp_apply] using hdesc.symm
  rw [← hEq]
  exact h.isHomeomorph

/-- Replacing the index type of a finite product of copies of `k` by its lift. -/
private noncomputable def finitePiLiftIso (k : Type u) [Field k] (n : ℕ) :
    CommAlgCat.of k (ULift (Fin n) → k) ≅ CommAlgCat.of k (Fin n → k) := by
  let a : (ULift (Fin n) → k) ≃ₐ[k] (Fin n → k) :=
    AlgEquiv.piCongrLeft k (fun _ : Fin n => k) (Equiv.ulift : ULift (Fin n) ≃ Fin n)
  exact Iso.mk (CommAlgCat.ofHom a.toAlgHom) (CommAlgCat.ofHom a.symm.toAlgHom)

/-- At a stage isomorphic to a finite product of copies of `k`, the underlying space of the
fibre product is the product of `X` with the underlying space of the stage. -/
private noncomputable def finiteStagePullbackHomeo
    (k : Type u) [Field k] {B : CommAlgCat.{u} k} {J : Type u} [Finite J]
    [Small.{u} J] (e : B ≅ CommAlgCat.of k (J → k))
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    ((Scheme.forgetToTop.obj
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k (↑B)))) f : Scheme.{u})) : Type u) ≃ₜ
      X × (((Over.forget (Spec (.of k))).obj
        ((AlgebraicGeometry.algSpec (.of k)).obj (Opposite.op B)) : Scheme.{u}) : Type u) := by
  let eSpec := (AlgebraicGeometry.algSpec (.of k)).mapIso e.op
  let ePull := (Over.pullback f).mapIso eSpec
  let hPull :
      (((Over.forget X).obj ((Over.pullback f).obj
        ((AlgebraicGeometry.algSpec (.of k)).obj
          (Opposite.op (CommAlgCat.of k (J → k))))) : Scheme.{u}) : Type u) ≃ₜ
        (((Over.forget X).obj ((Over.pullback f).obj
          ((AlgebraicGeometry.algSpec (.of k)).obj (Opposite.op B))) : Scheme.{u}) : Type u) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso ((Over.forget X).mapIso ePull))
  let hFinite :
      (pullback (Spec.map (CommRingCat.ofHom
        (algebraMap k (J → k)))) f : Scheme.{u}) ≃ₜ
        PrimeSpectrum (J → k) × X :=
    IsHomeomorph.homeomorph
      (fun x => ((pullback.fst (Spec.map (CommRingCat.ofHom
        (algebraMap k (J → k)))) f).base x,
        (pullback.snd (Spec.map (CommRingCat.ofHom
          (algebraMap k (J → k)))) f).base x))
      (finiteProductPullback_isHomeomorph k X f)
  let hSpec : PrimeSpectrum (J → k) ≃ₜ
      (((Over.forget (Spec (.of k))).obj
        ((AlgebraicGeometry.algSpec (.of k)).obj (Opposite.op B)) : Scheme.{u}) : Type u) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
      ((Over.forget (Spec (.of k))).mapIso eSpec))
  let basePts := (((Over.forget (Spec (.of k))).obj
    ((AlgebraicGeometry.algSpec (.of k)).obj (Opposite.op B)) : Scheme.{u}) : Type u)
  let hSpecX : PrimeSpectrum (J → k) × X ≃ₜ basePts × X :=
    hSpec.prodCongr (Homeomorph.refl X)
  let hSwap : basePts × X ≃ₜ X × basePts := Homeomorph.prodComm basePts X
  exact hPull.symm.trans (hFinite.trans (hSpecX.trans hSwap))

/-- The finite-stage identification is given by the two pullback projections. -/
private theorem finiteStagePullbackHomeo_apply
    (k : Type u) [Field k] {B : CommAlgCat.{u} k} {J : Type u} [Finite J]
    [Small.{u} J] (e : B ≅ CommAlgCat.of k (J → k))
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (x : ((Scheme.forgetToTop.obj
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k (↑B)))) f : Scheme.{u})) : Type u)) :
    finiteStagePullbackHomeo k e X f x =
      ((pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (↑B)))) f).base x,
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k (↑B)))) f).base x) := by
  let Bsch := (AlgebraicGeometry.algSpec (.of k)).obj (Opposite.op B)
  let Jsch := (AlgebraicGeometry.algSpec (.of k)).obj
    (Opposite.op (CommAlgCat.of k (J → k)))
  let eSpec := (AlgebraicGeometry.algSpec (.of k)).mapIso e.op
  let ePull := (Over.pullback f).mapIso eSpec
  let ePullSch := (Over.forget X).mapIso ePull
  have hfst : ePullSch.hom ≫ pullback.fst Bsch.hom f =
      pullback.fst Jsch.hom f ≫ eSpec.hom.left := by
    dsimp [Over.pullback]
    change pullback.lift (pullback.fst Jsch.hom f ≫ eSpec.hom.left)
      (pullback.snd Jsch.hom f) _ ≫ pullback.fst Bsch.hom f =
        pullback.fst Jsch.hom f ≫ eSpec.hom.left
    exact pullback.lift_fst _ _ _
  have hsnd : ePullSch.hom ≫ pullback.snd Bsch.hom f =
      pullback.snd Jsch.hom f := by
    dsimp [Over.pullback]
    change pullback.lift (pullback.fst Jsch.hom f ≫ eSpec.hom.left)
      (pullback.snd Jsch.hom f) _ ≫ pullback.snd Bsch.hom f =
        pullback.snd Jsch.hom f
    exact pullback.lift_snd _ _ _
  have hfstInv : ePullSch.inv ≫ pullback.fst Jsch.hom f ≫ eSpec.hom.left =
      pullback.fst Bsch.hom f := by
    rw [← hfst, Iso.inv_hom_id_assoc]
  have hsndInv : ePullSch.inv ≫ pullback.snd Jsch.hom f =
      pullback.snd Bsch.hom f := by
    rw [← hsnd, Iso.inv_hom_id_assoc]
  let hPull := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso ePullSch)
  let hFinite : (pullback (Spec.map (CommRingCat.ofHom
      (algebraMap k (J → k)))) f : Scheme.{u}) ≃ₜ
      PrimeSpectrum (J → k) × X :=
    IsHomeomorph.homeomorph
      (fun y => ((pullback.fst (Spec.map (CommRingCat.ofHom
        (algebraMap k (J → k)))) f).base y,
        (pullback.snd (Spec.map (CommRingCat.ofHom
          (algebraMap k (J → k)))) f).base y))
      (finiteProductPullback_isHomeomorph k X f)
  let basePts := (((Over.forget (Spec (.of k))).obj
    ((AlgebraicGeometry.algSpec (.of k)).obj (Opposite.op B)) : Scheme.{u}) : Type u)
  let hSpec : PrimeSpectrum (J → k) ≃ₜ basePts := TopCat.homeoOfIso
    (Scheme.forgetToTop.mapIso ((Over.forget (Spec (.of k))).mapIso eSpec))
  let hSpecX : PrimeSpectrum (J → k) × X ≃ₜ basePts × X :=
    hSpec.prodCongr (Homeomorph.refl X)
  let hSwap := Homeomorph.prodComm basePts X
  change hSwap (hSpecX (hFinite (hPull.symm x))) = _
  change Equiv.prodComm basePts X
    (hSpec ((pullback.fst (Spec.map (CommRingCat.ofHom
      (algebraMap k (J → k)))) f).base (ePullSch.inv x)),
      (pullback.snd (Spec.map (CommRingCat.ofHom
        (algebraMap k (J → k)))) f).base (ePullSch.inv x)) = _
  rw [Equiv.prodComm_apply]
  simp only [Prod.swap_prod_mk]
  apply Prod.ext
  · change (TopCat.Hom.hom (pullback.snd (Spec.map (CommRingCat.ofHom
      (algebraMap k (J → k)))) f).base)
      ((TopCat.Hom.hom ePullSch.inv.base) x) =
        (TopCat.Hom.hom (pullback.snd Bsch.hom f).base) x
    rw [← hsndInv]
    rfl
  · change (TopCat.Hom.hom eSpec.hom.left.base)
      ((TopCat.Hom.hom (pullback.fst Jsch.hom f).base)
        ((TopCat.Hom.hom ePullSch.inv.base) x)) =
        (TopCat.Hom.hom (pullback.fst Bsch.hom f).base) x
    rw [← hfstInv]
    rfl

/-- The first projection of the categorical product reads off the first coordinate of a point
of the concrete product. -/
private lemma prodIsoProd_symm_fst (Y Z : TopCat.{u}) (p : Y) (q : Z) :
    (ConcreteCategory.hom (prod.fst : Y ⨯ Z ⟶ Y))
      ((TopCat.homeoOfIso (TopCat.prodIsoProd Y Z)).symm (p, q)) = p := by
  rw [TopCat.homeoOfIso_symm_apply, TopCat.prodIsoProd_inv_fst_apply]

/-- The second projection of the categorical product reads off the second coordinate of a
point of the concrete product. -/
private lemma prodIsoProd_symm_snd (Y Z : TopCat.{u}) (p : Y) (q : Z) :
    (ConcreteCategory.hom (prod.snd : Y ⨯ Z ⟶ Z))
      ((TopCat.homeoOfIso (TopCat.prodIsoProd Y Z)).symm (p, q)) = q := by
  rw [TopCat.homeoOfIso_symm_apply, TopCat.prodIsoProd_inv_snd_apply]

/-- A product of morphisms acts coordinatewise on points of the concrete product. -/
private lemma prodIsoProd_symm_prodMap {Y Z Y' Z' : TopCat.{u}} (u : Y ⟶ Y') (v : Z ⟶ Z')
    (p : Y) (q : Z) :
    (ConcreteCategory.hom (prod.map u v))
        ((TopCat.homeoOfIso (TopCat.prodIsoProd Y Z)).symm (p, q)) =
      (TopCat.homeoOfIso (TopCat.prodIsoProd Y' Z')).symm (u p, v q) := by
  apply (TopCat.homeoOfIso (TopCat.prodIsoProd Y' Z')).injective
  have h1 : (ConcreteCategory.hom (prod.fst : Y' ⨯ Z' ⟶ Y'))
      ((ConcreteCategory.hom (prod.map u v))
        ((TopCat.homeoOfIso (TopCat.prodIsoProd Y Z)).symm (p, q))) =
      (ConcreteCategory.hom u) p := by
    rw [← ConcreteCategory.comp_apply, prod.map_fst, ConcreteCategory.comp_apply,
      prodIsoProd_symm_fst]
  have h2 : (ConcreteCategory.hom (prod.snd : Y' ⨯ Z' ⟶ Z'))
      ((ConcreteCategory.hom (prod.map u v))
        ((TopCat.homeoOfIso (TopCat.prodIsoProd Y Z)).symm (p, q))) =
      (ConcreteCategory.hom v) q := by
    rw [← ConcreteCategory.comp_apply, prod.map_snd, ConcreteCategory.comp_apply,
      prodIsoProd_symm_snd]
  rw [Homeomorph.apply_symm_apply, TopCat.homeoOfIso_apply, TopCat.prodIsoProd_hom_apply,
    h1, h2]

/-- Let `k` be a field and let `A` be a filtered colimit of
`k`-algebras that are finite products of copies of `k`.  For any scheme `X` over `k`, the
canonical map from the underlying space of `Spec A ×_k X` to `|Spec A| × |X|` is a
homeomorphism. -/
@[stacks 0B7T]
theorem isHomeomorph_pullback_to_product
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (hA : IsFilteredColimitOfFiniteProducts k A)
    (X : Scheme.{u}) (f : X ⟶ Spec (of k)) :
    IsHomeomorph (fun x :
      (pullback (Spec.map (ofHom (algebraMap k A))) f : Scheme.{u}) ↦
        ((pullback.fst (Spec.map (ofHom (algebraMap k A))) f).base x,
          (pullback.snd (Spec.map (ofHom (algebraMap k A))) f).base x)) := by
  classical
  rcases hA with ⟨I, hSmall, hFiltered, F, c, hc, hcPt, hStages⟩
  let : SmallCategory I := hSmall
  let : IsFiltered I := hFiltered
  let hc : IsColimit c := Classical.choice hc
  let e : c.pt ≅ CommAlgCat.of k A := Classical.choice hcPt
  let D0 : Iᵒᵖ ⥤ Over (Spec (.of k)) :=
    F.op ⋙ AlgebraicGeometry.algSpec (.of k)
  let C0 : Cone D0 := (AlgebraicGeometry.algSpec (.of k)).mapCone c.op
  let eSpec := (AlgebraicGeometry.algSpec (.of k)).mapIso e.op
  let C0A : Cone D0 := C0.extend eSpec.hom
  let D1 : Iᵒᵖ ⥤ Over X := D0 ⋙ Over.pullback f
  let C1 : Cone D1 := (Over.pullback f).mapCone C0
  let ePull := (Over.pullback f).mapIso eSpec
  let C1A : Cone D1 := C1.extend ePull.hom
  let DpullSch : Iᵒᵖ ⥤ Scheme := D1 ⋙ Over.forget X
  let CpullSch : Cone DpullSch := (Over.forget X).mapCone C1A
  let DbaseSch : Iᵒᵖ ⥤ Scheme := D0 ⋙ Over.forget (Spec (.of k))
  let CbaseSch : Cone DbaseSch := (Over.forget (Spec (.of k))).mapCone C0A
  let DpullTop : Iᵒᵖ ⥤ TopCat := DpullSch ⋙ Scheme.forgetToTop
  let CpullTop : Cone DpullTop := Scheme.forgetToTop.mapCone CpullSch
  let DbaseTop : Iᵒᵖ ⥤ TopCat := DbaseSch ⋙ Scheme.forgetToTop
  let CbaseTop : Cone DbaseTop := Scheme.forgetToTop.mapCone CbaseSch
  let : IsConnected (Iᵒᵖ) := IsCofiltered.isConnected (Iᵒᵖ)
  let : PreservesLimitsOfSize.{u, u} (AlgebraicGeometry.algSpec (.of k)) :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec
  let hC0 : IsLimit C0 :=
    (PreservesLimit.preserves (K := F.op)
      (F := AlgebraicGeometry.algSpec (.of k)) hc.op).some
  let hC0A : IsLimit C0A := by
    let hIso : C0A ≅ C0 := Cone.ext eSpec (by intro i; simp [C0A, C0])
    exact hC0.ofIsoLimit hIso.symm
  let hC1 : IsLimit C1 :=
    (PreservesLimit.preserves (K := D0) (F := Over.pullback f) hC0).some
  let hC1A : IsLimit C1A := by
    let hIso : C1A ≅ C1 := Cone.ext ePull (by intro i; simp [C1A, C1])
    exact hC1.ofIsoLimit hIso.symm
  let hCpullSch : IsLimit CpullSch :=
    (PreservesLimit.preserves (K := D1) (F := Over.forget X) hC1A).some
  let : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (DbaseSch.map g) := by
    intro i j g
    change IsAffineHom (Spec.map ((commAlgCatEquivUnder (.of k)).functor.map
      (F.map g.unop)).right)
    let : IsAffine (Spec (CommRingCat.of (F.obj j.unop))) := isAffine_Spec _
    let : IsAffine (Spec (CommRingCat.of (F.obj i.unop))) := isAffine_Spec _
    exact isAffineHom_of_isAffine _
  let : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (DpullSch.map g) := fun {i j} g =>
    MorphismProperty.overPullbackMap f (D0.map g) (inferInstanceAs (IsAffineHom (DbaseSch.map g)))
  let hCpullTop : IsLimit CpullTop :=
    ((preservesLimit_forgetToTop_of_isCofiltered_of_isAffineHom DpullSch).preserves
      hCpullSch).some
  let hCbaseSch : IsLimit CbaseSch :=
    (PreservesLimit.preserves (K := D0) (F := Over.forget (Spec (.of k))) hC0A).some
  let hCbaseTop : IsLimit CbaseTop :=
    ((preservesLimit_forgetToTop_of_isCofiltered_of_isAffineHom DbaseSch).preserves
      hCbaseSch).some
  let Xtop := Scheme.forgetToTop.obj X
  let prodF := prod.functor.obj Xtop
  let Dprod : Iᵒᵖ ⥤ TopCat := DbaseTop ⋙ prodF
  let Cprod : Cone Dprod := prodF.mapCone CbaseTop
  let : PreservesLimitsOfShape (Iᵒᵖ) prodF := prod_preservesConnectedLimits Xtop
  let hCprod : IsLimit Cprod :=
    (PreservesLimit.preserves (K := DbaseTop) (F := prodF) hCbaseTop).some
  let n : ∀ i : I, ℕ := fun i => Classical.choose (hStages i)
  let eFin : ∀ i : I, F.obj i ≅ CommAlgCat.of k (Fin (n i) → k) :=
    fun i => Classical.choice (Classical.choose_spec (hStages i))
  let eLift : ∀ i : I, F.obj i ≅ CommAlgCat.of k (ULift (Fin (n i)) → k) :=
    fun i => (eFin i).trans (finitePiLiftIso k (n i)).symm
  let α : DpullTop ≅ Dprod := NatIso.ofComponents
    (fun i => by
      dsimp [DpullTop, DpullSch, D1, D0, Dprod, prodF,
        DbaseTop, DbaseSch, Xtop]
      exact TopCat.isoOfHomeo
        ((finiteStagePullbackHomeo k (eLift i.unop) X f).trans
          (TopCat.homeoOfIso (TopCat.prodIsoProd (Scheme.forgetToTop.obj X)
            (Scheme.forgetToTop.obj ((Over.forget (Spec (.of k))).obj
              ((AlgebraicGeometry.algSpec (.of k)).obj
                (Opposite.op (F.obj i.unop)))))).symm)))
    (by
      intro i j g
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      have hi := finiteStagePullbackHomeo_apply k (eLift i.unop) X f x
      have hj := finiteStagePullbackHomeo_apply k (eLift j.unop) X f
        ((DpullSch.map g).base x)
      have hs : DpullSch.map g ≫
          pullback.snd (Spec.map (ofHom (algebraMap k (F.obj j.unop)))) f =
          pullback.snd (Spec.map (ofHom (algebraMap k (F.obj i.unop)))) f := by
        simp only [DpullSch, D1, D0, Functor.comp_map, Over.forget_map, Over.pullback_map_left]
        exact pullback.lift_snd _ _ _
      have hf : DpullSch.map g ≫
          pullback.fst (Spec.map (ofHom (algebraMap k (F.obj j.unop)))) f =
          pullback.fst (Spec.map (ofHom (algebraMap k (F.obj i.unop)))) f ≫
            DbaseSch.map g := by
        simp only [DpullSch, D1, D0, DbaseSch, Functor.comp_map, Over.forget_map,
          Over.pullback_map_left]
        exact pullback.lift_fst _ _ _
      change (TopCat.homeoOfIso (TopCat.prodIsoProd Xtop (DbaseTop.obj j))).symm
          (finiteStagePullbackHomeo k (eLift j.unop) X f ((DpullSch.map g).base x)) =
        (ConcreteCategory.hom (prod.map (𝟙 Xtop) (DbaseTop.map g)))
          ((TopCat.homeoOfIso (TopCat.prodIsoProd Xtop (DbaseTop.obj i))).symm
            (finiteStagePullbackHomeo k (eLift i.unop) X f x))
      rw [hj, hi]
      refine Eq.trans ?_ (prodIsoProd_symm_prodMap (𝟙 Xtop) (DbaseTop.map g) _ _).symm
      refine congrArg
        (fun z => (TopCat.homeoOfIso (TopCat.prodIsoProd Xtop (DbaseTop.obj j))).symm z) ?_
      refine Prod.ext ?_ ?_
      · exact congrArg (fun h : TopCat.Hom _ _ => h.hom x)
          (congrArg (fun h : Scheme.Hom _ _ => h.base) hs)
      · exact congrArg (fun h : TopCat.Hom _ _ => h.hom x)
          (congrArg (fun h : Scheme.Hom _ _ => h.base) hf))
  let hLim := hCpullTop.conePointsIsoOfNatIso hCprod α
  have hαfst (i : Iᵒᵖ) :
      α.hom.app i ≫ (prod.fst : Dprod.obj i ⟶ Xtop) =
        (pullback.snd (Spec.map (ofHom (algebraMap k (F.obj i.unop)))) f).base := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change (ConcreteCategory.hom (prod.fst : Dprod.obj i ⟶ Xtop))
      (((finiteStagePullbackHomeo k (eLift i.unop) X f).trans
        (TopCat.homeoOfIso (TopCat.prodIsoProd Xtop (DbaseTop.obj i))).symm) x) = _
    dsimp [DbaseTop, DbaseSch, D0]
    change (ConcreteCategory.hom (prod.fst : Xtop ⨯ DbaseTop.obj i ⟶ Xtop))
      ((TopCat.homeoOfIso (TopCat.prodIsoProd Xtop (DbaseTop.obj i))).symm
        ((finiteStagePullbackHomeo k (eLift i.unop) X f) x)) = _
    rw [finiteStagePullbackHomeo_apply k (eLift i.unop) X f x]
    exact prodIsoProd_symm_fst Xtop (DbaseTop.obj i) _ _
  have hαsnd (i : Iᵒᵖ) :
      α.hom.app i ≫ (prod.snd : Dprod.obj i ⟶ DbaseTop.obj i) =
        (pullback.fst (Spec.map (ofHom (algebraMap k (F.obj i.unop)))) f).base := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change (ConcreteCategory.hom (prod.snd : Dprod.obj i ⟶ DbaseTop.obj i))
      (((finiteStagePullbackHomeo k (eLift i.unop) X f).trans
        (TopCat.homeoOfIso (TopCat.prodIsoProd Xtop (DbaseTop.obj i))).symm) x) = _
    dsimp [DbaseTop, DbaseSch, D0]
    change (ConcreteCategory.hom (prod.snd : Xtop ⨯ DbaseTop.obj i ⟶ DbaseTop.obj i))
      ((TopCat.homeoOfIso (TopCat.prodIsoProd Xtop (DbaseTop.obj i))).symm
        ((finiteStagePullbackHomeo k (eLift i.unop) X f) x)) = _
    rw [finiteStagePullbackHomeo_apply k (eLift i.unop) X f x]
    exact prodIsoProd_symm_snd Xtop (DbaseTop.obj i) _ _
  let pX : CpullTop.pt ⟶ Xtop :=
    (pullback.snd (Spec.map (ofHom (algebraMap k A))) f).base
  let pB : CpullTop.pt ⟶ CbaseTop.pt :=
    (pullback.fst (Spec.map (ofHom (algebraMap k A))) f).base
  let canon : CpullTop.pt ⟶ Cprod.pt := prod.lift pX pB
  have hConeMap (i : Iᵒᵖ) : C1A.π.app i = (Over.pullback f).map (C0A.π.app i) :=
    ((Over.pullback f).map_comp eSpec.hom (C0.π.app i)).symm
  have hPullSnd (i : Iᵒᵖ) :
      CpullTop.π.app i ≫
        (pullback.snd (Spec.map (ofHom (algebraMap k (F.obj i.unop)))) f).base = pX := by
    have hsquare : CpullSch.π.app i ≫
        pullback.snd (Spec.map (ofHom (algebraMap k (F.obj i.unop)))) f =
          pullback.snd (Spec.map (ofHom (algebraMap k A))) f :=
      Over.w (C1A.π.app i)
    exact congrArg (fun m : Scheme.Hom _ _ => m.base) hsquare
  have hPullFst (i : Iᵒᵖ) :
      CpullTop.π.app i ≫
        (pullback.fst (Spec.map (ofHom (algebraMap k (F.obj i.unop)))) f).base =
          pB ≫ CbaseTop.π.app i := by
    have hsquare : CpullSch.π.app i ≫
        pullback.fst (Spec.map (ofHom (algebraMap k (F.obj i.unop)))) f =
          pullback.fst (Spec.map (ofHom (algebraMap k A))) f ≫ CbaseSch.π.app i := by
      have h0 : CpullSch.π.app i = ((Over.pullback f).map (C0A.π.app i)).left :=
        congrArg Over.Hom.left (hConeMap i)
      rw [h0]
      exact pullback.lift_fst _ _ _
    exact congrArg (fun m : Scheme.Hom _ _ => m.base) hsquare
  have hcanon : hLim.hom = canon := by
    apply hCprod.hom_ext
    intro i
    apply prod.hom_ext
    · have hs1 : hLim.hom ≫ Cprod.π.app i ≫ (prod.fst : Dprod.obj i ⟶ Xtop) =
          CpullTop.π.app i ≫ α.hom.app i ≫ (prod.fst : Dprod.obj i ⟶ Xtop) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (prod.fst : Dprod.obj i ⟶ Xtop))
            (hCpullTop.conePointsIsoOfNatIso_hom_comp hCprod α i)).trans
              (Category.assoc _ _ _))
      have hs2 : CpullTop.π.app i ≫ α.hom.app i ≫
          (prod.fst : Dprod.obj i ⟶ Xtop) = pX :=
        (congrArg (fun z => CpullTop.π.app i ≫ z) (hαfst i)).trans (hPullSnd i)
      have h1 : Cprod.π.app i ≫ (prod.fst : Dprod.obj i ⟶ Xtop) =
          (prod.fst : Xtop ⨯ CbaseTop.pt ⟶ Xtop) := by
        dsimp only [Cprod, Dprod, prodF, Functor.mapCone, Cone.functoriality,
          prod.functor, Functor.comp_obj]
        simp
      have hs3 : pX = canon ≫ Cprod.π.app i ≫ (prod.fst : Dprod.obj i ⟶ Xtop) :=
        (prod.lift_fst pX pB).symm.trans (congrArg (fun z => canon ≫ z) h1).symm
      exact hs1.trans (hs2.trans hs3)
    · have ht1 : hLim.hom ≫ Cprod.π.app i ≫ (prod.snd : Dprod.obj i ⟶ DbaseTop.obj i) =
          CpullTop.π.app i ≫ α.hom.app i ≫
            (prod.snd : Dprod.obj i ⟶ DbaseTop.obj i) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (prod.snd : Dprod.obj i ⟶ DbaseTop.obj i))
            (hCpullTop.conePointsIsoOfNatIso_hom_comp hCprod α i)).trans
              (Category.assoc _ _ _))
      have ht2 : CpullTop.π.app i ≫ α.hom.app i ≫
          (prod.snd : Dprod.obj i ⟶ DbaseTop.obj i) = pB ≫ CbaseTop.π.app i :=
        (congrArg (fun z => CpullTop.π.app i ≫ z) (hαsnd i)).trans (hPullFst i)
      have h2 : Cprod.π.app i ≫ (prod.snd : Dprod.obj i ⟶ DbaseTop.obj i) =
          (prod.snd : Xtop ⨯ CbaseTop.pt ⟶ CbaseTop.pt) ≫ CbaseTop.π.app i := by
        dsimp only [Cprod, Dprod, prodF, Functor.mapCone, Cone.functoriality,
          prod.functor, Functor.comp_obj]
        simp
      have ht3 : pB ≫ CbaseTop.π.app i =
          canon ≫ Cprod.π.app i ≫ (prod.snd : Dprod.obj i ⟶ DbaseTop.obj i) :=
        ((congrArg (fun z => z ≫ CbaseTop.π.app i) (prod.lift_snd pX pB)).symm.trans
          (Category.assoc _ _ _)).trans (congrArg (fun z => canon ≫ z) h2).symm
      exact ht1.trans (ht2.trans ht3)
  let eProd := TopCat.prodIsoProd Xtop CbaseTop.pt
  let eSwap : TopCat.of (↑Xtop × ↑CbaseTop.pt) ≅
      TopCat.of (↑CbaseTop.pt × ↑Xtop) :=
    TopCat.isoOfHomeo (Homeomorph.prodComm (↑Xtop) (↑CbaseTop.pt))
  let eFinal := hLim.trans (eProd.trans eSwap)
  have hfun (x : CpullTop.pt) :
      (TopCat.homeoOfIso eFinal) x = (pB x, pX x) := by
    change (ConcreteCategory.hom eFinal.hom) x = _
    simp only [eFinal, Iso.trans, hcanon, eProd, eSwap, TopCat.isoOfHomeo_hom,
      Homeomorph.prodComm]
    dsimp [canon, Cprod, prodF, prod.functor]
    rw [TopCat.prodIsoProd_hom_apply]
    apply Prod.ext <;> simp [← ConcreteCategory.comp_apply]
  have hfun' : (TopCat.homeoOfIso eFinal).toFun =
      fun x : CpullTop.pt => (pB x, pX x) := funext hfun
  change IsHomeomorph (fun x : CpullTop.pt => (pB x, pX x))
  rw [← hfun']
  exact (TopCat.homeoOfIso eFinal).isHomeomorph

end AlgebraicGeometry

end
